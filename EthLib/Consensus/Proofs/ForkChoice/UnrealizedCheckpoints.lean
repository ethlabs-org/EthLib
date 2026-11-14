module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
import EthLib.Base.Proofs.FilterM
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# Proofs: unrealized checkpoints are those of the next epoch

The fork choice runs justification and finalization on the state after a block.

The checkpoints it gets are the unrealized checkpoints of the block.

If no other block comes before the next epoch, the slot advance runs the same step at its end.

It weighs the same participation, the same balances and the same block roots.

So its checkpoints are the unrealized ones, also when the block slashed validators.

The block roots of the history must cover two epochs, as both presets do.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state tip after : BeaconState preset fork} {next : Slot}

section Helpers

open Serialization.Ssz Cryptography.Bls

/-! ## Justification reads the same values after the slots of an epoch -/

/-- A state that differs from another only in its slot, roots, header and payload availability. -/
private def Moved (state moved : BeaconState preset fork) : Prop :=
  ∃ (slot : Slot) (stateRoots blockRoots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (header : BeaconBlockHeader)
    (availability : Since .glamsterdam fork (ExecutionPayloadAvailability preset)),
    moved = { state with
      slot := slot
      stateRoots := stateRoots
      blockRoots := blockRoots
      latestBlockHeader := header
      executionPayloadAvailability := availability }

/-- The same epoch gives the same previous epoch. -/
private theorem previous_eq {moved : BeaconState preset fork}
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) :
    getPreviousEpoch moved = getPreviousEpoch state := by
  unfold getPreviousEpoch
  rw [epoch]

/-- From Altair, the participating validators are the same in both states. -/
private theorem participating_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) {altair : .altair ≤ fork}
    {flag : UInt64} {target : Epoch} :
    getUnslashedParticipatingIndices moved altair flag target =
      getUnslashedParticipatingIndices state altair flag target := by
  have previous := previous_eq epoch
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  unfold getUnslashedParticipatingIndices
  rw [epoch, previous]
  rfl

/-- The total active balance is the same in both states. -/
private theorem totalActive_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) :
    getTotalActiveBalance moved = getTotalActiveBalance state := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  unfold getTotalActiveBalance
  rw [epoch]
  rfl

/-- Both states give the same root for the first block of the previous or the current epoch.

This holds whenever both of them read that root. -/
private def SameRoots (state moved : BeaconState preset fork) : Prop :=
  ∀ {target : Epoch} {root root' : Root},
    (target = getPreviousEpoch state ∨ target = getCurrentEpoch state) →
    getBlockRoot state target = .ok root → getBlockRoot moved target = .ok root' → root' = root

/-- Two states with the same three checkpoints and the same justification bits. -/
private def SameOutcome (tip tip' : BeaconState preset fork) : Prop :=
  tip'.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint ∧
    tip'.previousJustifiedCheckpoint = tip.previousJustifiedCheckpoint ∧
    tip'.finalizedCheckpoint = tip.finalizedCheckpoint ∧
    tip'.justificationBits = tip.justificationBits

/-- A justified epoch gets the same checkpoint in both states. -/
private theorem justify_eq {moved : BeaconState preset fork} (roots : SameRoots state moved)
    {justified : Bool} {target : Epoch} {checkpoint first second : Checkpoint}
    (recent : target = getPreviousEpoch state ∨ target = getCurrentEpoch state)
    (one : justifyCheckpoint state justified target checkpoint = .ok first)
    (two : justifyCheckpoint moved justified target checkpoint = .ok second) : second = first := by
  unfold justifyCheckpoint at one two
  cases justified
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at one two
    rw [← one, ← two]
  · simp only [↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at one two
    obtain ⟨root, rootOk, rfl⟩ := one
    obtain ⟨root', rootOk', rfl⟩ := two
    rw [roots recent rootOk rootOk']

/-- Weighing the same balances gives the same checkpoints and bits in both states. -/
private theorem weigh_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    {total previousBalance currentBalance : Gwei}
    (one : weighJustificationAndFinalization state total previousBalance currentBalance = .ok tip)
    (two : weighJustificationAndFinalization moved total previousBalance currentBalance =
      .ok after) : SameOutcome tip after := by
  have previous := previous_eq epoch
  unfold weighJustificationAndFinalization at one two
  rw [epoch, previous] at two
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at one two
  obtain ⟨w1, hw1, th, hth, j1, hj1, w2, hw2, j2, hj2, f1, hf1, f2, hf2, f3, hf3, f4, hf4,
    rfl⟩ := one
  obtain ⟨w1', hw1', th', hth', j1', hj1', w2', hw2', j2', hj2', f1', hf1', f2', hf2', f3', hf3',
    f4', hf4', rfl⟩ := two
  cases hw1.symm.trans hw1'
  cases hth.symm.trans hth'
  cases hw2.symm.trans hw2'
  cases justify_eq roots (.inl rfl) hj1 hj1'
  cases justify_eq roots (.inr rfl) hj2 hj2'
  cases hf1.symm.trans hf1'
  cases hf2.symm.trans hf2'
  cases hf3.symm.trans hf3'
  cases hf4.symm.trans hf4'
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Before Altair, the balance of the signers is the same in both states. -/
private theorem attestingBalance_eq {moved : BeaconState preset fork} (same : Moved state moved)
    {attestations : Array (PendingAttestation preset)} :
    getAttestingBalance moved attestations = getAttestingBalance state attestations := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  rfl

/-- Before Altair, the votes for the first block of an epoch are the same in both states. -/
private theorem matchingTarget_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    {before : fork < .altair} {target : Epoch} {first second : Array (PendingAttestation preset)}
    (recent : target = getPreviousEpoch state ∨ target = getCurrentEpoch state)
    (one : getMatchingTargetAttestations state before target = .ok first)
    (two : getMatchingTargetAttestations moved before target = .ok second) : second = first := by
  have previous := previous_eq epoch
  have source : getMatchingSourceAttestations moved before target =
      getMatchingSourceAttestations state before target := by
    obtain ⟨_, _, _, _, _, rfl⟩ := same
    unfold getMatchingSourceAttestations
    rw [epoch, previous]
  unfold getMatchingTargetAttestations at one two
  rw [source] at two
  simp only [bind_ok_iff] at one two
  obtain ⟨found, foundOk, one⟩ := one
  obtain ⟨found', foundOk', two⟩ := two
  cases foundOk.symm.trans foundOk'
  by_cases empty : found.isEmpty
  · simp only [empty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at one two
    rw [← one, ← two]
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at one two
    obtain ⟨root, rootOk, rfl⟩ := one
    obtain ⟨root', rootOk', rfl⟩ := two
    rw [roots recent rootOk rootOk']

/-- Justification on a moved state with the same epoch and roots ends the same way. -/
private theorem justification_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    (one : processJustificationAndFinalization state = .ok tip)
    (two : processJustificationAndFinalization moved = .ok after) : SameOutcome tip after := by
  have previous := previous_eq epoch
  unfold processJustificationAndFinalization at one two
  split at one
  · rename_i altair
    simp only [altair, ↓reduceDIte] at two
    unfold processJustificationAndFinalizationAltair at one two
    rw [epoch] at two
    split at one
    · rename_i early
      simp only [early, ↓reduceIte] at two
      simp only [pure, Except.pure, Except.ok.injEq] at one two
      subst one two
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact ⟨rfl, rfl, rfl, rfl⟩
    rename_i late
    simp only [late, ↓reduceIte, previous, participating_eq same epoch,
      totalActive_eq same epoch] at two
    simp only [bind_ok_iff, liftAccessor_ok] at one two
    obtain ⟨p, hp, c, hc, t, ht, pb, hpb, cb, hcb, one⟩ := one
    obtain ⟨p', hp', c', hc', t', ht', pb', hpb', cb', hcb', two⟩ := two
    cases hp.symm.trans hp'
    cases hc.symm.trans hc'
    cases ht.symm.trans ht'
    have hpb'' : getTotalBalance state p = .ok pb' := by
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact hpb'
    have hcb'' : getTotalBalance state c = .ok cb' := by
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact hcb'
    cases hpb.symm.trans hpb''
    cases hcb.symm.trans hcb''
    exact weigh_eq same epoch roots one two
  · rename_i altair
    simp only [altair, ↓reduceDIte, epoch] at two
    split at one
    · rename_i early
      simp only [early, ↓reduceIte] at two
      simp only [pure, Except.pure, Except.ok.injEq] at one two
      subst one two
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact ⟨rfl, rfl, rfl, rfl⟩
    rename_i late
    simp only [late, ↓reduceIte, previous, totalActive_eq same epoch,
      attestingBalance_eq same] at two
    simp only [bind_ok_iff, liftAccessor_ok] at one two
    obtain ⟨p, hp, c, hc, t, ht, pb, hpb, cb, hcb, one⟩ := one
    obtain ⟨p', hp', c', hc', t', ht', pb', hpb', cb', hcb', two⟩ := two
    cases matchingTarget_eq same epoch roots (.inl rfl) hp hp'
    cases matchingTarget_eq same epoch roots (.inr rfl) hc hc'
    cases ht.symm.trans ht'
    cases hpb.symm.trans hpb'
    cases hcb.symm.trans hcb'
    exact weigh_eq same epoch roots one two

/-! ## The slots up to the end of the epoch -/

/-- The moved state reads the same block roots at the slots before the original one.

Only slots from the start of the previous epoch count. -/
private def KeepsRoots (state moved : BeaconState preset fork) : Prop :=
  ∀ slot : Slot, slot.toNat < state.slot.toNat →
    ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat →
    readCircular moved.blockRoots.elements slot = readCircular state.blockRoots.elements slot

/-- Roots kept from the start of the previous epoch are the same roots for justification. -/
private theorem sameRoots_of (keeps : KeepsRoots state moved) : SameRoots state moved := by
  intro target root root' recent one two
  unfold getBlockRoot at one two
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at one two
  obtain ⟨slot, start, one⟩ := one
  obtain ⟨slot', start', two⟩ := two
  cases start.symm.trans start'
  obtain ⟨lt, read⟩ := getBlockRootAtSlot_read one
  obtain ⟨-, read'⟩ := getBlockRootAtSlot_read two
  have low : ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat := by
    rw [(mulChecked_ok_iff.mp start).2]
    apply Nat.mul_le_mul_right
    rcases recent with rfl | rfl
    · rw [getPreviousEpoch_toNat]
    · exact Nat.sub_le _ _
  rw [keeps slot (UInt64.lt_iff_toNat_lt.mp lt) low, read] at read'
  exact (Except.ok.inj read').symm

/-- The caching of a slot keeps a moved state moved. -/
private theorem Moved.processSlot {cached : BeaconState preset fork} (same : Moved state moved)
    (computed : processSlot moved = .ok cached) : Moved state cached := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  exact ⟨_, _, _, _, _, rfl⟩

/-- A new slot keeps a moved state moved. -/
private theorem Moved.slot (same : Moved state moved) (slot : Slot) :
    Moved state { moved with slot } := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  exact ⟨_, _, _, _, _, rfl⟩

/-- The first slot of the epoch of a state is at most its slot. -/
private theorem epoch_bounds (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat := by
  rw [getCurrentEpoch_toNat]
  exact Nat.div_mul_le_self _ _

/-- The caching of a slot keeps the roots that the original state reads.

The slot must be in the epoch of the original state, from its slot on. -/
private theorem KeepsRoots.processSlot {cached : BeaconState preset fork}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (keeps : KeepsRoots state moved) (computed : processSlot moved = .ok cached)
    (low : state.slot.toNat ≤ moved.slot.toNat)
    (high : moved.slot.toNat < ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :
    KeepsRoots state cached := by
  intro slot lt lo
  obtain ⟨root, -, written⟩ := processSlot_blockRoots computed
  rw [readCircular_writeCircular_of_ne written, keeps slot lt lo]
  intro same
  have same' := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
  have start := epoch_bounds state
  rw [Nat.add_mul, Nat.one_mul] at high
  rw [Nat.sub_mul, Nat.one_mul] at lo
  exact Nat.mod_ne_of_sub_lt (by omega) (by omega) same'

/-- The slots up to the first slot of the next epoch end as justification on the original state.

The last of them runs the epoch transition, on a state that reads the same values. -/
private theorem advanceSlots_outcome
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip) :
    ∀ {count : Nat} {moved after : BeaconState preset fork}, Moved state moved →
      KeepsRoots state moved → state.slot.toNat ≤ moved.slot.toNat →
      moved.slot.toNat + count + 1 =
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      advanceSlots config checks (count + 1) moved = .ok after → SameOutcome tip after
  | count, moved, after, same, keeps, low, total, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨stepped, steppedOk, rest⟩ := computed
    obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok steppedOk
    have cachedSlot := processSlot_slot cachedOk
    have cachedSame := same.processSlot cachedOk
    have cachedKeeps := keeps.processSlot window cachedOk low (by omega)
    have start := epoch_bounds state
    have stateEpoch := getCurrentEpoch_toNat state
    rw [Nat.add_mul, Nat.one_mul] at total
    have epoch : getCurrentEpoch cached = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat cached, cachedSlot]
      exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    unfold epochIfLast at epochedOk
    cases count with
    | zero =>
      simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      have boundary : nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero, show moved.slot.toNat + 1 =
          ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat by
            rw [Nat.add_mul, Nat.one_mul]; omega]
        exact Nat.mul_mod_left _ _
      simp only [boundary, ↓reduceIte] at epochedOk
      obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
      obtain ⟨current, previous, finalized, justificationBits⟩ :=
        justification_eq cachedSame epoch (sameRoots_of cachedKeeps) pulled justifiedOk
      exact ⟨frame.currentJustified.trans current, frame.previousJustified.trans previous,
        frame.finalized.trans finalized, frame.justificationBits.trans justificationBits⟩
    | succ count =>
      have notBoundary : ¬ nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
        intro boundary
        have zero := congrArg UInt64.toNat boundary
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero] at zero
        have split := Nat.div_add_mod (moved.slot.toNat + 1) preset.SLOTS_PER_EPOCH.toNat
        rw [zero, Nat.add_zero, Nat.div_eq_of_lt_le (k := (getCurrentEpoch state).toNat)
          (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega), Nat.mul_comm] at split
        omega
      simp only [notBoundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact advanceSlots_outcome window pulled (cachedSame.slot nextSlot) cachedKeeps
        (by simp only; omega) (by simp only; rw [Nat.add_mul, Nat.one_mul]; omega) rest

end Helpers

private theorem advanceSlot_target_flags_bound {bound : Epoch}
    (holds : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat) flags,
      (if current then (state.currentEpochParticipation altair).data
        else (state.previousEpochParticipation altair).data)[position]? = some flags →
      hasFlag flags TIMELY_TARGET_FLAG_INDEX = true →
      (if current then getCurrentEpoch state else getPreviousEpoch state) ≤ bound)
    (computed : advanceSlot config checks state = .ok after) :
    ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat) flags,
      (if current then (after.currentEpochParticipation altair).data
        else (after.previousEpochParticipation altair).data)[position]? = some flags →
      hasFlag flags TIMELY_TARGET_FLAG_INDEX = true →
      (if current then getCurrentEpoch after else getPreviousEpoch after) ≤ bound := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨cachedPrevious, cachedCurrent⟩ := processSlot_participation cachedOk
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro altair current position flags found set
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    simp only [processEpoch, altair, ↓reduceDIte] at epochedOk
    obtain ⟨justified, rooted, justifiedOk, head, tail⟩ := processEpochAltair_split epochedOk
    obtain ⟨-, -, -, -, -, -, -, -, -, justifiedCurrent⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    cases current
    · rcases (tail.flags.1 altair position flags).1 found with rotated | rfl
      · rcases (head.flags.1 altair position flags).2 rotated with old | rfl
        · rw [justifiedCurrent, cachedCurrent] at old
          simpa only [Bool.false_eq_true, ↓reduceIte, previousEq] using
            holds altair true position flags old set
        · exact absurd set (by decide)
      · exact absurd set (by decide)
    · rcases (tail.flags.1 altair position flags).2 found with rotated | rfl
      · simp only [processParticipationFlagUpdates, Array.getElem?_replicate] at rotated
        split at rotated
        · cases rotated
          exact absurd set (by decide)
        · cases rotated
      · exact absurd set (by decide)
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epoched
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    cases current
    · simp only [Bool.false_eq_true, ↓reduceIte] at found ⊢
      rw [cachedPrevious] at found
      rw [previousEq]
      exact holds altair false position flags found set
    · simp only [↓reduceIte] at found ⊢
      rw [cachedCurrent] at found
      rw [currentEq]
      exact holds altair true position flags found set

private theorem advanceSlot_pending_bound {bound : Epoch}
    (holds : ∀ (before : fork < .altair) (current : Bool),
      bound < (if current then getCurrentEpoch state else getPreviousEpoch state) →
      (if current then (state.currentEpochAttestations before).data
        else (state.previousEpochAttestations before).data) = #[])
    (computed : advanceSlot config checks state = .ok after) :
    ∀ (before : fork < .altair) (current : Bool),
      bound < (if current then getCurrentEpoch after else getPreviousEpoch after) →
      (if current then (after.currentEpochAttestations before).data
        else (after.previousEpochAttestations before).data) = #[] := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro before current late
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation before epochedOk
    cases current
    · simp only [Bool.false_eq_true, ↓reduceIte, previousEq] at late ⊢
      simpa only [rotated, cachedEq, ↓reduceIte] using holds before true late
    · exact emptied
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epoched
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    rw [currentEq, previousEq] at late
    cases current <;> simpa only [cachedEq] using holds before _ late

private theorem getTotalBalance_nil (s : BeaconState preset fork) :
    getTotalBalance s [] = .ok preset.EFFECTIVE_BALANCE_INCREMENT := by
  apply getTotalBalance_ok_iff_stake.mpr
  simp [Models.stake]

private theorem justification_epoch_bound {bound : Epoch}
    (flags : ∀ (altair : .altair ≤ fork) (epoch : Epoch) (indices : List ValidatorIndex),
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch = .ok indices →
      bound < epoch → indices = [])
    (pending : ∀ (before : fork < .altair) (epoch : Epoch)
      (attestations : Array (PendingAttestation preset)),
      getMatchingTargetAttestations state before epoch = .ok attestations →
      bound < epoch → attestations = #[])
    (floor : ∀ total, getTotalActiveBalance state = .ok total →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat < 2 * total.toNat)
    (computed : processJustificationAndFinalization state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      after.currentJustifiedCheckpoint.epoch ≤ bound := by
  have finish {total previous current : Gwei}
      (totalOk : getTotalActiveBalance state = .ok total)
      (previousEmpty : bound < getPreviousEpoch state →
        previous = preset.EFFECTIVE_BALANCE_INCREMENT)
      (currentEmpty : bound < getCurrentEpoch state → current = preset.EFFECTIVE_BALANCE_INCREMENT)
      (weighed : weighJustificationAndFinalization state total previous current = .ok after) :
      after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
        after.currentJustifiedCheckpoint.epoch ≤ bound := by
    rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ |
      ⟨recent, threshold, weight, thresholdOk, weightOk, passed, epoch, -⟩
    · exact .inl same
    right
    by_contra late
    have gt := UInt64.not_le.mp late
    rw [epoch] at gt
    have empty : (if recent then current else previous) = preset.EFFECTIVE_BALANCE_INCREMENT := by
      cases recent
      · exact previousEmpty gt
      · exact currentEmpty gt
    rw [empty] at weightOk
    have a := (mulChecked_ok_iff.mp thresholdOk).2
    have b := (mulChecked_ok_iff.mp weightOk).2
    have c := UInt64.le_iff_toNat_le.mp passed
    have d := floor total totalOk
    change threshold.toNat = total.toNat * 2 at a
    change weight.toNat = preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 3 at b
    omega
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · cases computed
      exact .inl rfl
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
        previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
      apply finish totalOk _ _ weighed
      · intro late
        rw [flags altair _ _ previousOk late, getTotalBalance_nil] at previousBalanceOk
        exact (Except.ok.inj previousBalanceOk).symm
      · intro late
        rw [flags altair _ _ currentOk late, getTotalBalance_nil] at currentBalanceOk
        exact (Except.ok.inj currentBalanceOk).symm
  · split at computed
    · cases computed
      exact .inl rfl
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
        previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
      have emptyBalance :
          getAttestingBalance state #[] = .ok preset.EFFECTIVE_BALANCE_INCREMENT := by
        simp [getAttestingBalance, getUnslashedAttestingIndices, unslashedAmong, sortedSet,
          filterM_nil, getTotalBalance_nil, pure, Except.pure, bind, Except.bind]
      apply finish totalOk _ _ weighed
      · intro late
        rw [pending _ _ _ previousOk late, emptyBalance] at previousBalanceOk
        exact (Except.ok.inj previousBalanceOk).symm
      · intro late
        rw [pending _ _ _ currentOk late, emptyBalance] at currentBalanceOk
        exact (Except.ok.inj currentBalanceOk).symm

private theorem advanceSlot_currentJustified_bound {bound : Epoch}
    (flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat) flags,
      (if current then (state.currentEpochParticipation altair).data
        else (state.previousEpochParticipation altair).data)[position]? = some flags →
      hasFlag flags TIMELY_TARGET_FLAG_INDEX = true →
      (if current then getCurrentEpoch state else getPreviousEpoch state) ≤ bound)
    (pending : ∀ (before : fork < .altair) (current : Bool),
      bound < (if current then getCurrentEpoch state else getPreviousEpoch state) →
      (if current then (state.currentEpochAttestations before).data
        else (state.previousEpochAttestations before).data) = #[])
    (floor : ∀ total, getTotalActiveBalance state = .ok total →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat < 2 * total.toNat)
    (computed : advanceSlot config checks state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      after.currentJustifiedCheckpoint.epoch ≤ bound := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have frame := frame_processSlot cachedOk
  obtain ⟨sr, br, header, availability, cachedEq⟩ := processSlot_ok cachedOk
  have moved : Moved state cached := ⟨state.slot, sr, br, header, availability, cachedEq⟩
  have currentEq : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch cached = getPreviousEpoch state := previous_eq currentEq
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, rest⟩ := processEpoch_frame epochedOk
    have result := justification_epoch_bound (state := cached) (bound := bound)
      (fun altair epoch indices read late => by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro index member
        obtain ⟨-, -, fs, found, set⟩ := mem_getUnslashedParticipatingIndices read index member
        have recent : epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached := by
          unfold getUnslashedParticipatingIndices at read
          dsimp only at read
          split at read
          · assumption
          · cases read
        rw [currentEq, previousEq] at recent
        rw [currentEq] at found
        simp only [cachedEq] at found
        by_cases same : epoch = getCurrentEpoch state
        · simp only [same, ↓reduceIte] at found
          exact (UInt64.not_lt.mpr (flags altair true _ _ found set)) (same ▸ late)
        · simp only [same, ↓reduceIte] at found
          have eq := recent.resolve_right same
          exact (UInt64.not_lt.mpr (flags altair false _ _ found set)) (eq ▸ late))
      (fun before epoch attestations read late => by
        unfold getMatchingTargetAttestations getMatchingSourceAttestations at read
        simp only [bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq] at read
        obtain ⟨_, ⟨_, recent, rfl⟩, read⟩ := read
        have empty : (if epoch = getCurrentEpoch cached then
            (cached.currentEpochAttestations before).data
            else (cached.previousEpochAttestations before).data) = #[] := by
          rw [currentEq, previousEq] at recent
          rw [currentEq]
          by_cases same : epoch = getCurrentEpoch state
          · simpa only [same, ↓reduceIte, cachedEq] using pending before true (same ▸ late)
          · simpa only [same, Bool.false_eq_true, ↓reduceIte, cachedEq] using
              pending before false ((recent.resolve_right same) ▸ late)
        simpa only [empty, Array.isEmpty_empty, ↓reduceIte, Except.ok.injEq] using read.symm)
      (fun total read => floor total (by rwa [totalActive_eq moved currentEq] at read))
      justifiedOk
    change epoched.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨ _
    rw [rest.currentJustified, ← frame.currentJustified]
    exact result
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epoched
    exact .inl frame.currentJustified

private theorem advanceSlots_currentJustified_bound {bound : Epoch} {count : Nat}
    (flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat) flags,
      (if current then (state.currentEpochParticipation altair).data
        else (state.previousEpochParticipation altair).data)[position]? = some flags →
      hasFlag flags TIMELY_TARGET_FLAG_INDEX = true →
      (if current then getCurrentEpoch state else getPreviousEpoch state) ≤ bound)
    (pending : ∀ (before : fork < .altair) (current : Bool),
      bound < (if current then getCurrentEpoch state else getPreviousEpoch state) →
      (if current then (state.currentEpochAttestations before).data
        else (state.previousEpochAttestations before).data) = #[])
    (floor : ∀ count middle total, advanceSlots config checks count state = .ok middle →
      middle.slot ≤ after.slot → getTotalActiveBalance middle = .ok total →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat < 2 * total.toNat)
    (computed : advanceSlots config checks count state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      after.currentJustifiedCheckpoint.epoch ≤ bound := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    exact .inl rfl
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, stepped, rest⟩ := computed
    have lo : state.slot ≤ after.slot := by
      have a := advanceSlot_slot stepped
      have b := advanceSlots_slot count rest
      apply UInt64.le_iff_toNat_le.mpr
      omega
    have first := advanceSlot_currentJustified_bound flags pending
      (fun total totalOk => floor 0 state total rfl lo totalOk) stepped
    have last := ih (advanceSlot_target_flags_bound flags stepped)
      (advanceSlot_pending_bound pending stepped)
      (fun count next total run le totalOk => floor (count + 1) next total
        (by simpa only [advanceSlots, stepped, bind, Except.bind] using run) le totalOk) rest
    rcases last with same | bounded
    · rw [same]
      exact first
    · exact .inr bounded

/-- Empty slots within one epoch keep the current justified checkpoint. -/
theorem advanceSlots_currentJustified_same_epoch {count : Nat}
    (advanced : advanceSlots config checks count state = .ok after)
    (epoch : getCurrentEpoch after = getCurrentEpoch state) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at advanced
    subst after
    rfl
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at advanced
    obtain ⟨middle, stepped, rest⟩ := advanced
    have stepSlot := advanceSlot_slot stepped
    have restSlot := advanceSlots_slot count rest
    have middleEpoch : getCurrentEpoch middle = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      have lo := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (show state.slot.toNat ≤ middle.slot.toNat by omega)
      have hi := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (show middle.slot.toNat ≤ after.slot.toNat by omega)
      have same := congrArg UInt64.toNat epoch
      simp only [getCurrentEpoch_toNat] at same ⊢
      omega
    rw [ih rest (epoch.trans middleEpoch.symm)]
    obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok stepped
    have inside : ¬ nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
      intro boundary
      have crossed := nextSlot_epoch_of_boundary sum boundary
      have same := congrArg UInt64.toNat middleEpoch
      simp only [getCurrentEpoch_toNat] at same
      omega
    simp only [epochIfLast, inside, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epoched
    exact (frame_processSlot cachedOk).currentJustified

/-- Processing slots within one epoch keeps the current justified checkpoint. -/
theorem processSlots_currentJustified_same_epoch {slot : Slot}
    (advanced : processSlots config checks state slot = .ok after)
    (epoch : getCurrentEpoch after = getCurrentEpoch state) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
  obtain ⟨_, -, run⟩ := advanced
  exact advanceSlots_currentJustified_same_epoch run epoch

/-- Advance a state to the first slot of the next epoch, with no block on the way.

Its justified and finalized checkpoints are then those of the state after justification.

Its justification bits are also those of that state.

That step reads the same participation, balances and block roots as the epoch transition.

The theorem assumes that the block roots of the history cover two epochs, as both presets do.

The bound is on natural numbers, since twice the slots of an epoch could overflow 64 bits. -/
theorem processSlots_checkpoints_eq_of_justification
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip)
    (start : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok next)
    (advanced : processSlots config checks state next = .ok after) :
    after.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint ∧
      after.previousJustifiedCheckpoint = tip.previousJustifiedCheckpoint ∧
      after.finalizedCheckpoint = tip.finalizedCheckpoint ∧
      after.justificationBits = tip.justificationBits := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
  obtain ⟨_, lt, advanced⟩ := advanced
  have lt' := UInt64.lt_iff_toNat_lt.mp lt
  have nextValue : next.toNat =
      ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [(mulChecked_ok_iff.mp start).2, UInt64.toNat_add, UInt64.toNat_one]
    have bounded := (getCurrentEpoch state).toNat_lt
    by_cases full : (getCurrentEpoch state).toNat + 1 < 2 ^ 64
    · rw [Nat.mod_eq_of_lt full]
    · have wrapped : ((getCurrentEpoch state).toNat + 1) % 2 ^ 64 = 0 := by omega
      rw [(mulChecked_ok_iff.mp start).2, UInt64.toNat_add, UInt64.toNat_one, wrapped,
        Nat.zero_mul] at lt'
      omega
  obtain ⟨count, counted⟩ : ∃ count, next.toNat - state.slot.toNat = count + 1 :=
    ⟨next.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  exact advanceSlots_outcome (moved := state) window pulled
    ⟨state.slot, state.stateRoots, state.blockRoots, state.latestBlockHeader,
      state.executionPayloadAvailability, rfl⟩
    (fun _ _ _ => rfl) (Nat.le_refl _) (by omega) advanced

/-- Any slot of the next epoch reads the justification computed before the empty slots. -/
theorem processSlots_currentJustified_next_epoch {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip)
    (advanced : processSlots config checks state slot = .ok after)
    (epoch : (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1) :
    after.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint := by
  have afterSlot := (processSlots_slot advanced).2
  let boundary := after.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH
  have boundaryOk : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok boundary := by
    have bounded := (getCurrentEpoch after).toNat_lt
    have same : getCurrentEpoch state + 1 = getCurrentEpoch after := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_one, ← epoch, Nat.mod_eq_of_lt bounded]
    rw [same]
    exact computeStartSlotAtEpoch_computeEpochAtSlot after.slot
  have value : boundary.toNat =
      ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    have h := (computeStartSlotAtEpoch_ok_iff.mp
      (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) after.slot)).2
    change boundary.toNat = (getCurrentEpoch after).toNat * preset.SLOTS_PER_EPOCH.toNat at h
    rwa [epoch] at h
  have lo : state.slot < boundary := by
    have pos := UInt64.lt_iff_toNat_lt.mp positive
    have bound := Nat.lt_div_mul_add (a := state.slot.toNat) pos
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [value, getCurrentEpoch_toNat, Nat.add_mul, Nat.one_mul]
    omega
  have hi : boundary ≤ slot := by
    rw [← afterSlot, UInt64.le_iff_toNat_le, value, ← epoch, getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  by_cases same : boundary = slot
  · exact (processSlots_checkpoints_eq_of_justification window pulled
      (same ▸ boundaryOk) advanced).1
  · obtain ⟨middle, before, rest⟩ := processSlots_split lo
      (UInt64.lt_of_le_of_ne hi same) advanced
    have middleEpoch : getCurrentEpoch middle = getCurrentEpoch after := by
      rw [getCurrentEpoch, (processSlots_slot before).2]
      have h := computeEpochAtSlot_computeStartSlotAtEpoch positive boundaryOk
      rw [h]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_one, ← epoch,
        Nat.mod_eq_of_lt (getCurrentEpoch after).toNat_lt]
    exact (processSlots_currentJustified_same_epoch rest middleEpoch.symm).trans
      (processSlots_checkpoints_eq_of_justification window pulled boundaryOk before).1

/-- Empty slots select the original justification, its next-epoch pull-up, or an older source.

The balance floor applies at every intermediate state, not only at the start.

The stale case retains the original checkpoint as an alternative. -/
theorem processSlots_source_selector {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip)
    (advanced : processSlots config checks state slot = .ok after)
    (floor : ∀ count middle total, advanceSlots config checks count state = .ok middle →
      middle.slot ≤ slot → getTotalActiveBalance middle = .ok total →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat < 2 * total.toNat) :
    (getCurrentEpoch after = getCurrentEpoch state ∧
      after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint) ∨
    ((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1 ∧
      after.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint) ∨
    ((getCurrentEpoch state).toNat + 1 < (getCurrentEpoch after).toNat ∧
      (after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
        after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state)) := by
  by_cases same : getCurrentEpoch after = getCurrentEpoch state
  · exact .inl ⟨same, processSlots_currentJustified_same_epoch advanced same⟩
  by_cases next : (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1
  · exact .inr (.inl ⟨next,
      processSlots_currentJustified_next_epoch positive window pulled advanced next⟩)
  have slotEq := (processSlots_slot advanced).2
  have run := advanced
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
  obtain ⟨_, lo, run⟩ := run
  have bound := advanceSlots_currentJustified_bound (bound := getCurrentEpoch state)
    (fun _ current _ _ _ _ => by
      cases current
      · exact getPreviousEpoch_le state
      · exact UInt64.le_refl _)
    (fun _ current late => by
      cases current
      · exact False.elim ((UInt64.not_lt.mpr (getPreviousEpoch_le state)) late)
      · exact False.elim ((UInt64.not_lt.mpr (UInt64.le_refl _)) late))
    (fun count middle total run le read => floor count middle total run (slotEq ▸ le) read) run
  refine .inr (.inr ⟨?_, bound⟩)
  have monotone := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
    (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lo))
  have ne : (getCurrentEpoch after).toNat ≠ (getCurrentEpoch state).toNat :=
    fun eq => same (UInt64.toNat_inj.mp eq)
  rw [← slotEq] at monotone
  simp only [getCurrentEpoch_toNat] at ne next ⊢
  omega

/-- The pulled-up tip of a block records the justified checkpoint of the next epoch.

The state of the block must advance to the first slot of the next epoch.

The store records no finalized checkpoint for each block; the previous theorem covers that one.

The theorem assumes that the block roots of the history cover two epochs, as both presets do. -/
theorem Store.computePulledUpTip_unrealizedJustification {store pulledStore : Store preset fork}
    {root : Root}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : store.computePulledUpTip config root = .ok pulledStore)
    (stateOk : store.blockState root = .ok state)
    (start : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok next)
    (advanced : processSlots config checks state next = .ok after) :
    pulledStore.unrealizedJustifications[root]? = some after.currentJustifiedCheckpoint := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨found, foundOk, tip, weighed, block, -, epoch, -, pulled⟩ := pulled
  rw [stateOk, Except.ok.injEq] at foundOk
  subst foundOk
  rw [(processSlots_checkpoints_eq_of_justification window (Base.mapError_ok_iff.mp weighed)
    start advanced).1]
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled <;>
    simp only [updateCheckpoints, updateUnrealizedCheckpoints] <;> split_ifs <;> simp

end EthLib.Consensus
