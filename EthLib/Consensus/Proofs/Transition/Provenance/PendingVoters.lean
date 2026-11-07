module

public import EthLib.Consensus.Proofs.Transition.Provenance.Links
public import EthLib.Consensus.Proofs.Transition.Provenance.Pending
import all Init.Data.List.Control

/-!
# Proofs: the counted voters of a weighing call before Altair

Before Altair a weighing call counts the signers of the pending attestations of an epoch.

It finds the signers from the bits of each pending attestation and a committee.

It computes that committee anew, in its own state.

This file shows that the committee is the one the inclusion of the attestation used.

So each counted voter is a signer of an attestation that a block of the chain included, and whose
indexed form was valid at its site.

The inputs of the committee stay fixed between the two, by `ShuffleKept`.

The site is in the target epoch or the one after, and so is the call.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Lists -/

/-- A member of a filtered list is a member of the list or of the start of the result. -/
theorem mem_of_filterAuxM_ok {α ε : Type} {p : α → Except ε Bool} :
    ∀ {items accumulated result : List α},
      List.filterAuxM p items accumulated = .ok result →
      ∀ x ∈ result, x ∈ items ∨ x ∈ accumulated
  | [], accumulated, result, computed, x, member => by
    simp only [List.filterAuxM] at computed
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact .inr (computed ▸ member)
  | head :: tail, accumulated, result, computed, x, member => by
    simp only [List.filterAuxM] at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨kept, _, rest⟩ := computed
    rcases mem_of_filterAuxM_ok rest x member with inTail | inAccumulated
    · exact .inl (List.mem_cons_of_mem _ inTail)
    · cases kept
      · exact .inr inAccumulated
      · rcases List.mem_cons.mp inAccumulated with rfl | inAccumulated
        · exact .inl List.mem_cons_self
        · exact .inr inAccumulated

/-- A member of a filtered list is a member of the list. -/
theorem mem_of_filterM_ok {α ε : Type} {p : α → Except ε Bool} {items result : List α}
    (computed : items.filterM p = .ok result) {x : α} (member : x ∈ result) : x ∈ items := by
  simp only [List.filterM] at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, auxOk, rfl⟩ := computed
  rcases mem_of_filterAuxM_ok auxOk x (List.mem_reverse.mp member) with inItems | inNil
  · exact inItems
  · cases inNil

/-! ## The counted voters before Altair -/

/-- Before Altair each counted voter is a signer of one of the pending attestations. -/
theorem mem_getUnslashedAttestingIndices {attestations : Array (PendingAttestation preset)}
    {voters : List ValidatorIndex}
    (computed : getUnslashedAttestingIndices state attestations = .ok voters)
    {index : ValidatorIndex} (member : index ∈ voters) :
    ∃ pending ∈ attestations.toList, ∃ signers,
      getPendingAttestingIndices state pending = .ok signers ∧ index ∈ signers := by
  simp only [getUnslashedAttestingIndices, unslashedAmong, bind_ok_iff] at computed
  obtain ⟨lists, listsOk, filtered⟩ := computed
  have inSet := mem_of_filterM_ok filtered member
  rw [mem_sortedSet, List.mem_flatten] at inSet
  obtain ⟨signers, signersMember, inSigners⟩ := inSet
  obtain ⟨pending, pendingMember, pendingOk⟩ := mapM_ok_mem listsOk signers signersMember
  exact ⟨pending, pendingMember, signers, pendingOk, inSigners⟩

/-- Before Altair the matching target attestations of an epoch are pending attestations of the
epoch whose target root is the root the state reads for it. -/
theorem mem_getMatchingTargetAttestations (before : fork < .altair) {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)}
    (computed : getMatchingTargetAttestations state before epoch = .ok attestations)
    {pending : PendingAttestation preset} (member : pending ∈ attestations.toList) :
    pending ∈ epochPending state before (decide (epoch = getCurrentEpoch state)) ∧
      getBlockRoot state epoch = .ok pending.data.target.root := by
  simp only [getMatchingTargetAttestations, getMatchingSourceAttestations, bind_ok_iff,
    ensure_ok_iff, pure, Except.pure] at computed
  obtain ⟨source, ⟨_, -, sourceOk⟩, computed⟩ := computed
  have sourceIs := Except.ok.inj sourceOk
  split at computed
  · cases computed
    simp at member
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨root, rootOk, rest⟩ := computed
    cases rest
    simp only [Array.toList_filter, List.mem_filter, beq_iff_eq] at member
    obtain ⟨inSource, sameRoot⟩ := member
    refine ⟨?_, sameRoot ▸ rootOk⟩
    rw [← sourceIs] at inSource
    unfold epochPending
    by_cases current : epoch = getCurrentEpoch state
    · simpa [current] using inSource
    · simpa [current] using inSource

/-! ## Along a chain -/

namespace ShuffleKept

variable {epoch : Epoch}

/-- Before Altair a slot step keeps the inputs of the shuffle of an epoch up to its end.

The step starts in the epoch or the one after, and ends at most one epoch after it. -/
theorem advanceSlot {next : BeaconState preset fork} (before : fork < .altair)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : epoch ≤ getCurrentEpoch state)
    (near : (getCurrentEpoch next).toNat ≤ epoch.toNat + 1)
    (computed : advanceSlot config checks state = .ok next) : ShuffleKept epoch state next := by
  have stepSlot := advanceSlot_slot computed
  simp only [EthLib.Consensus.advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextSlot, ⟨fits, nextEq⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have nextIs : nextSlot = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    rw [nextEq, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [processSlot_slot cachedOk]
  refine (processSlot cachedOk).trans ((?_ : ShuffleKept epoch cached epoched).trans (of_eq rfl rfl))
  unfold epochIfLast at epochedOk
  rw [nextIs] at epochedOk
  by_cases closes : ClosesEpoch preset state
  · have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
    simp only [last, ↓reduceIte] at epochedOk
    -- The step closes the epoch, so the state is in the epoch itself.
    have moved := epoch_of_closes stepSlot closes
    have boundNat := UInt64.le_iff_toNat_le.mp bound
    have atEpoch : getCurrentEpoch cached = epoch := by
      rw [cachedEpoch]
      exact UInt64.toNat_inj.mp (by omega)
    exact processEpoch before lookahead finite atEpoch epochedOk
  · have notLast : ¬(state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
    simp only [notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    exact epochedOk ▸ refl _

end ShuffleKept

/-- Before Altair a chain keeps the inputs of the shuffle of an epoch from the epoch on.

The chain ends before Altair, so it stays in one fork, and at most one epoch past the epoch. -/
theorem Reaches.shuffleKept {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (before : after.fork < .altair)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH)
    (bound : epoch ≤ getCurrentEpoch start.state)
    (near : (getCurrentEpoch after.state).toNat ≤ epoch.toNat + 1) :
    ∃ same : start.fork = after.fork, ShuffleKept epoch (same ▸ start.state) after.state := by
  obtain ⟨run⟩ := chain
  obtain ⟨startFork, startState⟩ := start
  induction run with
  | nil => exact ⟨rfl, .refl _⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks ⟨startFork, startState⟩ middle := ⟨run⟩
    have middleBound : epoch ≤ getCurrentEpoch middle.state := by
      have := middleChain.epoch_le
      exact UInt64.le_iff_toNat_le.mpr (Nat.le_trans (UInt64.le_iff_toNat_le.mp bound) this)
    have stepEpoch := ((Reaches.refl _).step step : Reaches config checks middle last).epoch_le
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨same, kept⟩ := more before (Nat.le_trans stepEpoch near)
      change startFork = fork at same
      subst same
      exact ⟨rfl, kept.trans (ShuffleKept.advanceSlot before lookahead finite middleBound near
        computed)⟩
    | @upgrade _ post due computed =>
      -- Every upgrade leads to Altair or a later fork.
      exfalso
      obtain ⟨fork, state⟩ := middle
      cases fork <;>
        simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
          throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
      all_goals
        obtain ⟨_, _, rfl⟩ := computed
        exact absurd before (by dsimp only; decide)
    | @block fork engine signed validateResult state post notDue computed =>
      obtain ⟨same, kept⟩ := more before (Nat.le_trans stepEpoch near)
      change startFork = fork at same
      subst same
      obtain ⟨-, processed, -⟩ := applySignedBlock_ok computed
      have postSlot := processBlock_slot processed
      have stateNear : (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 := by
        simp only at near
        unfold getCurrentEpoch at near ⊢
        rw [postSlot] at near
        exact near
      exact ⟨rfl, kept.trans (ShuffleKept.processBlock before lookahead finite middleBound
        stateNear processed)⟩

end EthLib.Consensus
