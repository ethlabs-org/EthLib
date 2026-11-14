module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.Transition.TargetFlags
public import EthLib.Consensus.Proofs.Transition.TargetPending
public import EthLib.Consensus.Proofs.Transition.EpochParticipation
public import EthLib.Consensus.Proofs.Transition.EpochUpdates

/-!
# Proofs: included target votes justify at an epoch boundary

A quorum of active, unslashed voters passes the target test after the first two epochs.

The slot transition caches roots before weighing votes, then rotates the votes for the next epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

private theorem recent_epoch_ne (state : BeaconState preset fork)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    getPreviousEpoch state ≠ getCurrentEpoch state := by
  have previous := getPreviousEpoch_toNat state
  have late : 1 < (getCurrentEpoch state).toNat := counted
  intro same
  have := congrArg UInt64.toNat same
  omega

private theorem validator_of_active_read {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {v : ValidatorIndex}
    (read : getActiveValidatorIndicesChecked state epoch = .ok indices)
    (active : v ∈ getActiveValidatorIndices state epoch) (clean : NotSlashed state v) :
    ∃ validator, getValidator state v = .ok validator ∧ validator.slashed = false := by
  have same := getActiveValidatorIndicesChecked_ok read
  obtain ⟨validator, found, -⟩ := mem_iff_of_getActiveValidatorIndicesChecked_ok read |>.mp
    (same ▸ active)
  refine ⟨validator, ?_, ?_⟩
  · simp [getValidator, found]
  · simpa [NotSlashed, found] using clean

private theorem mem_target_indices {state : BeaconState preset fork}
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (altair : .altair ≤ fork) (recent : Bool) {indices : List ValidatorIndex}
    (read : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices)
    {v : ValidatorIndex}
    (active : v ∈ getActiveValidatorIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (clean : NotSlashed state v)
    (flagged : TargetFlagAt (recentParticipation state altair recent) v.toNat) :
    v ∈ indices := by
  have ne := recent_epoch_ne state counted
  have selected : (if recent then getCurrentEpoch state else getPreviousEpoch state) =
      getPreviousEpoch state ∨
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        getCurrentEpoch state := by cases recent <;> simp
  unfold getUnslashedParticipatingIndices at read
  dsimp only at read
  rw [ite_eq_left selected] at read
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
    obtain ⟨activeIndices, activeOk, entries, entriesOk, rfl⟩ := read
    obtain ⟨validator, validatorOk, unslashed⟩ := validator_of_active_read activeOk active clean
    have member : v ∈ activeIndices := (getActiveValidatorIndicesChecked_ok activeOk).symm ▸ active
    obtain ⟨entry, entryMem, entryOk⟩ := exists_mem_of_mapM_ok entriesOk member
    obtain ⟨flags, found, set⟩ := flagged
    have flagsEq : (if (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        getCurrentEpoch state then (state.currentEpochParticipation altair).data
        else (state.previousEpochParticipation altair).data)[v.toNat]? = some flags := by
      cases recent <;> simpa [recentParticipation, ne] using found
    simp only [flagsEq, validatorOk, set, unslashed, Bool.not_false, Bool.and_self,
      bind, Except.bind, Except.ok.injEq] at entryOk
    subst entry
    exact List.mem_map.mpr ⟨(v, true), List.mem_filter.mpr ⟨entryMem, rfl⟩, rfl⟩

private theorem mem_pending_indices {state : BeaconState preset fork}
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (before : fork < .altair) (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (matching : getMatchingTargetAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    (read : getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex}
    (active : v ∈ getActiveValidatorIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (clean : NotSlashed state v)
    {pending : PendingAttestation preset} (member : pending ∈ recentPending state before recent)
    (target : pending.data.target.root = root) {signers : List ValidatorIndex}
    (signersOk : getPendingAttestingIndices state pending = .ok signers)
    (signed : v ∈ signers) : v ∈ indices := by
  have ne := recent_epoch_ne state counted
  have sourceOk : getMatchingSourceAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        .ok (recentPending state before recent) := by
    cases recent <;> simp [getMatchingSourceAttestations, recentPending, ne, ensure]
  have listed : pending ∈ attestations := by
    simp only [getMatchingTargetAttestations, sourceOk, bind, Except.bind] at matching
    split at matching
    · rename_i empty
      have := Array.isEmpty_iff.mp empty
      rw [this] at member
      simp at member
    · simp only [rootOk, liftAccessor, Except.mapError,
        pure, Except.pure, Except.ok.injEq] at matching
      subst attestations
      exact Array.mem_filter.mpr ⟨member, by simpa using target⟩
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at read
  obtain ⟨lists, listsOk, filtered⟩ := read
  obtain ⟨result, resultMem, resultOk⟩ := exists_mem_of_mapM_ok listsOk
    (Array.mem_toList_iff.mpr listed)
  have same := Except.ok.inj (signersOk.symm.trans resultOk)
  subst result
  have inSet : v ∈ sortedSet lists.flatten :=
    mem_sortedSet.mpr (List.mem_flatten.mpr ⟨signers, resultMem, signed⟩)
  have pass : (do return !(← getValidator state v).slashed) =
      (Except.ok true : Except AccessorError Bool) := by
    have inside : v.toNat < state.validators.data.size := by
      simp only [getActiveValidatorIndices, List.mem_filterMap,
        Option.ite_none_right_eq_some, Option.some.injEq,
        List.mem_zipIdx_iff_getElem?, Prod.exists] at active
      obtain ⟨validator, position, found, _, same⟩ := active
      have bound := (List.getElem?_eq_some_iff.mp found).1
      rw [← same, Nat.toUInt64_eq, UInt64.toNat_ofNat']
      have := Nat.mod_le position (2 ^ 64)
      simpa using Nat.lt_of_le_of_lt this bound
    let validator := state.validators.data[v.toNat]
    have found : state.validators.data[v.toNat]? = some validator :=
      Array.getElem?_eq_getElem inside
    have validatorOk := getValidator_eq_ok_iff.mpr found
    have unslashed : validator.slashed = false := by simpa [NotSlashed, found] using clean
    simp [validatorOk, unslashed]
  exact mem_filterM_ok_of_test filtered inSet pass

private theorem weighs_justifies {state after : BeaconState preset fork}
    {total previous current : Gwei}
    (weighed : weighJustificationAndFinalization state total previous current = .ok after)
    (recent : Bool)
    (quorum : 2 * total.toNat ≤ 3 * (if recent then current else previous).toNat) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at weighed
  obtain ⟨previousWeight, previousOk, threshold, thresholdOk, first, firstOk, currentWeight,
    currentOk, second, secondOk, _, _, _, _, _, _, _, _, rfl⟩ := weighed
  have thresholdEq := (mulChecked_ok_iff.mp thresholdOk).2
  have previousEq := (mulChecked_ok_iff.mp previousOk).2
  have currentEq := (mulChecked_ok_iff.mp currentOk).2
  have epochs := getPreviousEpoch_le state
  cases recent
  · have passed : threshold ≤ previousWeight := by
      simp only [UInt64.le_iff_toNat_le]
      simp only [Bool.false_eq_true, ↓reduceIte] at quorum
      simp only [UInt64.toNat_ofNat] at thresholdEq previousEq
      omega
    have firstEpoch := (justifyCheckpoint_ok firstOk).resolve_right
      (by simp [decide_eq_true passed])
    rcases justifyCheckpoint_ok secondOk with ⟨-, epoch, -⟩ | ⟨-, same⟩
    · simpa [epoch] using epochs
    · simp [same, firstEpoch.2.1]
  · have passed : threshold ≤ currentWeight := by
      simp only [UInt64.le_iff_toNat_le]
      simp only [↓reduceIte] at quorum
      simp only [UInt64.toNat_ofNat] at thresholdEq currentEq
      omega
    have secondEpoch := (justifyCheckpoint_ok secondOk).resolve_right
      (by simp [decide_eq_true passed])
    simp [secondEpoch.2.1]

/-- Included active, unslashed target voters with two thirds of the total justify their epoch. -/
theorem processJustificationAndFinalization_justifies
    {state after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {voters : Finset ValidatorIndex} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (quorum : 2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters)
    (voted : ∀ v ∈ voters,
      v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      NotSlashed state v ∧
      ((∃ altair : .altair ≤ fork,
          TargetFlagAt (recentParticipation state altair recent) v.toNat) ∨
        ∃ before : fork < .altair, ∃ pending ∈ recentPending state before recent,
          pending.data.target.root = root ∧
          ∃ indices, getPendingAttestingIndices state pending = .ok indices ∧ v ∈ indices)) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  have enough : ∀ (indices : List ValidatorIndex) (balance : Gwei),
      getTotalBalance state indices = .ok balance → voters ⊆ indices.toFinset →
      2 * total.toNat ≤ 3 * balance.toNat := by
    intro indices balance balanceOk subset
    have value := (getTotalBalance_ok_iff_stake.mp balanceOk).2.2
    have lower := stake_mono (w := fun v => balanceAt state v.toNat) subset
    omega
  have late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := UInt64.not_le.mpr counted
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    simp only [processJustificationAndFinalizationAltair, late, ↓reduceIte, bind_ok_iff,
      liftAccessor_ok, totalOk, Except.ok.injEq, exists_eq_left'] at computed
    obtain ⟨previous, previousOk, current, currentOk, previousBalance, previousBalanceOk,
      currentBalance, currentBalanceOk, weighed⟩ := computed
    apply weighs_justifies weighed recent
    have read : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) =
          .ok (if recent then current else previous) := by cases recent <;> assumption
    apply enough (if recent then current else previous) _ (by cases recent <;> assumption)
    intro v member
    obtain ⟨active, clean, flags | ⟨before, -⟩⟩ := voted v member
    · obtain ⟨_, flags⟩ := flags
      exact List.mem_toFinset.mpr (mem_target_indices counted altair recent read active clean flags)
    · exact False.elim (Nat.not_lt_of_ge altair before)
  · rename_i notAltair
    simp only [bind_ok_iff, liftAccessor_ok, totalOk, Except.ok.injEq,
      exists_eq_left', getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, previousBalance,
      ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩, currentBalance,
      ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    apply weighs_justifies weighed recent
    apply enough (if recent then currentIndices else previousIndices) _
      (by cases recent <;> assumption)
    intro v member
    obtain ⟨active, clean, voted⟩ := voted v member
    rcases voted with ⟨altair, -⟩ | ⟨before, pending, member, target, indices, read, signed⟩
    · exact absurd altair notAltair
    · exact List.mem_toFinset.mpr (mem_pending_indices counted before recent rootOk
        (attestations := if recent then current else previous)
        (by cases recent <;> assumption) (by cases recent <;> assumption)
        active clean member target read signed)

/-- At the last slot, caching preserves the quorum that the epoch transition weighs. -/
theorem advanceSlot_justifies {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {voters : Finset ValidatorIndex} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (quorum : 2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters)
    (voted : ∀ v ∈ voters,
      v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      NotSlashed state v ∧
      ((∃ altair : .altair ≤ fork,
          TargetFlagAt (recentParticipation state altair recent) v.toNat) ∨
        ∃ before : fork < .altair, ∃ pending ∈ recentPending state before recent,
          pending.data.target.root = root ∧
          ∃ indices, getPendingAttestingIndices state pending = .ok indices ∧ v ∈ indices)) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
  change _ ≤ epoched.currentJustifiedCheckpoint.epoch
  rw [frame.currentJustified]
  obtain ⟨current, previous, totalEq, -, -, -, balanceEq⟩ := processSlot_countingBalances cachedOk
  have roots : getBlockRoot cached
      (if recent then getCurrentEpoch cached else getPreviousEpoch cached) = .ok root := by
    rw [current, previous, getBlockRoot_processSlot cachedOk
      (slot_lt_epoch_add_historical positive window (by cases recent <;> simp))]
    exact rootOk
  have result := processJustificationAndFinalization_justifies (voters := voters) justifiedOk
    (current.symm ▸ counted) recent roots (totalEq.trans totalOk) ?_ ?_
  · simpa [current, previous] using result
  · simpa only [balanceEq] using quorum
  · obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have activeEq : ∀ epoch, getActiveValidatorIndices cached epoch =
        getActiveValidatorIndices state epoch := by
      intro epoch
      rw [cachedEq]
      rfl
    have pendingEq : ∀ pending, getPendingAttestingIndices cached pending =
        getPendingAttestingIndices state pending := by
      intro pending
      rw [cachedEq]
      rfl
    intro v member
    obtain ⟨active, clean, flags | pending⟩ := voted v member
    · refine ⟨?_, ?_, .inl ?_⟩
      · rwa [current, previous, activeEq]
      · simpa [cachedEq, NotSlashed] using clean
      · simpa [cachedEq, recentParticipation] using flags
    · refine ⟨?_, ?_, .inr ?_⟩
      · rwa [current, previous, activeEq]
      · simpa [cachedEq, NotSlashed] using clean
      · obtain ⟨before, attestation, member, target, indices, read, signed⟩ := pending
        refine ⟨before, attestation, ?_, target, indices, ?_, signed⟩
        · simpa only [cachedEq, recentPending] using member
        · rw [pendingEq]
          exact read

/-- The boundary carries each current target flag and pending vote into the previous list. -/
theorem advanceSlot_rotates_votes {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    {position : ℕ} (inside : position < state.validators.data.size) :
    (∀ altair : .altair ≤ fork, TargetFlagAt (recentParticipation state altair true) position →
      TargetFlagAt (recentParticipation after altair false) position) ∧
    (∀ before : fork < .altair, ∀ pending ∈ recentPending state before true,
      pending ∈ recentPending after before false) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  constructor
  · intro altair flagged
    simp only [processEpoch, altair, ↓reduceDIte] at epochedOk
    obtain ⟨justified, rooted, justifiedOk, head, tail⟩ := processEpochAltair_split epochedOk
    obtain ⟨-, -, -, -, -, validators, _, _, _, current⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    obtain ⟨flags, found, set⟩ := flagged
    have justifiedInside : position < justified.validators.data.size := by
      simpa [validators, cachedEq] using inside
    have rootedInside := Nat.lt_of_lt_of_le justifiedInside head.registryGrows
    have kept := (head.flags.2 altair position justifiedInside).2
    have rotated := (tail.flags.2 altair position rootedInside).1
    refine ⟨flags, ?_, set⟩
    change (epoched.previousEpochParticipation altair).data[position]? = some flags
    rw [rotated, processParticipationFlagUpdates_previous, kept, current]
    simpa [recentParticipation, cachedEq] using found
  · intro before pending member
    obtain ⟨rotated, -⟩ := processEpoch_pendingRotation before epochedOk
    change pending ∈ (epoched.previousEpochAttestations before).data
    rw [rotated]
    simpa [recentPending, cachedEq] using member

end EthLib.Consensus
