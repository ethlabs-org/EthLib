module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes
import EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes

/-!
# Proofs: the target count of the rule from the votes of the store

The rule counts the honest votes that the target of the current epoch will get, at the least.

It takes the votes so far for the target, less the adversary.

It adds the honest share of the slots still to come.

The first lemma reads the votes so far as the stake of a list of voters.

The second reads the count as those votes less the adversary, plus the honest share.

A signed vote shows that its voter signed the target.

A voter for the target of the head is in the committees that the rule reads.

This holds when the block of the target is near, or when the head is in the current epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The target score is a sum of balances over the successful latest-target tests. -/
private theorem getCurrentTargetScore_eq_sum
    {head : Root} {state : BeaconState preset fork} {target : Checkpoint} {score : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (targetOk : store.getCurrentTarget config head = .ok target)
    (scoreOk : store.getCurrentTargetScore config head = .ok score) :
    ∃ counted : List ValidatorIndex,
      (getActiveValidatorIndices state (getCurrentEpoch state)).filterM
        (fun index => return !(← validatorAt state index).slashed) =
          (Except.ok counted : Except ForkChoiceError (List ValidatorIndex)) ∧
      score.toNat = (counted.map fun index =>
        match store.latestMessages[index]? with
        | none => 0
        | some message =>
          if index ∈ store.equivocatingIndices then 0
          else if (store.getCheckpointForBlock message.root
            (getLatestMessageEpoch preset message)).toOption = some target
          then balanceAt state index.toNat else 0).sum := by
  simp only [getCurrentTargetScore, targetOk, stateOk, bind_ok_iff] at scoreOk
  obtain ⟨t, tOk, s, sOk, counted, countedOk, summed⟩ := scoreOk
  cases Except.ok.inj tOk
  cases Except.ok.inj sOk
  refine ⟨counted, countedOk, toNat_eq_of_sumGwei summed ?_⟩
  intro index member computed valueOk
  cases latest : store.latestMessages[index]? with
  | none =>
    have zero : computed = 0 := by simpa [latest, pure, Except.pure] using valueOk.symm
    simp [zero]
  | some message =>
    by_cases equivocating : index ∈ store.equivocatingIndices
    · have zero : computed = 0 := by
        simpa [latest, equivocating, pure, Except.pure] using valueOk.symm
      simp [equivocating, zero]
    · simp only [latest, equivocating, ite_false, bind_ok_iff] at valueOk
      obtain ⟨checkpoint, checkpointOk, valueOk⟩ := valueOk
      by_cases same : target = checkpoint
      · subst checkpoint
        simp only [ite_true] at valueOk
        simpa [latest, equivocating, checkpointOk, Except.toOption] using
          toNat_eq_balanceAt_of_effectiveBalance valueOk
      · have zero : computed = 0 := by simpa [same, pure, Except.pure] using valueOk.symm
        simp [equivocating, checkpointOk, Ne.symm same, zero, Except.toOption]

/-- A successful total-balance read makes the target score a finite stake, without duplicates. -/
private theorem getCurrentTargetScore_eq_stake
    {head : Root} {state : BeaconState preset fork} {target : Checkpoint} {score total : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (targetOk : store.getCurrentTarget config head = .ok target)
    (totalOk : getTotalActiveBalance state = .ok total)
    (scoreOk : store.getCurrentTargetScore config head = .ok score) :
    ∃ counted : List ValidatorIndex,
      (getActiveValidatorIndices state (getCurrentEpoch state)).filterM
        (fun index => return !(← validatorAt state index).slashed) =
          (Except.ok counted : Except ForkChoiceError (List ValidatorIndex)) ∧
      counted.Nodup ∧
      score.toNat = stake (fun v => balanceAt state v.toNat)
        (counted.toFinset.filter fun index => (match store.latestMessages[index]? with
          | none => false
          | some message => decide (index ∉ store.equivocatingIndices ∧
            (store.getCheckpointForBlock message.root
              (getLatestMessageEpoch preset message)).toOption = some target)) = true) := by
  obtain ⟨counted, countedOk, summed⟩ := getCurrentTargetScore_eq_sum stateOk targetOk scoreOk
  simp only [getTotalActiveBalance, bind_ok_iff] at totalOk
  obtain ⟨active, activeOk, _⟩ := totalOk
  -- The active indices are sorted, so without duplicates, and a filter keeps that.
  have distinct : (getActiveValidatorIndices state (getCurrentEpoch state)).Nodup := by
    have sorted := sorted_of_getActiveValidatorIndicesChecked_ok activeOk
    rw [getActiveValidatorIndicesChecked_ok activeOk] at sorted
    exact sorted.imp UInt64.ne_of_lt
  have keptDistinct := (sublist_of_filterM_ok countedOk).nodup distinct
  refine ⟨counted, countedOk, keptDistinct, ?_⟩
  rw [stake, Finset.sum_filter, List.sum_toFinset _ keptDistinct, summed]
  congr 1
  apply List.map_congr_left
  intro index _
  cases store.latestMessages[index]? with
  | none => simp
  | some message =>
    by_cases equiv : index ∈ store.equivocatingIndices <;> simp [equiv]

/-- A successful target-support count is the discounted score plus the remaining honest share. -/
private theorem computeHonestFfgSupportForCurrentTarget_eq
    {head : Root} {state : BeaconState preset fork} {slot epochStart lastSlot : Slot}
    {total soFar support : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (slotOk : store.getCurrentSlot config = .ok slot)
    (totalOk : getTotalActiveBalance state = .ok total)
    (startOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (soFarOk : store.computeCommitteeWeightBetweenSlots head state epochStart lastSlot = .ok soFar)
    (supportOk : store.computeHonestFfgSupportForCurrentTarget config head = .ok support) :
    ∃ score adversary,
      store.getCurrentTargetScore config head = .ok score ∧
      store.computeAdversarialWeight config head state epochStart lastSlot = .ok adversary ∧
      support.toNat = score.toNat - adversary.toNat +
        (total.toNat - soFar.toNat) / 100 *
          (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
  simp only [computeHonestFfgSupportForCurrentTarget, slotOk, stateOk,
    mapError_ok_iff, bind_ok_iff] at supportOk
  obtain ⟨s, sOk, st, stOk, t, tOk, score, scoreOk, first, firstOk, last, lastOk',
    weight, weightOk, remaining, remainingOk, share, shareOk, future, futureOk,
    adversary, adversaryOk, sumOk⟩ := supportOk
  cases Except.ok.inj sOk
  cases Except.ok.inj stOk
  rw [totalOk, Except.ok.injEq] at tOk
  subst t
  rw [startOk, Except.ok.injEq] at firstOk
  subst first
  rw [lastOk, Except.ok.injEq] at lastOk'
  subst last
  rw [soFarOk, Except.ok.injEq] at weightOk
  subst weight
  have remainingNat := (subChecked_ok_iff.mp remainingOk).2
  have shareNat := (subChecked_ok_iff.mp shareOk).2
  have futureNat := (mulChecked_ok_iff.mp futureOk).2
  have sumNat := (addChecked_ok_iff.mp sumOk).2
  refine ⟨score, adversary, scoreOk, adversaryOk, ?_⟩
  simpa only [toNat_saturatingSub, futureNat, UInt64.toNat_div, remainingNat, shareNat,
    UInt64.toNat_ofNat] using sumNat

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A latest vote's checkpoint target has been signed by the event that holds the vote. -/
private theorem Execution.signsTarget_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {n : ℕ} {v : ValidatorIndex} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message)
    {target : Checkpoint}
    (targetOk : ((e.world n).state u).getCheckpointForBlock message.root
      (getLatestMessageEpoch preset message) = .ok target) :
    SignsTarget e v target (e.world n).time := by
  obtain ⟨attestation, m, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start caller found
  have epoch : getLatestMessageEpoch preset message = attestation.data.target.epoch := by
    rw [same]
    unfold getLatestMessageEpoch LatestMessage.ofAttestation
    split
    · exact origin.targetEpoch.symm
    · rfl
  have root : message.root = attestation.data.beaconBlockRoot := by rw [same]; rfl
  rw [epoch, root] at targetOk
  have targetEq : attestation.data.target = target := by
    simpa [Store.getCheckpointForBlock, origin.targetRoot] using targetOk
  exact ⟨n, le_rfl, m, e.view_subset_sent n u seen, attestation.data, signed, targetEq⟩

/-- A voter for the target of the head is in the committees that the rule reads.

The target is the one of the current epoch, in the chain of the head.

The rule reads the committees of the current epoch so far, in the state of the head.

The target state and the state of the head must agree on the committees of the epoch of the vote.

That holds in two cases.

The block of the target is at most one epoch before the current epoch.

Then the vote and the head descend from that block, so the store's committee agreement applies.

Or the block of the head is in the current epoch.

Then the state of the target checkpoint runs on to the state of the head.

The head state must be before the mix that the seed of the epoch reads is written again.
-/
private theorem Execution.mem_window_of_target {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} {head : ForkChoiceNode}
    {slot first lastSlot : Slot} {participants : Std.TreeSet ValidatorIndex}
    {v : ValidatorIndex} {attestation : Attestation preset fork}
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first lastSlot =
      .ok participants)
    (targetOk : ((e.world k).state w).getCurrentTarget config head.root =
      .ok attestation.data.target)
    (origin : ((e.world k).state w).VoteOrigin config v attestation)
    (inReach : (∀ rootBlock : BeaconBlock preset fork,
      ((e.world k).state w).blocks[attestation.data.target.root]? = some rootBlock →
      (computeEpochAtSlot preset slot).toNat ≤
        (computeEpochAtSlot preset rootBlock.slot).toNat + 1) ∨
      ∀ headBlock : BeaconBlock preset fork,
        ((e.world k).state w).blocks[head.root]? = some headBlock → first ≤ headBlock.slot) :
    v ∈ participants := by
  have reached := e.forwardReachableWith
    (fun u member => (start u member) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  -- The target is the current one, so its epoch is the epoch of the slot.
  obtain ⟨epoch, targetRoot, epochOk, headTarget, targetEq⟩ :=
    Store.getCurrentTarget_eq_ok_iff.mp targetOk
  have epochRead : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have epochEq : epoch = computeEpochAtSlot preset slot :=
    Except.ok.inj (epochOk.symm.trans epochRead)
  have targetEpoch : attestation.data.target.epoch = computeEpochAtSlot preset slot :=
    (congrArg Checkpoint.epoch targetEq).trans epochEq
  have rootEq : attestation.data.target.root = targetRoot := congrArg Checkpoint.root targetEq
  obtain ⟨_, rootBlock, _, rootFound, _, headDescends⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas headTarget
  have voteTarget := origin.targetRoot
  rw [rootEq] at voteTarget
  obtain ⟨_, _, _, _, _, voteDescends⟩ := Store.isAncestor_of_getCheckpointBlock preGloas voteTarget
  rw [← rootEq] at rootFound headDescends voteDescends
  -- The head has a state, at or before the current slot.
  obtain ⟨headBlock, headBlockFound, -⟩ := Store.slot_le_of_isAncestor rootFound headDescends
  obtain ⟨headState, headFound, -, -⟩ := reached.reachable.blockStatesFromParents headBlockFound
  have headLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot headFound slotOk
  have headCurrent :
      (getCurrentEpoch headState).toNat ≤ (computeEpochAtSlot preset slot).toNat := by
    rw [getCurrentEpoch_toNat]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp headLe)
  have voteEpoch :
      computeEpochAtSlot preset attestation.data.slot = computeEpochAtSlot preset slot :=
    origin.targetEpoch.symm.trans targetEpoch
  -- The target state and the state of the head agree on the committees of the vote.
  obtain ⟨targetState, index, committee, targetFound, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  have agree : CommitteesKept (computeEpochAtSlot preset attestation.data.slot) targetState
        headState ∧
      getCommitteeCountPerSlot headState (computeEpochAtSlot preset attestation.data.slot) =
        getCommitteeCountPerSlot targetState (computeEpochAtSlot preset attestation.data.slot) := by
    rcases inReach with near | atOrAfter
    · exact reached.committeesKept_of_voteOrigin anchorSlot minLookahead maxLookahead (by omega)
        rootFound headDescends origin rfl voteDescends
        (by rw [voteEpoch]; exact near rootBlock rootFound) targetFound headFound
        (by rw [voteEpoch]; omega)
    · -- The state of the target checkpoint runs on to the state of the head.
      have startOk : computeStartSlotAtEpoch preset attestation.data.target.epoch = .ok first := by
        rw [targetEpoch]
        exact firstOk
      have checkpoint : ((e.world k).state w).getCheckpointBlock head.root
          attestation.data.target.epoch = .ok attestation.data.target.root := by
        rw [targetEq]
        exact headTarget
      have run := reached.runKept_of_checkpointState anchorSlot checkpoint headBlockFound startOk
        (atOrAfter headBlock headBlockFound) targetFound headFound
      -- The target state is at the start of the epoch or later.
      obtain ⟨base, start', baseFound, startOk', fromBlock⟩ :=
        reached.checkpointStatesFromBlocks targetFound
      rw [startOk, Except.ok.injEq] at startOk'
      subst startOk'
      have targetLe : first ≤ targetState.slot := by
        rcases fromBlock with ⟨baseLe, rfl⟩ | ⟨-, _, -, slotsOk⟩
        · exact baseLe
        · exact (processSlots_slot slotsOk).2 ▸ UInt64.le_refl _
      have targetEpochLe : (computeEpochAtSlot preset attestation.data.slot).toNat ≤
          (getCurrentEpoch targetState).toNat := by
        rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
        · rw [computeEpochAtSlot, UInt64.toNat_div, zero, Nat.div_zero]
          exact Nat.zero_le _
        · have voteStart : computeStartSlotAtEpoch preset
              (computeEpochAtSlot preset attestation.data.slot) = .ok first := by
            rw [voteEpoch]
            exact firstOk
          rw [← computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive)
            voteStart, getCurrentEpoch_toNat]
          exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp targetLe)
      exact run.committees_count (by omega) (le_activityFixedEpoch maxLookahead (by omega))
        (by rw [voteEpoch]; omega)
  obtain ⟨kept, count⟩ := agree
  -- The slot of the vote is in the range that the rule reads.
  have low : first ≤ attestation.data.slot := by
    have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
    have divLe := Nat.div_mul_le_self attestation.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    change (computeEpochAtSlot preset attestation.data.slot).toNat *
      preset.SLOTS_PER_EPOCH.toNat ≤ attestation.data.slot.toNat at divLe
    rw [voteEpoch] at divLe
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have high : attestation.data.slot ≤ lastSlot := by
    obtain ⟨current, currentOk, past⟩ := origin.past
    have currentEq := Except.ok.inj (currentOk.symm.trans slotOk)
    subst current
    have lastNat := (subChecked_ok_iff.mp lastOk).2
    have pastNat := UInt64.lt_iff_toNat_lt.mp past
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one] at lastNat
    omega
  exact Store.mem_getCommitteesBetweenSlots windowOk low high
    (Store.blockState_ok_iff.mpr headFound) (count ▸ below)
    ((kept _ _ rfl).trans committeeOk) member

end Models.Network

end EthLib.Consensus
