module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators

/-!
# Proofs: the target count of the rule from the votes of the store

The rule counts the honest votes that the target of the current epoch will get, at the least.

It takes the votes so far for the target, less the adversary.

It adds the honest share of the slots still to come.

The first lemma reads the votes so far as the stake of a list of voters.

The second reads the count as those votes less the adversary, plus the honest share.
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

end EthLib.Consensus
