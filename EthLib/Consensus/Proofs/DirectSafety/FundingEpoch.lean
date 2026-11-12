module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import all EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import all EthLib.Consensus.Proofs.Transition.BalanceDrift

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem funding_kept_prefix {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (credit : Nat)
    (size : t.validators.data.size = s.validators.data.size)
    (life : RegistryLifecycle s t) (slot : t.slot = s.slot)
    (queue : t.pendingConsolidations = s.pendingConsolidations)
    (effective : ∀ i, i < s.validators.data.size →
      effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i)
    (balances : (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤ credit) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + credit := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  have bound := funding_potential_change
    (s.pendingConsolidations electra).data.toList
    (s.pendingConsolidations electra).data.toList
    (fun i => actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)
    size life (by rw [epoch]) (fun _ h => Or.inl h) (fun i => ?_)
  · rw [← queue, funding_potential_eq t electra] at bound
    rw [queue, funding_potential_eq s electra] at bound
    omega
  · by_cases inside : i < s.validators.data.size
    · rw [effective i inside]; omega
    · have outside : s.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
      have outsideT : t.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
      simp only [effectiveAt, outside, outsideT, Option.map_none, Option.getD_none,
        Nat.zero_max]
      omega

private def FundingOrdinary (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source ≠ .deposits ∧ e.source ≠ .consolidations

private theorem funding_ordinary_record {fork : Fork} {pre post : BalanceReplay preset fork}
    {source : BalanceSource} {limits action}
    (initial : FundingOrdinary pre.2) (ordinary : source ≠ .deposits ∧ source ≠ .consolidations)
    (ok : recordBalance source limits action pre = .ok post) : FundingOrdinary post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, _, _, rfl⟩ := ok
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact initial e old
  · obtain rfl := List.mem_singleton.mp new
    exact ordinary

private theorem funding_ordinary_deltas {fork : Fork} (source : BalanceSource)
    (ordinary : source ≠ .deposits ∧ source ≠ .consolidations) (deltas : Array Gwei × Array Gwei)
    {pre post : BalanceReplay preset fork} (initial : FundingOrdinary pre.2)
    (ok : replayDeltas source deltas pre = .ok post) : FundingOrdinary post.2 := by
  apply foldlM_ok_invariant (fun p => FundingOrdinary p.2) _ initial ok
  intro pre i post initial ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, rewarded, rewardOk, penaltyOk⟩ := ok
  exact funding_ordinary_record
    (funding_ordinary_record initial (by decide) rewardOk) ordinary penaltyOk

private theorem funding_ordinary_rewards {fork : Fork} {pre post : BalanceReplay preset fork}
    (initial : FundingOrdinary pre.2)
    (ok : replayRewards (config := config) pre = .ok post) : FundingOrdinary post.2 := by
  unfold replayRewards at ok
  split at ok
  · cases ok; exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, folded, last⟩ := bind_ok_iff.mp ok
      exact funding_ordinary_deltas _ (by decide) _
        (foldlM_ok_invariant (fun p => FundingOrdinary p.2)
          (fun _ _ _ h ok => funding_ordinary_deltas _ (by decide) _ h ok) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact funding_ordinary_deltas _ (by decide) _
        (foldlM_ok_invariant (fun p => FundingOrdinary p.2)
          (fun _ _ _ h ok => funding_ordinary_deltas _ (by decide) _ h ok)
          (funding_ordinary_deltas _ (by decide) _ initial rewardOk) folded) last

private theorem funding_rewards {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processRewardsAndPenalties config s = .ok t)
    {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (s, []) = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + (events.map fundingCredit).sum := by
  have coverage := coverage_rewards (coverage_refl ⟨fork, s⟩) replayed
  have bounded := replayRewards_bounded (by simp [EventsBounded]) replayed
  have ordinary := funding_ordinary_rewards (by simp [FundingOrdinary]) replayed
  have balanceBound : (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤
      (events.map fundingCredit).sum := by
    calc
      _ ≤ ∑ i ∈ Finset.range s.validators.data.size,
          (events.map fun e => coverageDelta false e.before e.after i).sum :=
        Finset.sum_le_sum (fun i _ => coverage false i)
      _ ≤ (events.map fun e => e.credits).sum :=
        coverage_sum_events events _ false
      _ ≤ (events.map fundingCredit).sum := by
        have pointwise : ∀ e ∈ events, e.credits ≤ fundingCredit e := by
          intro e member
          have bound := (bounded e member).1
          have ord := ordinary e member
          cases source : e.source <;> simp_all [fundingCredit]
        clear coverage bounded ordinary replayed
        induction events with
        | nil => simp
        | cons e rest ih =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (pointwise e (by simp))
            (ih (fun e h => pointwise e (by simp [h])))
  have registry : t.validators = s.validators := by
    rw [processRewardsAndPenalties_frame ok]
  exact funding_kept_prefix electra _ (congrArg (·.data.size) registry)
    (registryLifecycle_processRewardsAndPenalties ok) (frame_processRewardsAndPenalties ok).slot
    (processRewardsAndPenalties_pendingConsolidations ok)
    (fun i _ => by simp only [effectiveAt, registry]) balanceBound

private theorem funding_same {fork : Fork} {s t : BeaconState preset fork}
    (registry : t.validators = s.validators) (balances : t.balances = s.balances)
    (slot : t.slot = s.slot) (queue : t.pendingConsolidations = s.pendingConsolidations) :
    fundedStake ⟨fork, t⟩ = fundedStake ⟨fork, s⟩ := by
  simp only [fundedStake, effectiveAt, actualBalanceAt, registry, balances,
    getCurrentEpoch, slot, queue]
  rfl

private theorem funding_registry {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processRegistryUpdates config s = .ok t) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  have bound := funding_kept_prefix electra 0 (sameSizes_processRegistryUpdates ok).1
    (registryLifecycle_processRegistryUpdates ok) (frame_processRegistryUpdates ok).slot
    (processRegistryUpdates_pendingConsolidations ok) (effectiveKept_registry ok)
    (by simp only [actualBalanceAt, coverage_registry ok, Nat.sub_self, Finset.sum_const_zero]
        exact Nat.le_refl _)
  simpa using bound

private theorem funding_slashings {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processSlashings s = .ok t) : fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  obtain ⟨_, _, credits, _⟩ := delayed_slashing_bounds s t (s.validators.bound early) ok
  have registry := balanceDrift_slashings ok
  have bound := funding_kept_prefix electra 0 (sameSizes_processSlashings ok).1
    (registryLifecycle_processSlashings ok) (frame_processSlashings ok).slot
    (processSlashings_pendingConsolidations ok)
    (fun i _ => by simp only [effectiveAt, registry]) ?_
  · simpa using bound
  · have covered := coverage_event_sum
      (⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ : BalanceEvent preset)
      s.validators.data.size false
    change (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤ balanceCredits s t at covered
    omega

private theorem funding_before {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s) (pending : PendingConsolidationInvariant config s)
    (ok : epochBeforePayments config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  simp only [epochBeforePayments, altair, before, ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pendingOk⟩ := ok
  have justifiedRegistry := (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1
  have justifiedSlot := (randaoMixes_slot_processJustificationAndFinalization justifiedOk).2
  have justifiedFunding := funding_same justifiedRegistry (coverage_justification justifiedOk)
    justifiedSlot (processJustificationAndFinalization_pendingConsolidations justifiedOk)
  have scoredFunding := funding_same (balanceDrift_inactivity scoredOk).1
    (coverage_inactivity scoredOk) (frame_processInactivityUpdates scoredOk).slot
    (processInactivityUpdates_pendingConsolidations scoredOk)
  obtain ⟨rewardEvents, rewardReplay⟩ := replayRewards_result scored rewarded [] rewardedOk
  have rewardFunding := funding_rewards electra rewardedOk rewardReplay
  have registryFunding := funding_registry electra registeredOk
  have slashFunding := funding_slashings electra early slashedOk
  have resetFunding := funding_same (balanceDrift_reset resetOk).1
    (balanceDrift_reset resetOk).2 (frame_processEth1DataReset resetOk).slot
    (processEth1DataReset_pendingConsolidations resetOk)
  have resetMatch : BalancesMatch reset :=
    (frame_processEth1DataReset resetOk).balancesMatch <|
    (frame_processSlashings slashedOk).balancesMatch <|
    (frame_processRegistryUpdates registeredOk).balancesMatch <|
    (frame_processRewardsAndPenalties rewardedOk).balancesMatch <|
    (frame_processInactivityUpdates scoredOk).balancesMatch <|
    balancesMatch_of_sameSizes (sameSizes_processJustificationAndFinalization justifiedOk) matched
  have resetOrder : ExitsOrdered reset :=
    (frame_processEth1DataReset resetOk).exitsOrdered <|
    (frame_processSlashings slashedOk).exitsOrdered <|
    (frame_processRegistryUpdates registeredOk).exitsOrdered <|
    (frame_processRewardsAndPenalties rewardedOk).exitsOrdered <|
    (frame_processInactivityUpdates scoredOk).exitsOrdered <|
    (by simpa only [ExitsOrdered, justifiedRegistry] using ordered)
  have a₁ := activation.processJustificationAndFinalization justifiedOk
  have a₂ := a₁.processInactivityUpdates scoredOk
  have a₃ := a₂.processRewardsAndPenalties rewardedOk
  have a₄ := a₃.processRegistryUpdates registeredOk
  have resetActivation := (a₄.processSlashings slashedOk).processEth1DataReset resetOk
  have resetPending := (((((pending.justification justifiedOk).inactivity scoredOk).rewards
    rewardedOk).registry registeredOk).slashings slashedOk).eth1Reset resetOk
  obtain ⟨deposited, depositedOk, consolidatedOk, pendingFunding⟩ :=
    funding_pending_balances electra early delay resetMatch resetOrder resetActivation
      resetPending pendingOk
  have carry : reset.depositBalanceToConsume = s.depositBalanceToConsume := by
    rw [depositCarry_processEth1DataReset resetOk,
      depositCarry_processSlashings slashedOk, depositCarry_processRegistryUpdates registeredOk,
      depositCarry_processRewardsAndPenalties rewardedOk,
      depositCarry_processInactivityUpdates scoredOk,
      depositCarry_processJustificationAndFinalization justifiedOk]
  obtain ⟨limit, limitOk⟩ := delayedSlashingLimit_result slashedOk
  have slashReplay : recordBalance .slashings
      (fun s => return (0, ← delayedSlashingLimit s)) processSlashings
      (registered, rewardEvents) = .ok
        (slashed, rewardEvents ++
          [⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩]) := by
    simp [recordBalance, limitOk, slashedOk, bind, Except.bind, pure, Except.pure]
  simp only [bind, Except.bind, pure, Except.pure] at slashReplay
  have equal : events = rewardEvents ++
      [⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩] ++
      [⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
        consumedDeposits reset deposited electra, 0⟩] ++
      [⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, t⟩,
        consumedConsolidations deposited t electra,
        consumedConsolidations deposited t electra⟩] := by
    simp only [epochBalanceReplay, altair, before, electra, ↓reduceDIte,
      carryBalance_result justifiedOk [],
      carryBalance_result (action := fun s => processInactivityUpdates config s altair) scoredOk [],
      rewardReplay, carryBalance_result registeredOk rewardEvents, slashReplay,
      carryBalance_result resetOk _, depositedOk, consolidatedOk,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at replayed
    exact replayed.2.symm
  rw [equal, List.map_append, List.map_append, List.map_append,
    List.sum_append, List.sum_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fundingCredit,
    Nat.add_zero, funding_carry, electra, ↓reduceDIte]
  have withdrawn : withdrawnConsolidationCredit
      ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, consumedDeposits reset deposited electra, 0⟩ =
      withdrawnConsolidationCredit ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, 0, 0⟩ := rfl
  rw [withdrawn]
  rw [carry] at pendingFunding
  rw [scoredFunding, justifiedFunding] at rewardFunding
  omega

private theorem funding_tail {fork : Fork} {s t : BeaconState preset fork}
    (altair : .altair ≤ fork) (capella : .shapella ≤ fork)
    (ok : (do
      let state ← processSlashingsReset s
      let state ← processRandaoMixesReset state
      let state ← processHistoricalSummariesUpdate state capella
      let state := processParticipationFlagUpdates state altair
      let state ← processSyncCommitteeUpdates state altair
      if fulu : Fork.fusaka ≤ fork then liftAccessor (processProposerLookahead state fulu)
      else pure state) = .ok t) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ =
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ := by
  simp only [bind_ok_iff] at ok
  obtain ⟨cleared, clearedOk, mixed, mixedOk, historical, historicalOk,
    synced, syncedOk, rest⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
  simp only [processHistoricalSummariesUpdate, processSyncCommitteeUpdates,
    processProposerLookahead, liftAccessor, Except.mapError,
    bind, Except.bind, pure, Except.pure] at historicalOk syncedOk rest
  repeat' (split at * <;> try contradiction)
  all_goals
    simp_all only [Except.ok.injEq]
    subst_vars
    rfl

/-- The epoch passes conserve funding apart from churn and the recorded external credits. -/
theorem funding_epoch {fork : Fork} {s t middle : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (ok : processEpoch config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events)) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr early
  simp only [processEpoch, altair, ↓reduceDIte,
    processEpochAltair_eq_epochBeforePayments_bind, notGloas, capella,
    ↓reduceDIte, pure_bind, bind_ok_iff] at ok
  obtain ⟨before, beforeOk, updated, updatedOk, rest⟩ := ok
  obtain ⟨recorded, recordedOk⟩ := epochBalanceReplay_before beforeOk
  have same := Except.ok.inj (recordedOk.symm.trans replayed)
  have states := (Prod.mk.inj same).1
  subst middle
  have bound := funding_before electra early delay matched ordered activation pending
    beforeOk events replayed
  have tail := funding_tail (s := updated) (t := t) altair capella
    (by simpa only [bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      exists_eq_right] using rest)
  have queue : updated.pendingConsolidations = before.pendingConsolidations := by
    unfold processEffectiveBalanceUpdates at updatedOk
    apply foldlM_ok_invariant (fun state : BeaconState preset fork =>
      state.pendingConsolidations = before.pendingConsolidations) ?_ rfl updatedOk
    intro state i next kept step
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, _, _, _, _, _, set⟩ := step
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact kept
  have effective := funding_effective_updates
    (before.pendingConsolidations electra).data.toList updatedOk
  rw [← queue, funding_potential_eq updated electra] at effective
  rw [queue, funding_potential_eq before electra] at effective
  have carry := depositCarry_processEffectiveBalanceUpdates updatedOk
  simp only [funding_carry, electra, ↓reduceDIte, carry] at tail bound ⊢
  omega

end

end EthLib.Consensus.DirectSafety
