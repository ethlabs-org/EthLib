module

public import EthLib.Consensus.Proofs.Transition.EpochPassAtCall
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.PendingConsolidations
public import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.BuilderPayments
import EthLib.Consensus.Proofs.Transition.EpochDecomposition
import EthLib.Consensus.Proofs.Transition.EpochJustification
import EthLib.Consensus.Proofs.Transition.InactivityLeakTrace
import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBalances
import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts
import EthLib.Consensus.Proofs.Transition.Withdrawals
import EthLib.Consensus.Proofs.Transition.Execution
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.Slot
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
import EthLib.Consensus.Proofs.Transition.BranchLedger
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The fall of an effective balance over the end of an epoch

A voter that is never slashed loses effective balance only when the update of the effective
balances at the end of the epoch crosses the downward band.

That update reads the balance after the rewards pass.

From the call's state to that pass, the balance falls by at most the sync penalties, the queued
partial withdrawals that are due, and the penalties of the pass.

The withdrawal sweep pays only the excess above the largest effective balance, so the bound reads
the smaller of the balance and the effective balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The fall that an update of effective balances allows -/

/-- How far an effective balance can fall when the update reads a balance of at least `low`. -/
private def fallGap (inc down effective low : ℕ) : ℕ :=
  if effective ≤ low + down then 0 else effective - (low - low % inc)

/-- A balance rounded down to an increment grows with the balance. -/
private theorem rounded_mono (inc : ℕ) {low high : ℕ} (le : low ≤ high) :
    low - low % inc ≤ high - high % inc := by
  have one := Nat.mod_add_div low inc
  have two := Nat.mod_add_div high inc
  have three := Nat.div_le_div_right (c := inc) le
  have four := Nat.mul_le_mul_left inc three
  omega

/-- The allowed fall shrinks as the balance read grows. -/
private theorem fallGap_anti (inc down effective : ℕ) {low high : ℕ} (le : low ≤ high) :
    fallGap inc down effective high ≤ fallGap inc down effective low := by
  have := rounded_mono inc le
  unfold fallGap
  split <;> split <;> omega

/-- Lowering the balance read by `c` raises the allowed fall by a bounded amount.

The rise is less than `c`, an increment and the downward band together. -/
private theorem fallGap_sub {inc : ℕ} (positive : 0 < inc) (down effective low c : ℕ) :
    fallGap inc down effective (low - c) ≤
      fallGap inc down effective low + c + inc + down - 1 := by
  have one := Nat.mod_lt (low - c) positive
  have two := Nat.mod_le low inc
  have three := rounded_mono inc (Nat.sub_le low c)
  have four := Nat.mod_add_div low inc
  have five := Nat.mod_add_div (low - c) inc
  -- The two rounded values differ by less than `c` plus an increment.
  have close : low - low % inc ≤ (low - c) - (low - c) % inc + c + inc - 1 := by
    have := Nat.mod_lt low positive
    omega
  unfold fallGap
  split <;> split <;> omega

/-- An update of one effective balance within its largest lowers it by at most the allowed fall.

The fall is read below the balance that the update reads. -/
private theorem updatedEffectiveBalance_fall {largest balance effective result : Gwei}
    (bands : preset.IncrementWithinUpwardBand) (capped : effective ≤ largest)
    (computed : updatedEffectiveBalance preset largest balance effective = .ok result) :
    effective.toNat ≤ result.toNat +
      fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand effective.toNat
        balance.toNat := by
  have cap := UInt64.le_iff_toNat_le.mp capped
  have increment := bands.1
  have band := bands.2
  rcases updatedEffectiveBalance_split computed with ⟨rfl, -, -⟩ | ⟨rfl, crossed⟩
  · exact Nat.le_add_right _ _
  · have value : (min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest).toNat =
        min (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          largest.toNat := by
      rw [Base.Uint64.toNat_min, toNat_rounded]
    rw [value]
    have remainder := Nat.mod_lt balance.toNat increment
    have remainderLe := Nat.mod_le balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    unfold fallGap
    generalize balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = r at *
    split <;> omega

/-! ## The pending consolidations of an epoch -/

/-- A pass over pending consolidations lowers no balance of a validator that cannot yet leave.

Each consolidation from that validator finds it not yet withdrawable, so the pass stops there. -/
private theorem passConsolidations_floor {f : Fork} {nextEpoch : Epoch} {index : Nat} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset f} {result},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      (∀ c ∈ consolidations, c.sourceIndex.toNat = index → ∀ w,
        state.validators.data[index]? = some w → nextEpoch < w.withdrawableEpoch) →
      BalanceNotLowered index state result.1
  | [], _, _, computed, _ => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact BalanceNotLowered.refl index _
  | consolidation :: rest, state, result, computed, apart => by
    have others : ∀ c ∈ rest, c.sourceIndex.toNat = index → ∀ w,
        state.validators.data[index]? = some w → nextEpoch < w.withdrawableEpoch :=
      fun c member => apart c (List.mem_cons_of_mem _ member)
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i source sourceOk
    have sourceRead := getValidator_eq_ok_iff.mp (liftAccessor_ok.mp sourceOk)
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      exact (passConsolidations_floor recur others :)
    split at computed
    · cases computed
      exact BalanceNotLowered.refl index _
    rename_i notWithdrawable
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i lowered loweredOk
    split at computed
    · cases computed
    rename_i raised raisedOk
    split at computed
    · cases computed
    rename_i recur
    cases computed
    have lowerOk := liftAccessor_ok.mp loweredOk
    have raiseOk := liftAccessor_ok.mp raisedOk
    -- The source is not the validator, which is not yet withdrawable.
    have other : consolidation.sourceIndex.toNat ≠ index := by
      intro same
      rw [same] at sourceRead
      exact notWithdrawable (apart consolidation List.mem_cons_self same source sourceRead)
    have step : BalanceNotLowered index state raised := by
      intro earlier found
      obtain ⟨kept, keptAt, keptEq⟩ := balance_decreaseBalance lowerOk found
      rw [ite_eq_right_iff.mpr (fun h => absurd h other)] at keptEq
      obtain ⟨grown, grownAt, grownEq⟩ := balance_increaseBalance raiseOk keptAt
      refine ⟨grown, grownAt, UInt64.le_iff_toNat_le.mpr ?_⟩
      rw [grownEq, keptEq]
      exact Nat.le_add_right _ _
    have validators : raised.validators = state.validators :=
      (increaseBalance_validators raiseOk).trans (decreaseBalance_validators lowerOk)
    exact step.trans (passConsolidations_floor recur fun c member same w read =>
      others c member same w (by rw [← validators]; exact read) :)

/-! ## The epoch transition of a voter -/

/-- From Altair and before Gloas, take a validator active in the epoch of an epoch transition and
not slashed.

Its effective balance, when within its largest, falls by at most the fall allowed below its
balance after the rewards pass.

Every later step of the transition up to the update keeps or raises that balance. -/
private theorem epoch_fall {f : Fork} {c t : BeaconState preset f} (altair : .altair ≤ f)
    (early : f < .glamsterdam) (bands : preset.IncrementWithinUpwardBand)
    (ok : processEpoch config checks c = .ok t) (holds : PendingConsolidationInvariant config c)
    (matched : BalancesMatch c) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} {old : Validator} (found : c.validators.data[i]? = some old)
    (active : isActiveAt c (getCurrentEpoch c) i = true) (unslashed : old.slashed = false)
    (capped : old.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f old) :
    ∃ justified scored rewarded : BeaconState preset f,
      processJustificationAndFinalization c = .ok justified ∧
      processInactivityUpdates config justified altair = .ok scored ∧
      processRewardsAndPenalties config scored = .ok rewarded ∧
      old.effectiveBalance.toNat ≤ effectiveAt ⟨f, t⟩ i +
        fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
          old.effectiveBalance.toNat (actualBalanceAt ⟨f, rewarded⟩ i) := by
  have trace := processEpoch_trace ok
  change EpochTrace _ (.justification :: .inactivity :: .rewards :: .registry :: .slashings ::
    .eth1Reset :: .pendingDeposits :: .pendingConsolidations :: .payments ::
    .effectiveBalances :: [.slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain _ | ⟨justifiedOk, trace⟩ := trace
  obtain _ | ⟨scoredOk, trace⟩ := trace
  obtain _ | ⟨rewardedOk, trace⟩ := trace
  obtain _ | ⟨registeredOk, trace⟩ := trace
  obtain _ | ⟨slashedOk, trace⟩ := trace
  obtain _ | ⟨resetOk, trace⟩ := trace
  obtain _ | ⟨depositedOk, trace⟩ := trace
  obtain _ | ⟨consolidatedOk, trace⟩ := trace
  obtain _ | ⟨settledOk, trace⟩ := trace
  obtain _ | ⟨updatedOk, trace⟩ := trace
  rename_i justified scored rewarded registered slashed reset deposited consolidated settled
    updated
  have justifiedEdge := EpochStage.action_cases.mp justifiedOk
  have scoredEdge := EpochStage.action_cases.mp scoredOk
  have rewardedEq : processRewardsAndPenalties config scored = .ok rewarded :=
    EpochStage.action_cases.mp rewardedOk
  have registeredEq : processRegistryUpdates config rewarded = .ok registered :=
    EpochStage.action_cases.mp registeredOk
  have slashedEq : processSlashings registered = .ok slashed :=
    EpochStage.action_cases.mp slashedOk
  have updatedEq : processEffectiveBalanceUpdates settled = .ok updated :=
    EpochStage.action_cases.mp updatedOk
  have justifiedEq : processJustificationAndFinalization c = .ok justified := justifiedEdge
  have scoredEq : processInactivityUpdates config justified altair = .ok scored := by
    simpa only [EpochStage.Edge, altair, ↓reduceDIte] using scoredEdge
  refine ⟨justified, scored, rewarded, justifiedEq, scoredEq, rewardedEq, ?_⟩
  -- Justification, the scores and the rewards keep the registry and the slot.
  have justifiedSame := justifiedEdge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have scoredSame := scoredEdge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have rewardedFrame := processRewardsAndPenalties_frame rewardedEq
  have rewardedValidators : rewarded.validators = c.validators :=
    (congrArg BeaconState.validators rewardedFrame).trans (scoredSame.1.trans justifiedSame.1)
  have rewardedSlot : rewarded.slot = c.slot :=
    (congrArg BeaconState.slot rewardedFrame).trans
      (scoredSame.2.2.2.2.trans justifiedSame.2.2.2.2)
  -- The registry updates keep the validator, its flag and the balances.
  obtain ⟨registryKept, -⟩ := processRegistryUpdates_kept registeredEq
  have foundRewarded : rewarded.validators.data[i]? = some old := by
    rw [rewardedValidators]
    exact found
  obtain ⟨atRegistered, foundRegistered, sameRegistered⟩ :=
    registryKept i old foundRewarded
  have insideRegistered : i < registered.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp foundRegistered).1
  -- The slashings charge only slashed validators.
  have slashedFrame := processSlashings_frame slashedEq
  have slashedBalance : slashed.balances.data[i]? = registered.balances.data[i]? := by
    have notDue : ∀ epoch, ¬ SlashingPenaltyDue preset epoch atRegistered := fun _ due => by
      have charged := due.1
      rw [sameRegistered.2.2.2, unslashed] at charged
      exact Bool.false_ne_true charged
    by_cases electra : .pectra ≤ f
    · obtain ⟨_, _, _, _, each⟩ :=
        processSlashings_balances_of_electra electra (registered.validators.bound early) slashedEq
      obtain ⟨charged, atCharged, balanceEq⟩ := (each i).1 insideRegistered
      rw [foundRegistered, Option.some.injEq] at atCharged
      subst atCharged
      rw [balanceEq]
      simp [notDue]
    · obtain ⟨_, _, _, _, each⟩ :=
        processSlashings_balances_of_lt_electra (Nat.lt_of_not_le electra) slashedEq
      obtain ⟨charged, atCharged, balanceEq⟩ := (each i).1 insideRegistered
      rw [foundRegistered, Option.some.injEq] at atCharged
      subst atCharged
      rw [balanceEq]
      simp [notDue]
  have resetSame := (EpochStage.action_cases.mp resetOk).records
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  -- The deposits only raise balances.
  have insideReset : i < reset.validators.data.size := by
    rw [resetSame.1, congrArg BeaconState.validators slashedFrame]
    exact insideRegistered
  have depositedStep : ValidatorsKept reset deposited ∧ BalanceNotLowered i reset deposited ∧
      deposited.pendingConsolidations = reset.pendingConsolidations ∧
      deposited.slot = reset.slot := by
    have edge := EpochStage.action_cases.mp depositedOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · obtain ⟨one, two, three⟩ := processPendingDeposits_balanceNotLowered edge insideReset
      exact ⟨one, two, three, (frame_processPendingDeposits edge).slot⟩
    · subst edge
      exact ⟨ValidatorsKept.refl _, BalanceNotLowered.refl i _, rfl, rfl⟩
  have depositedSlot : deposited.slot = c.slot :=
    depositedStep.2.2.2.trans <| resetSame.2.2.2.2.trans <|
      (congrArg BeaconState.slot slashedFrame).trans <|
      (frame_processRegistryUpdates registeredEq).slot.trans rewardedSlot
  -- The validator keeps its effective balance, flag and credentials up to the update.
  have consolidatedEdge := EpochStage.action_cases.mp consolidatedOk
  have consolidatedValidators : consolidated.validators = deposited.validators := by
    have edge := consolidatedEdge
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (processPendingConsolidations_kept edge).1
    · subst edge; rfl
  have settledSame : settled.validators = consolidated.validators ∧
      settled.balances = consolidated.balances := by
    have edge := EpochStage.action_cases.mp settledOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact absurd ‹_› (Nat.not_le_of_lt early)
    · subst edge
      exact ⟨rfl, rfl⟩
  have keptAll : ValidatorsKept rewarded deposited :=
    registryKept.trans <|
      (ValidatorsKept.of_eq (congrArg BeaconState.validators slashedFrame)).trans <|
      (ValidatorsKept.of_eq resetSame.1).trans depositedStep.1
  obtain ⟨kept, atKept, sameKept⟩ := keptAll i old foundRewarded
  have atSettled : settled.validators.data[i]? = some kept := by
    rw [settledSame.1, consolidatedValidators]
    exact atKept
  -- The validator stays active through the transition, so it exits after the next epoch.
  have tail := sameBalancesRegistryScores_tail altair trace
  have activeAfter : isActiveAt t (getCurrentEpoch c) i = true := by
    rw [activeKept_processEpoch ok _ (getCurrentEpoch_le_activityFixedEpoch c) i]
    exact active
  -- The consolidations do not take from the validator.
  have consolidatedStep : BalanceNotLowered i deposited consolidated := by
    have edge := consolidatedEdge
    simp only [EpochStage.Edge] at edge
    split at edge
    · rename_i electra
      obtain ⟨result, passed, balances, -⟩ := processPendingConsolidations_pass edge
      intro earlier atEarlier
      obtain ⟨later, atLater, low⟩ := passConsolidations_floor passed (fun cons member same w
          read => by
        -- The invariant puts the source's exit after its activation, with the delay.
        have invariant : PendingConsolidationInvariant config deposited := by
          have one := justifiedEdge.pendingConsolidationInvariant holds
          have two := scoredEdge.pendingConsolidationInvariant one
          have three := (EpochStage.action_cases.mp rewardedOk).pendingConsolidationInvariant two
          have four := (EpochStage.action_cases.mp registeredOk).pendingConsolidationInvariant
            three
          have five := (EpochStage.action_cases.mp slashedOk).pendingConsolidationInvariant four
          have six := (EpochStage.action_cases.mp resetOk).pendingConsolidationInvariant five
          exact (EpochStage.action_cases.mp depositedOk).pendingConsolidationInvariant six
        obtain ⟨w', read', -, ordered, assigned⟩ := (invariant electra).2 cons member
        rw [same, read, Option.some.injEq] at read'
        subst w'
        rw [atKept, Option.some.injEq] at read
        subst w
        -- The validator after the transition keeps that exit and is active, so it exits later.
        obtain ⟨u, atU, life⟩ :=
          (registryLifecycle_processEffectiveBalanceUpdates updatedEq).validators i kept atSettled
        have exitSame := life.exitEpoch assigned
        have atT : t.validators.data[i]? = some u := by rw [tail.2.1]; exact atU
        obtain ⟨u', atT', isActive⟩ := isActiveAt_eq_true_iff.mp activeAfter
        rw [atT, Option.some.injEq] at atT'
        subst u'
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActive
        have exitLt := UInt64.lt_iff_toNat_lt.mp isActive.2
        rw [exitSame] at exitLt
        have depositedEpoch : getCurrentEpoch deposited = getCurrentEpoch c := by
          simp only [getCurrentEpoch, depositedSlot]
        rw [depositedEpoch]
        refine UInt64.lt_iff_toNat_lt.mpr ?_
        have bound := kept.exitEpoch.toNat_lt
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
        omega) earlier atEarlier
      exact ⟨later, by rw [balances]; exact atLater, low⟩
    · subst edge
      exact BalanceNotLowered.refl i _
  -- The balance after the rewards reaches the update, no lower.
  have notLowered : BalanceNotLowered i rewarded settled :=
    (BalanceNotLowered.of_balances (processRegistryUpdates_balances registeredEq) i).trans <|
      BalanceNotLowered.trans (fun earlier atEarlier => ⟨earlier,
        by rw [slashedBalance]; exact atEarlier, UInt64.le_refl _⟩ :
          BalanceNotLowered i registered slashed) <|
      (BalanceNotLowered.of_balances resetSame.2.1 i).trans <| depositedStep.2.1.trans <|
      consolidatedStep.trans (BalanceNotLowered.of_balances settledSame.2 i)
  -- Every state of the transition has one balance for each validator.
  have settledMatch : BalancesMatch settled := by
    have scoredMatch : BalancesMatch scored := by
      unfold BalancesMatch at matched ⊢
      rw [scoredSame.1, scoredSame.2.1, justifiedSame.1, justifiedSame.2.1]
      exact matched
    have resetMatch : BalancesMatch reset := by
      have one := (frame_processSlashings slashedEq).balancesMatch <|
        (frame_processRegistryUpdates registeredEq).balancesMatch <|
        (frame_processRewardsAndPenalties rewardedEq).balancesMatch scoredMatch
      unfold BalancesMatch at one ⊢
      rw [resetSame.1, resetSame.2.1]
      exact one
    have depositedMatch : BalancesMatch deposited := by
      have edge := EpochStage.action_cases.mp depositedOk
      simp only [EpochStage.Edge] at edge
      split at edge
      · exact (frame_processPendingDeposits edge).balancesMatch resetMatch
      · subst edge; exact resetMatch
    have consolidatedMatch : BalancesMatch consolidated := by
      have edge := consolidatedEdge
      simp only [EpochStage.Edge] at edge
      split at edge
      · exact (frame_processPendingConsolidations edge).balancesMatch depositedMatch
      · subst edge; exact depositedMatch
    unfold BalancesMatch at consolidatedMatch ⊢
    rw [settledSame.1, settledSame.2]
    exact consolidatedMatch
  obtain ⟨settledBalance, owned⟩ : ∃ b, settled.balances.data[i]? = some b :=
    ⟨_, Array.getElem?_eq_getElem (by
      unfold BalancesMatch at settledMatch
      rw [settledMatch]
      exact (Array.getElem?_eq_some_iff.mp atSettled).1)⟩
  obtain ⟨effective, atUpdated, effectiveOk⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance_eq updatedEq atSettled owned
  rw [sameKept.2.1, withdrawalMaxEffectiveBalance_of_credentials sameKept.2.2.1] at effectiveOk
  have fall := updatedEffectiveBalance_fall bands capped effectiveOk
  have effectiveT : effectiveAt ⟨f, t⟩ i = effective.toNat := by
    simp [effectiveAt, tail.2.1, atUpdated]
  have low : actualBalanceAt ⟨f, rewarded⟩ i ≤ settledBalance.toNat := by
    cases atRewarded : rewarded.balances.data[i]? with
    | none => simp [actualBalanceAt, atRewarded]
    | some earlier =>
      obtain ⟨later, atLater, le⟩ := notLowered earlier atRewarded
      rw [owned, Option.some.injEq] at atLater
      subst later
      simpa [actualBalanceAt, atRewarded] using UInt64.le_iff_toNat_le.mp le
  have anti := fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
    old.effectiveBalance.toNat low
  rw [effectiveT]
  omega

/-- From Altair and before Gloas, take a validator active in an epoch and not slashed.

A slot that ends that epoch lowers its effective balance by at most the fall allowed below its
balance after the rewards pass.

The upgrades after the transition keep the effective balance of a validator that was activated. -/
private theorem crossing_fall {z z' : ForkedBeaconState preset} (altair : .altair ≤ z.fork)
    (ok : advanceSlotAcross config checks z = .ok z') (early : z'.fork < .glamsterdam)
    (next : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch z.state).toNat + 1)
    (bands : preset.IncrementWithinUpwardBand)
    (holds : PendingConsolidationInvariant config z.state) (matched : BalancesMatch z.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} {old : Validator} (found : z.state.validators.data[i]? = some old)
    (active : isActiveAt z.state (getCurrentEpoch z.state) i = true)
    (unslashed : old.slashed = false)
    (capped : old.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset z.fork old) :
    ∃ cached justified scored rewarded : BeaconState preset z.fork,
      processSlot z.state = .ok cached ∧
      processJustificationAndFinalization cached = .ok justified ∧
      processInactivityUpdates config justified altair = .ok scored ∧
      processRewardsAndPenalties config scored = .ok rewarded ∧
      old.effectiveBalance.toNat ≤ effectiveAt z' i +
        fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
          old.effectiveBalance.toNat (actualBalanceAt ⟨z.fork, rewarded⟩ i) := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have forkEarly : z.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (processUpgrades_fork_le (forked := ⟨z.fork, advanced⟩) upgraded) early
  obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, advancedEq⟩ :=
    advanceSlot_ok advancedOk
  have slotAfter : z'.state.slot = nextSlot := by
    rw [processUpgrades_slot upgraded, advancedEq]
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  swap
  · rename_i inside
    have same := nextSlot_epoch_of_inside sum inside
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotAfter] at next
    omega
  -- The slot runs the epoch transition from the cached state, which keeps the registry.
  have cachedSame : cached.validators = z.state.validators ∧
      cached.balances = z.state.balances ∧ cached.slot = z.state.slot ∧
      cached.pendingConsolidations = z.state.pendingConsolidations := by
    rw [cachedEq]; exact ⟨rfl, rfl, rfl, rfl⟩
  have cachedHolds : PendingConsolidationInvariant config cached := by
    subst cachedEq; exact holds
  have cachedMatch : BalancesMatch cached := by
    subst cachedEq; exact matched
  have cachedFound : cached.validators.data[i]? = some old := by
    rw [cachedSame.1]; exact found
  have cachedActive : isActiveAt cached (getCurrentEpoch cached) i = true := by
    subst cachedEq; exact active
  obtain ⟨justified, scored, rewarded, justifiedOk, scoredOk, rewardedOk, fall⟩ :=
    epoch_fall altair forkEarly bands epochedOk cachedHolds cachedMatch delay cachedFound
      cachedActive unslashed capped
  refine ⟨cached, justified, scored, rewarded, cachedOk, justifiedOk, scoredOk, rewardedOk, ?_⟩
  -- The upgrades keep the effective balance of a validator that was activated.
  obtain ⟨a, aRead, life⟩ := (registryLifecycle_advanceSlot advancedOk).validators i old found
  have activated : old.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    obtain ⟨old', read', isActive⟩ := isActiveAt_eq_true_iff.mp active
    rw [found, Option.some.injEq] at read'
    subst old'
    intro far
    simp only [isActiveValidator, far, FAR_FUTURE_EPOCH, Bool.and_eq_true, decide_eq_true_eq]
      at isActive
    have := UInt64.le_iff_toNat_le.mp isActive.1
    have bound := (getCurrentEpoch z.state).toNat_lt
    have exitBound := UInt64.lt_iff_toNat_lt.mp isActive.2
    have exitLt := old.exitEpoch.toNat_lt
    simp at this
    omega
  have upgradedSame := balanceDrift_upgrades_active upgraded early i a aRead
    (by rwa [life.activationEpoch activated])
  rw [upgradedSame, advancedEq]
  exact fall

/-! ## The floor of a balance under the withdrawals of a block -/

/-- In withdrawals that name each validator once, the one at `k` adds its amount to the total of
those before it, and none after it names the same validator.

This is master's private `withdrawnFrom_split` (WithdrawalAmounts.lean). -/
private theorem withdrawnFrom_at {sweep : Array Withdrawal}
    (distinct : (sweep.toList.map (·.validatorIndex.toNat)).Nodup) {k : Nat}
    (inside : k < sweep.size) :
    withdrawnFrom sweep sweep[k].validatorIndex =
      withdrawnFrom (sweep.extract 0 k) sweep[k].validatorIndex + sweep[k].amount.toNat := by
  have insideList : k < sweep.toList.length := by simpa using inside
  have pieces : sweep.toList = sweep.toList.take k ++
      sweep.toList[k] :: sweep.toList.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons insideList, List.take_append_drop]
  have later : ∀ other ∈ sweep.toList.drop (k + 1),
      other.validatorIndex ≠ sweep[k].validatorIndex := by
    intro other member same
    have whole : (sweep.toList.take (k + 1) ++ sweep.toList.drop (k + 1)).map
        (·.validatorIndex.toNat) |>.Nodup := by
      rw [List.take_append_drop]
      exact distinct
    rw [List.map_append, List.nodup_append] at whole
    refine whole.2.2 _ (List.mem_map_of_mem (List.getElem_mem (l := sweep.toList.take (k + 1))
      (n := k) (by simp; omega))) _ (List.mem_map_of_mem member) ?_
    simp [same]
  unfold withdrawnFrom
  rw [pieces]
  simp only [List.filter_append, List.filter_cons, Array.getElem_toList, decide_true,
    ↓reduceIte, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  rw [List.filter_eq_nil_iff.mpr fun other member same => later other member
    (of_decide_eq_true same)]
  simp [Array.toList_extract, List.extract_eq_take_drop]

/-- The queued partial withdrawals of a payload pay a validator only above the activation balance.

They pay only a validator whose effective balance is at least that balance. -/
private theorem partials_floor {f : Fork} {s : BeaconState preset f} {electra : .pectra ≤ f}
    {start : WithdrawalIndex} {partials : Array Withdrawal} {next : WithdrawalIndex} {count : ℕ}
    (computed : getPendingPartialWithdrawals s electra start #[] = .ok (partials, next, count))
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    {balance : Gwei} (read : s.balances.data[v.toNat]? = some balance)
    (paid : 0 < withdrawnFrom partials v) :
    withdrawnFrom partials v + preset.MIN_ACTIVATION_BALANCE.toNat ≤ balance.toNat ∧
      preset.MIN_ACTIVATION_BALANCE ≤ val.effectiveBalance := by
  have pays := getPendingPartialWithdrawals_pays computed
  have prefixes : ∀ j ≤ partials.size, withdrawnFrom (partials.extract 0 j) v = 0 ∨
      (withdrawnFrom (partials.extract 0 j) v + preset.MIN_ACTIVATION_BALANCE.toNat ≤
        balance.toNat ∧ preset.MIN_ACTIVATION_BALANCE ≤ val.effectiveBalance) := by
    intro j
    induction j with
    | zero => intro _; left; simp [withdrawnFrom]
    | succ j ih =>
      intro small
      have prior := ih (by omega)
      rw [Array.extract_succ_right (by omega) (by omega), withdrawnFrom_push]
      split
      · rename_i named
        obtain ⟨pending, -, validator, left, -, index, validatorOk, leftOk, eligible, amount⟩ :=
          pays j (by omega)
        rw [named] at index
        rw [← index] at validatorOk leftOk
        rw [getValidator_eq_ok_iff, found, Option.some.injEq] at validatorOk
        subst validator
        obtain ⟨balance', read', sum⟩ := getBalanceAfterWithdrawals_ok leftOk
        rw [read, Option.some.injEq] at read'
        subst balance'
        simp only [Array.empty_append] at sum
        simp only [isEligibleForPartialWithdrawals, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at eligible
        have amountLe :
            partials[j].amount.toNat ≤ left.toNat - preset.MIN_ACTIVATION_BALANCE.toNat := by
          rw [amount, Base.Uint64.toNat_min,
            UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt eligible.2)]
          exact Nat.min_le_left _ _
        have above := UInt64.lt_iff_toNat_lt.mp eligible.2
        right
        exact ⟨by omega, eligible.1.2⟩
      · simpa using prior
  rcases prefixes partials.size (Nat.le_refl _) with zero | holds
  · rw [Array.extract_eq_self_of_le (Nat.le_refl _)] at zero
    omega
  · rw [Array.extract_eq_self_of_le (Nat.le_refl _)] at holds
    exact holds

/-- From Electra and before Gloas, take a validator that cannot withdraw in full.

The withdrawals of a payload leave it at least the smaller of its balance and its effective
balance, less what the queued partial withdrawals pay it, up to its effective balance above the
activation balance.

The sweep pays it only its excess above its largest effective balance, which is its effective
balance. -/
private theorem withdrawals_floor {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (early : f < .glamsterdam) (electra : .pectra ≤ f)
    (computed : processWithdrawals s capella payload = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch) :
    ∃ (partials : Array Withdrawal) (next : WithdrawalIndex) (count : ℕ),
      getPendingPartialWithdrawals s electra (s.nextWithdrawalIndex capella) #[] =
        .ok (partials, next, count) ∧
      min (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat ≤
        actualBalanceAt ⟨f, t⟩ v.toNat +
          min (withdrawnFrom partials v)
            (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  obtain ⟨expected, expectedOk, -, -⟩ := processWithdrawals_expected early computed
  obtain ⟨builders, partials, buildersSweep, sweep, index1, index2, index3, index4, count1,
    count2, count3, count4, split, -, -, buildersEmpty, partialsOk, -, -,
    buildersSweepEmpty, sweepOk⟩ := getExpectedWithdrawals_parts expectedOk
  obtain ⟨rfl, rfl⟩ := buildersEmpty early
  obtain ⟨rfl, rfl⟩ := buildersSweepEmpty early
  refine ⟨partials, _, _, partialsOk electra, ?_⟩
  cases read : s.balances.data[v.toNat]? with
  | none => simp [actualBalanceAt, read]
  | some balance =>
    obtain ⟨bounded, lowered⟩ := processWithdrawals_balance_of_notBuilder computed expectedOk
      (fun gloas => absurd gloas (Nat.not_le_of_lt early)) (.inl early) read
    have after : actualBalanceAt ⟨f, t⟩ v.toNat =
        balance.toNat - withdrawnFrom expected.withdrawals v := by
      simp only [actualBalanceAt]
      cases h : t.balances.data[v.toNat]? <;> rw [h] at lowered <;> simp_all
    have before : actualBalanceAt ⟨f, s⟩ v.toNat = balance.toNat := by
      simp [actualBalanceAt, read]
    rw [after, before]
    rw [split] at bounded ⊢
    simp only [Array.empty_append, Array.append_empty, withdrawnFrom_append] at bounded ⊢
    by_cases swept : ∃ k, ∃ inside : k < sweep.size, sweep[k].validatorIndex = v
    · -- The sweep pays the validator its excess, down to its largest effective balance.
      obtain ⟨k, inside, named⟩ := swept
      obtain ⟨pays, distinct⟩ := getValidatorsSweepWithdrawals_pays (s.validators.bound early)
        sweepOk
      obtain ⟨validator, left, validatorOk, leftOk, kind⟩ := pays k inside
      have total := withdrawnFrom_at distinct inside
      rw [named] at validatorOk leftOk total
      rw [getValidator_eq_ok_iff, found, Option.some.injEq] at validatorOk
      subst validator
      obtain ⟨balance', read', sum⟩ := getBalanceAfterWithdrawals_ok leftOk
      rw [read, Option.some.injEq] at read'
      subst balance'
      simp only [Array.empty_append, withdrawnFrom_append] at sum
      rcases kind with ⟨full, -⟩ | ⟨-, excess, amount⟩
      · simp only [isFullyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq] at full
        exact absurd full.1.2 (UInt64.not_le.mpr later)
      · simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at excess
        rw [amount, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt excess.2)] at total
        have above := UInt64.lt_iff_toNat_lt.mp excess.2
        rw [← excess.1.2] at above total
        omega
    · -- Otherwise only the queued partial withdrawals pay it.
      have zero : withdrawnFrom sweep v = 0 := withdrawnFrom_eq_zero fun w member same => by
        obtain ⟨k, inside, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
        exact swept ⟨k, inside, same⟩
      rw [zero] at bounded ⊢
      by_cases positive : 0 < withdrawnFrom partials v
      · obtain ⟨floor, effective⟩ := partials_floor (partialsOk electra) found read positive
        have := UInt64.le_iff_toNat_le.mp effective
        omega
      · omega

/-- From Electra and before Gloas, the execution part of a block keeps the floor of the
withdrawals. -/
private theorem execution_floor {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {body : BeaconBlockBody preset f}
    {bellatrix : .bellatrix ≤ f} (early : f < .glamsterdam) (electra : .pectra ≤ f)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch) :
    ∃ (partials : Array Withdrawal) (next : WithdrawalIndex) (count : ℕ),
      getPendingPartialWithdrawals s electra
        (s.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
          .ok (partials, next, count) ∧
      min (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat ≤
        actualBalanceAt ⟨f, t⟩ v.toNat +
          min (withdrawnFrom partials v)
            (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt early
  have capella : .shapella ≤ f := Nat.le_trans (by decide) electra
  simp only [notGloas, capella, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
  obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
  obtain ⟨partials, next, count, partialsOk, floor⟩ :=
    withdrawals_floor early electra withdrawnOk found later
  exact ⟨partials, next, count, partialsOk, by simpa [actualBalanceAt] using floor⟩

/-! ## The sync aggregate of a block -/

/-- A member index that a key reads names the validator that holds that key. -/
private theorem validatorIndexOfPubkey_key {f : Fork} {s : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {member : ValidatorIndex}
    (computed : validatorIndexOfPubkey s key = .ok member) {index : Nat} {validator : Validator}
    (found : s.validators.data[index]? = some validator) (named : member.toNat = index) :
    validator.pubkey = key := by
  unfold validatorIndexOfPubkey at computed
  split at computed
  · rename_i position located
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at computed
    obtain ⟨there, keyed⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    rw [(Uint64.ofNatChecked_ok_iff.mp computed).2] at named
    subst named
    rw [Array.getElem?_eq_getElem there, Option.some.injEq] at found
    subst found
    exact beq_iff_eq.mp keyed.1
  · cases computed

/-- The members that the keys of a committee read name a validator at most once for each of its
keys. -/
private theorem members_count_le {f : Fork} {s : BeaconState preset f} {index : Nat}
    {validator : Validator} (found : s.validators.data[index]? = some validator) :
    ∀ {keys : List Cryptography.Bls.BLSPubkey} {members : List ValidatorIndex},
      keys.mapM (validatorIndexOfPubkey s) = .ok members →
      (members.filter (·.toNat = index)).length ≤
        (keys.filter fun key => validator.pubkey == key).length
  | [], members, computed => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | key :: keys, members, computed => by
    simp only [List.mapM_cons, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨member, memberOk, rest, restOk, rfl⟩ := computed
    have tail := members_count_le found restOk
    simp only [List.filter_cons]
    by_cases named : member.toNat = index
    · have keyed := validatorIndexOfPubkey_key memberOk found named
      subst keyed
      simp only [named, decide_true, ↓reduceIte, beq_self_eq_true, List.length_cons]
      omega
    · by_cases keyed : (validator.pubkey == key) = true <;> simp [named, keyed] <;> omega

/-- Applying the sync rewards and penalties lowers a balance by at most one reward per member
that names its position. -/
private theorem syncFold_floor {j : Nat} {reward proposerReward : Nat} {chosen : ValidatorIndex} :
    ∀ (members : List (ValidatorIndex × Bool)) (balance : Nat),
      balance ≤ members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then reward else 0) +
            (if chosen.toNat = j then proposerReward else 0)
          else if member.1.toNat = j then balance - reward else balance) balance +
        (members.filter (·.1.toNat = j)).length * reward
  | [], balance => by simp
  | member :: members, balance => by
    rw [List.foldl_cons, List.filter_cons]
    have rest := syncFold_floor (j := j) (reward := reward) (proposerReward := proposerReward)
      (chosen := chosen) members (if member.2 then
      balance + (if member.1.toNat = j then reward else 0) +
        (if chosen.toNat = j then proposerReward else 0)
      else if member.1.toNat = j then balance - reward else balance)
    by_cases named : member.1.toNat = j <;> by_cases signed : member.2 <;>
      simp only [named, signed, ↓reduceIte, decide_true, decide_false, List.length_cons,
        Bool.false_eq_true] at rest ⊢ <;>
      first
      | (rw [Nat.add_mul, Nat.one_mul]; omega)
      | omega

/-- The first parts of a zip are a sublist of the first list. -/
private theorem zip_fst_sublist {α β : Type} :
    ∀ (first : List α) (second : List β), ((first.zip second).map Prod.fst).Sublist first
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: first, _ :: second => by simpa using (zip_fst_sublist first second).cons_cons a

/-- From Altair, the sync aggregate lowers the balance of a validator by at most the participant
reward for each of its seats in the current committee. -/
private theorem syncAggregate_floor {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t)
    {index : Nat} {validator : Validator} (found : s.validators.data[index]? = some validator) :
    ∃ reward : Gwei, syncParticipantReward s = .ok reward ∧
      actualBalanceAt ⟨f, s⟩ index ≤ actualBalanceAt ⟨f, t⟩ index +
        ((s.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
          validator.pubkey == key).length * reward.toNat := by
  obtain ⟨reward, proposerReward, members, chosen, rewardOk, -, membersOk, -, balances⟩ :=
    processSyncAggregate_balance computed
  refine ⟨reward, rewardOk, ?_⟩
  cases atIndex : s.balances.data[index]? with
  | none => simp [actualBalanceAt, atIndex]
  | some earlier =>
    obtain ⟨final, atFinal, value⟩ := balances index earlier atIndex
    simp only [actualBalanceAt, atIndex, atFinal, Option.map_some, Option.getD_some, value]
    refine (syncFold_floor (j := index) (reward := reward.toNat)
      (proposerReward := proposerReward.toNat) (chosen := chosen)
      (members.zip aggregate.syncCommitteeBits.bits.toArray).toList earlier.toNat).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
    have onList : (s.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
        (validatorIndexOfPubkey s) = .ok members.toList := by
      rw [← Array.toList_mapM, membersOk]
      rfl
    have counted := members_count_le found onList
    have prefixed : ((members.zip aggregate.syncCommitteeBits.bits.toArray).toList.map
        Prod.fst).Sublist members.toList := by
      rw [Array.toList_zip]
      exact zip_fst_sublist _ _
    have sub := (prefixed.filter (·.toNat = index)).length_le
    rw [List.filter_map, List.length_map] at sub
    exact sub.trans counted

/-! ## The floor of a balance under a block -/

/-- The seats of the validator at a position in the current sync committee of a state. -/
private def seatsAt {f : Fork} (s : BeaconState preset f) (altair : .altair ≤ f) (i : ℕ) : ℕ :=
  ((s.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
    (s.validators.data[i]?).any (·.pubkey == key)).length

/-- The sync participant reward, as a formula of the effective balances active in the current
epoch. -/
private def seatRewardAt {f : Fork} (s : BeaconState preset f) : ℕ :=
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let total := max inc (∑ i ∈ (Finset.range s.validators.data.size).filter
    (fun i => isActiveAt s (getCurrentEpoch s) i = true),
      ((s.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
  total / inc * (inc * preset.BASE_REWARD_FACTOR.toNat /
    (integerSquareroot (UInt64.ofNat total)).toNat) * SYNC_REWARD_WEIGHT.toNat /
      WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat / preset.SYNC_COMMITTEE_SIZE.toNat

/-- A successful sync participant reward is the formula of the active effective balances. -/
private theorem syncReward_value {f : Fork} {s : BeaconState preset f} {reward : Gwei}
    (computed : syncParticipantReward s = .ok reward) : reward.toNat = seatRewardAt s := by
  obtain ⟨total, perIncrement, totalOk, -, perValue, rewardValue⟩ :=
    syncParticipantReward_ok computed
  have totalValue := getTotalActiveBalance_toNat totalOk
  rw [rewardValue, perValue]
  unfold seatRewardAt
  dsimp only
  rw [← totalValue, UInt64.ofNat_toNat, toNat_integerSquareroot, Nat.mul_comm
    (UInt64.toNat preset.EFFECTIVE_BALANCE_INCREMENT * preset.BASE_REWARD_FACTOR.toNat /
      (UInt64.toNat total).sqrt)]

/-- What the queued partial withdrawals of a block pay a validator, from Electra and before Gloas.

They are read from the state after the header, as the execution part reads them. -/
private def blockQueuePaid {f : Fork} (before : BeaconState preset f)
    (block : BeaconBlock preset f) (v : ValidatorIndex) : ℕ :=
  if electra : .pectra ≤ f then
    ((do
      let headed ← processBlockHeader before block
      let (partials, _) ← getPendingPartialWithdrawals headed electra
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[]
      pure (withdrawnFrom partials v) : Except TransitionError ℕ).toOption).getD 0
  else 0

/-- From Electra and before Gloas, take a validator that cannot withdraw in full and stays
unslashed, with its effective balance within its largest.

A block leaves it at least the smaller of its balance and its effective balance, less two amounts.

The first is its seats times the sync participant reward, read after the block.

The second is what the queued partial withdrawals pay it, up to its effective balance above the
activation balance. -/
private theorem block_floor {f : Fork}
    {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (early : f < .glamsterdam) (electra : .pectra ≤ f)
    (matched : BalancesMatch s) (computed : processBlock config checks engine s block = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch)
    (capped : val.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f val)
    (unslashed : ∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) :
    min (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat ≤
      actualBalanceAt ⟨f, t⟩ v.toNat +
        seatsAt t (Nat.le_trans (by decide) electra) v.toNat * seatRewardAt t +
        min (blockQueuePaid s block v)
          (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt early
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  have beforeHeze : f < .hegota := Nat.lt_trans early (by decide)
  obtain ⟨input, last, started, operatedOk, -, synced⟩ := processBlock_operationsInput computed
  have startedFrame := frame_operationsInput started
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at paidOk
  subst paidOk
  simp only [bellatrix, ↓reduceDIte] at executedOk
  simp only [beforeHeze, ↓reduceDIte] at votedOk
  simp only [altair, ↓reduceDIte] at synced
  -- The header keeps the registry, the balances and the slot.
  obtain ⟨_, _, headedEq⟩ := processBlockHeader_eq headedOk
  have headedFound : headed.validators.data[v.toNat]? = some val := by
    rw [headedEq]; exact found
  have headedLater : getCurrentEpoch headed < val.withdrawableEpoch := by
    rw [headedEq]; exact later
  have headedBalance :
      actualBalanceAt ⟨f, headed⟩ v.toNat = actualBalanceAt ⟨f, s⟩ v.toNat := by
    subst headedEq; rfl
  -- The execution part pays the withdrawals.
  obtain ⟨partials, next, count, partialsOk, executionFloor⟩ :=
    execution_floor early electra executedOk headedFound headedLater
  have queue : blockQueuePaid s block v = withdrawnFrom partials v := by
    unfold blockQueuePaid
    simp only [electra, ↓reduceDIte, headedOk, partialsOk, bind, Except.bind, pure,
      Except.pure, Except.toOption, Option.getD_some]
  -- The RANDAO reveal and the vote keep the registry and the balances.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, revealedEq⟩ := processRandao_eq revealedOk
  obtain ⟨-, -, votedEq⟩ := processEth1Data_eq votedOk
  have inputValidators : input.validators = executed.validators := by
    exact (congrArg BeaconState.validators votedEq).trans (by rw [revealedEq])
  have inputBalances : input.balances = executed.balances := by
    exact (congrArg BeaconState.balances votedEq).trans (by rw [revealedEq])
  have inputFound : input.validators.data[v.toNat]? = some val := by
    rw [inputValidators, processBlockExecution_validators executedOk]
    exact headedFound
  -- The operations keep the floor, and the sync aggregate takes at most the seats.
  have lastClear : ∀ w, last.validators.data[v.toNat]? = some w → w.slashed = false := by
    obtain ⟨_, syncedEq⟩ := processSyncAggregate_eq synced
    intro w read
    exact unslashed w (by rw [syncedEq]; exact read)
  have operationsFloor := processOperations_floor early (startedFrame.balancesMatch matched) operatedOk
    inputFound capped lastClear
  obtain ⟨w, lastFound, samePubkey⟩ := validators_getElem?_of_validatorKeys_prefix
    (frame_processOperations operatedOk).pubkeysPrefix inputFound
  obtain ⟨reward, rewardOk, syncFloor⟩ := syncAggregate_floor synced lastFound
  obtain ⟨_, syncedEq⟩ := processSyncAggregate_eq synced
  have seats : seatsAt t altair v.toNat =
      ((last.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        w.pubkey == key).length := by
    subst syncedEq
    simp only [seatsAt, lastFound, Option.any_some]
  have rewardValue : reward.toNat = seatRewardAt t := by
    rw [syncReward_value rewardOk, syncedEq]
    rfl
  rw [seats, ← rewardValue, queue]
  have inputBalance : actualBalanceAt ⟨f, input⟩ v.toNat =
      actualBalanceAt ⟨f, executed⟩ v.toNat := by
    simp only [actualBalanceAt, inputBalances]
  rw [inputBalance] at operationsFloor
  rw [headedBalance] at executionFloor
  have := Nat.min_le_right (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat
  have := Nat.min_le_left (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat
  omega

/-! ## The queue of pending partial withdrawals inside one epoch

Payments consume entries from the front of the queue.

Each consumed entry pays at most its amount, and only after its withdrawable epoch.

A withdrawal request appends an entry that is withdrawable only after the current epoch.

So the blocks of one epoch pay a validator at most the entries of the queue at its start that are
due by then.

Ported from the donor's PendingPartialsKept.lean and DirectSafety/PartialWithdrawalLedger.lean.
-/

/-- Two states hold the same queue of pending partial withdrawals, from Electra. -/
private def PartialsSame (state after : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork,
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra

private theorem PartialsSame.refl (state : BeaconState preset fork) : PartialsSame state state :=
  fun _ => rfl

private theorem PartialsSame.trans {first second third : BeaconState preset fork}
    (one : PartialsSame first second) (two : PartialsSame second third) :
    PartialsSame first third :=
  fun electra => (two electra).trans (one electra)

private theorem PartialsSame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → PartialsSame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : PartialsSame state after :=
  foldlM_ok_invariant (PartialsSame state)
    (fun _ _ _ before ok => before.trans (frame _ _ _ ok)) (PartialsSame.refl state) computed

/-- Setting a validator at a plain position keeps the queue. -/
private theorem partialsSame_setValidatorAt {position : Nat} {validator : Validator}
    (set : state.setValidatorAt position validator = .ok after) : PartialsSame state after := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact fun _ => rfl

/-- Setting a validator keeps the queue. -/
private theorem partialsSame_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : PartialsSame state after :=
  partialsSame_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

/-- Setting a balance keeps the queue. -/
private theorem partialsSame_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : PartialsSame state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact fun _ => rfl

/-- Raising a balance keeps the queue. -/
private theorem partialsSame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : PartialsSame state after :=
  let ⟨_, set⟩ := increaseBalance_ok computed
  partialsSame_setBalance set

/-- Lowering a balance keeps the queue. -/
private theorem partialsSame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : PartialsSame state after :=
  let ⟨_, set⟩ := decreaseBalance_ok computed
  partialsSame_setBalance set

/-- Starting the exit of a validator keeps the queue. -/
private theorem partialsSame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    PartialsSame state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact PartialsSame.refl _
  refine PartialsSame.trans ?_ (partialsSame_setValidator set)
  unfold exitQueue at queue
  split at queue
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := queue
    exact fun _ => rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, rfl, _⟩ := queue
    exact PartialsSame.refl _

/-- Adding a validator keeps the queue. -/
private theorem partialsSame_addValidatorToRegistry {pubkey withdrawalCredentials amount}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    PartialsSame state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact fun _ => rfl
  split at computed
  · cases computed
    exact fun _ => rfl
  · cases computed


private theorem getPendingPartialWithdrawals_loop_ledger {fork : Fork}
    {state : BeaconState preset fork} {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    ∃ (count : ℕ) (pay : ℕ → ℕ), result.2.2 = processed + count ∧ count ≤ queue.length ∧
      (∀ k, count ≤ k → pay k = 0) ∧
      (∀ k < count, ∃ w, queue[k]? = some w ∧ pay k ≤ w.amount.toNat ∧
        (0 < pay k → w.withdrawableEpoch ≤ epoch)) ∧
      ∀ v, ((result.1.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum =
        ((withdrawals.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum +
          ∑ k ∈ Finset.range count,
            if queue[k]?.map (·.validatorIndex) = some v then pay k else 0
  | [], _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨0, fun _ => 0, rfl, Nat.zero_le _, fun _ _ => rfl,
      fun _ small => absurd small (by omega), fun _ => by simp⟩
  | pending :: rest, withdrawals, next, processed, _, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨0, fun _ => 0, rfl, Nat.zero_le _, fun _ _ => rfl,
        fun _ small => absurd small (by omega), fun _ => by simp⟩
    rename_i ready
    have due : pending.withdrawableEpoch ≤ epoch := by
      simp only [not_or, Nat.not_le] at ready
      exact UInt64.not_lt.mp ready.1
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, left, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, loopOk⟩ := computed
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      obtain ⟨count, pay, counted, bounded, beyond, entries, sums⟩ :=
        getPendingPartialWithdrawals_loop_ledger rest _ _ _ loopOk
      refine ⟨count + 1, fun k => k.casesOn
        (min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount).toNat pay,
        by omega, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro k large
        cases k with
        | zero => omega
        | succ k => exact beyond k (by omega)
      · intro k small
        cases k with
        | zero => exact ⟨pending, rfl, UInt64.le_iff_toNat_le.mp Std.min_le_right, fun _ => due⟩
        | succ k => exact entries k (by omega)
      · intro v
        rw [sums v, Finset.sum_range_succ']
        by_cases named : pending.validatorIndex = v
        · simp [named, Array.toList_push, List.filter_append]
          omega
        · simp [named, Array.toList_push, List.filter_append]
    · obtain ⟨count, pay, counted, bounded, beyond, entries, sums⟩ :=
        getPendingPartialWithdrawals_loop_ledger rest _ _ _ computed
      refine ⟨count + 1, fun k => k.casesOn 0 pay, by omega,
        by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro k large
        cases k with
        | zero => rfl
        | succ k => exact beyond k (by omega)
      · intro k small
        cases k with
        | zero => exact ⟨pending, rfl, Nat.zero_le _, fun positive => absurd positive (by simp)⟩
        | succ k => exact entries k (by omega)
      · intro v
        rw [sums v, Finset.sum_range_succ']
        simp

private theorem getPendingPartialWithdrawals_ledger {fork : Fork}
    {state : BeaconState preset fork} {electra : .pectra ≤ fork} {start : WithdrawalIndex}
    {prior partials : Array Withdrawal} {next : WithdrawalIndex} {count : ℕ}
    (computed : getPendingPartialWithdrawals state electra start prior =
      .ok (partials, next, count)) :
    ∃ pay : ℕ → ℕ, count ≤ (state.pendingPartialWithdrawals electra).data.toList.length ∧
      (∀ k, count ≤ k → pay k = 0) ∧
      (∀ k < count, ∃ w, (state.pendingPartialWithdrawals electra).data.toList[k]? = some w ∧
        pay k ≤ w.amount.toNat ∧ (0 < pay k → w.withdrawableEpoch ≤ getCurrentEpoch state)) ∧
      ∀ v, ((partials.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum =
        ∑ k ∈ (Finset.range count).filter (fun k =>
          (state.pendingPartialWithdrawals electra).data.toList[k]?.map (·.validatorIndex) =
            some v), pay k := by
  unfold getPendingPartialWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, loopOk⟩ := computed
  obtain ⟨found, pay, counted, bounded, beyond, entries, sums⟩ :=
    getPendingPartialWithdrawals_loop_ledger _ _ _ _ loopOk
  simp only [Nat.zero_add] at counted
  subst counted
  refine ⟨pay, bounded, beyond, entries, fun v => ?_⟩
  rw [sums v, Finset.sum_filter]
  simp

private theorem withdrawals_pendingPartials {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) :
    ∃ (partials : Array Withdrawal) (next : WithdrawalIndex) (count : ℕ),
      getPendingPartialWithdrawals s electra (s.nextWithdrawalIndex capella) #[] =
        .ok (partials, next, count) ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop count := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, expectedOk, _, _, applied⟩ := ok
  unfold getExpectedWithdrawals at expectedOk
  simp only [notGloas, electra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at expectedOk
  obtain ⟨_, rfl, ⟨partials, next, count⟩, partialsOk, _, rfl, _, _, rfl⟩ := expectedOk
  refine ⟨partials, next, count, partialsOk, ?_⟩
  simp only [applyExpectedWithdrawals, notGloas, electra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  have paidQueue :
      withdrawn.pendingPartialWithdrawals electra = s.pendingPartialWithdrawals electra := by
    unfold applyWithdrawals at paid
    rw [← Array.foldlM_toList] at paid
    refine foldlM_ok_invariant
      (fun t => t.pendingPartialWithdrawals electra = s.pendingPartialWithdrawals electra)
      ?_ rfl paid
    intro a withdrawal b kept stepped
    simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
    exact (partialsSame_decreaseBalance stepped electra).trans kept
  have movedQueue :
      indexed.pendingPartialWithdrawals electra = withdrawn.pendingPartialWithdrawals electra := by
    unfold updateNextWithdrawalIndex at moved
    split at moved
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at moved
      obtain ⟨_, _, rfl⟩ := moved
      rfl
    · cases moved; rfl
  simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at swept
  obtain ⟨_, _, swept⟩ := swept
  split at swept
  · cases swept
  · cases swept
    simp only [updatePendingPartialWithdrawals, Array.toList_extract, List.extract_eq_take_drop,
      movedQueue, paidQueue]
    exact List.take_of_length_le (by simp)

private def QueueAppend {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork, ∃ added : List PendingPartialWithdrawal,
    (t.pendingPartialWithdrawals electra).data.toList =
      (s.pendingPartialWithdrawals electra).data.toList ++ added ∧
    ∀ w ∈ added, getCurrentEpoch s < w.withdrawableEpoch

private theorem QueueAppend.of_same {fork : Fork} {s t : BeaconState preset fork}
    (same : PartialsSame s t) : QueueAppend s t := fun electra =>
  ⟨[], by rw [same electra, List.append_nil], by simp⟩

private theorem QueueAppend.trans {fork : Fork} {s t u : BeaconState preset fork}
    (one : QueueAppend s t) (two : QueueAppend t u)
    (epoch : getCurrentEpoch s ≤ getCurrentEpoch t) :
    QueueAppend s u := by
  intro electra
  obtain ⟨a, first, lateA⟩ := one electra
  obtain ⟨b, second, lateB⟩ := two electra
  refine ⟨a ++ b, by rw [second, first, List.append_assoc], ?_⟩
  intro w member
  rcases List.mem_append.mp member with member | member
  · exact lateA w member
  · exact UInt64.lt_of_le_of_lt epoch (lateB w member)

private theorem QueueAppend.foldlM {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (appends : ∀ s a t, step s a = .ok t → QueueAppend s t)
    (slots : ∀ s a t, step s a = .ok t → t.slot = s.slot)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM step s = .ok t) : QueueAppend s t := by
  have both := foldlM_ok_invariant
    (fun t => QueueAppend s t ∧ t.slot = s.slot)
    (fun a item b prior ok =>
      ⟨prior.1.trans (appends a item b ok) (by
          simp only [getCurrentEpoch, prior.2]; exact UInt64.le_refl _),
        (slots a item b ok).trans prior.2⟩)
    ⟨.of_same (PartialsSame.refl s), rfl⟩ ok
  exact both.1

private theorem partialWithdrawal_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    QueueAppend s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨balance, _, kept, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨queued, epoch⟩, called, withdrawable, delayed, pending, appended, rfl⟩ := ok
    have queue : queued.pendingPartialWithdrawals electra =
        s.pendingPartialWithdrawals electra := by
      unfold computeExitEpochAndUpdateChurn at called
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at called
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := called
      rfl
    have late : getCurrentEpoch s < withdrawable := by
      obtain ⟨first, firstOk⟩ : ∃ first,
          computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first := by
        unfold computeExitEpochAndUpdateChurn at called
        simp only [bind_ok_iff] at called
        obtain ⟨first, firstOk, _⟩ := called
        exact ⟨first, by simpa only [liftArith, mapError_ok_iff] using firstOk⟩
      have placed := UInt64.le_iff_toNat_le.mp
        (computeExitEpochAndUpdateChurn_first firstOk called).1
      have starts := (computeActivationExitEpoch_ok_iff.mp firstOk).2
      have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp delayed)).2
      dsimp only at sum
      simp only [UInt64.lt_iff_toNat_lt]
      omega
    intro electra'
    refine ⟨[⟨index, min (balance - kept) amount, withdrawable⟩], ?_, ?_⟩
    · simp only [appendWithinLimit_data appended, Array.toList_push, queue]
    · intro w member
      obtain rfl := List.mem_singleton.mp member
      exact late
  · cases ok
    exact .of_same (PartialsSame.refl s)

private theorem withdrawalRequest_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : QueueAppend s t := by
  rcases withdrawalRequest_cases ok with same | ⟨index, exited⟩ | ⟨index, v, owed, withdrawn⟩
  · subst t
    exact .of_same (PartialsSame.refl s)
  · exact .of_same (partialsSame_initiateValidatorExit exited)
  · exact partialWithdrawal_queueAppend withdrawn

private theorem slashValidator_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) : PartialsSame s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, exitedOk, _, _, markedOk, _, _, _,
    lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  simp only [show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early, ↓reduceDIte] at done
  subst done
  intro electra
  rw [partialsSame_increaseBalance final electra, partialsSame_increaseBalance raised electra,
    partialsSame_decreaseBalance lowered electra,
    ← partialsSame_initiateValidatorExit exitedOk electra]
  obtain ⟨_, rfl⟩ := setValidator_ok markedOk
  rfl

private theorem proposerSlashing_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : PartialsSame s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator_partialsSame early slashed

private theorem attesterSlashing_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : PartialsSame s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, flag⟩, foldedOk, ok⟩ := ok
  simp only [pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => PartialsSame s step.1) ?_
    (PartialsSame.refl s) foldedOk
  intro ⟨state, _⟩ index next kept stepped
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at stepped
  obtain ⟨_, _, stepped⟩ := stepped
  split at stepped
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at stepped
    obtain ⟨_, slashed, rfl⟩ := stepped
    exact kept.trans (slashValidator_partialsSame early slashed)
  · cases stepped; exact kept

private theorem attestation_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    PartialsSame s t := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processAttestation, altair, ↓reduceDIte] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok, notGloas, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, raised, rfl⟩ := ok
  intro electra
  rw [partialsSame_increaseBalance raised electra]
  unfold setEpochParticipation
  split <;> rfl

private theorem deposit_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : PartialsSame s t := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  simp only [applyDeposit, electra, ↓reduceDIte] at credited
  unfold applyDepositElectra at credited
  split at credited
  · simp only [bind_ok_iff] at credited
    obtain ⟨_, _, credited⟩ := credited
    split at credited
    · simp only [bind_ok_iff, liftAccessor_ok] at credited
      obtain ⟨_, added, queued⟩ := credited
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
      intro e
      exact partialsSame_addValidatorToRegistry added e
    · cases credited; exact PartialsSame.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp credited)
    exact PartialsSame.refl _

private theorem credentials_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : PartialsSame s t := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact partialsSame_setValidator set

private theorem consolidationRequest_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : PartialsSame s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact PartialsSame.refl _)
    | cases ok
    | (intro e; simp only [switchToCompoundingValidator, queueExcessActiveBalance, bind_ok_iff,
        liftAccessor_ok] at ok
       obtain ⟨_, _, _, set, _, _, queued⟩ := ok
       obtain ⟨_, rfl⟩ := setValidator_ok set
       split at queued
       · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
         obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
         exact partialsSame_setBalance set e
       · cases queued; rfl)
    | (intro e
       simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
         Except.ok.injEq] at ok
       obtain ⟨⟨_, _⟩, scheduled, _, _, _, set, _, _, rfl⟩ := ok
       obtain ⟨_, rfl⟩ := setValidator_ok set
       simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
         Except.ok.injEq, Prod.mk.injEq] at scheduled
       obtain ⟨_, _, _, _, ⟨_, _⟩, _, rfl, _⟩ := scheduled
       rfl)

private theorem executionRequests_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionRequests config s body electra = .ok t) : QueueAppend s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  have first : PartialsSame s deposited := by
    refine PartialsSame.foldlM (fun a request b called => ?_) deposits
    obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp called)
    intro e
    unfold recordDepositRequestsStart
    split <;> (try split) <;> rfl
  have second := QueueAppend.foldlM
    (fun _ _ _ called => withdrawalRequest_queueAppend called)
    (fun _ _ _ called => (frame_processWithdrawalRequest called).slot) withdrawals
  have third := PartialsSame.foldlM
    (fun _ _ _ called => consolidationRequest_partialsSame called) consolidations
  have slot := (BlockFrame.foldlM
    (fun _ _ _ called => frame_processDepositRequest called) deposits).slot
  have withdrawnSlot := (BlockFrame.foldlM
    (fun _ _ _ called => frame_processWithdrawalRequest called) withdrawals).slot
  exact ((QueueAppend.of_same first).trans second (by
    simp only [getCurrentEpoch, slot]; exact UInt64.le_refl _)).trans
    (.of_same third) (by
      simp only [getCurrentEpoch, withdrawnSlot, slot]; exact UInt64.le_refl _)

private theorem operations_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks s body parentSlot = .ok t) : QueueAppend s t := by
  let step := fun a b : BeaconState preset fork => QueueAppend a b ∧ b.slot = a.slot
  have same {a b : BeaconState preset fork} (kept : PartialsSame a b) (slot : b.slot = a.slot) :
      step a b := ⟨.of_same kept, slot⟩
  have chain {a b c : BeaconState preset fork} (one : step a b) (two : step b c) :
      step a c := ⟨one.1.trans two.1 (by
        simp only [getCurrentEpoch, one.2]; exact UInt64.le_refl _), two.2.trans one.2⟩
  obtain ⟨proposed, slashed, attested, proposers, slashings, attestations, rest⟩ :=
    processOperations_folds_of step (fun a => same (.refl a) rfl) chain
      (fun called => same (deposit_partialsSame electra called) (frame_processDeposit called).slot)
      (fun called => same (partialsSame_initiateValidatorExit
        (processVoluntaryExit_initiates called)) (frame_processVoluntaryExit called).slot)
      (fun called => same (credentials_partialsSame called)
        (frame_processBlsToExecutionChange called).slot)
      (fun called => ⟨executionRequests_queueAppend called,
        (frame_processExecutionRequests called).slot⟩)
      (fun {a b} gloas _ => False.elim ((Nat.not_le_of_lt early) gloas)) ok
  have first := PartialsSame.foldlM
    (fun _ _ _ called => proposerSlashing_partialsSame early called) proposers
  have second := PartialsSame.foldlM
    (fun _ _ _ called => attesterSlashing_partialsSame early called) slashings
  have third := PartialsSame.foldlM
    (fun _ _ _ called => attestation_partialsSame electra early called) attestations
  exact (chain (same (first.trans (second.trans third))
    (((Frame.foldlM (fun _ _ _ called => frame_processAttestation called) attestations).slot).trans
      (((BlockFrame.foldlM (fun _ _ _ called => frame_processAttesterSlashing called)
        slashings).slot).trans
        (BlockFrame.foldlM (fun _ _ _ called => frame_processProposerSlashing called)
          proposers).slot))) rest).1

private theorem block_partialLedger {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ (headed : BeaconState preset fork) (partials : Array Withdrawal) (next : WithdrawalIndex)
      (count : ℕ) (new : List PendingPartialWithdrawal),
      processBlockHeader s block = .ok headed ∧
      getPendingPartialWithdrawals headed electra
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
          .ok (partials, next, count) ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop count ++ new ∧
      ∀ w ∈ new, getCurrentEpoch s < w.withdrawableEpoch := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  obtain ⟨voted, operated, started, operatedOk, -, synced⟩ := processBlock_operationsInput ok
  have slot := (frame_operationsInput started).slot
  obtain ⟨parented, headed, executed, revealed, paid, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [notGloas, bellatrix, before, altair, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at paid executedOk votedOk synced
  subst paid
  obtain ⟨partials, next, count, partialsOk, executedQueue⟩ :
      ∃ (partials : Array Withdrawal) (next : WithdrawalIndex) (count : ℕ),
        getPendingPartialWithdrawals headed electra (headed.nextWithdrawalIndex capella) #[] =
          .ok (partials, next, count) ∧
        (executed.pendingPartialWithdrawals electra).data.toList =
          (headed.pendingPartialWithdrawals electra).data.toList.drop count := by
    simp only [processBlockExecution, notGloas, capella, ↓reduceDIte, bind_ok_iff] at executedOk
    obtain ⟨withdrawn, withdrawnOk, payload⟩ := executedOk
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
    simpa only using withdrawals_pendingPartials electra early withdrawnOk
  have voteQueue := congrArg (fun state => state.pendingPartialWithdrawals electra)
    (processEth1Data_eq votedOk).2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
  have headQueue : (voted.pendingPartialWithdrawals electra).data.toList =
      (s.pendingPartialWithdrawals electra).data.toList.drop count := by
    rw [voteQueue]
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact executedQueue
  obtain ⟨new, queue, late⟩ := operations_queueAppend electra early operatedOk electra
  obtain ⟨_, syncedEq⟩ := processSyncAggregate_eq synced
  refine ⟨headed, partials, next, count, new, headedOk, partialsOk, ?_, ?_⟩
  · rw [syncedEq]
    exact queue.trans (congrArg (· ++ new) headQueue)
  · simpa only [getCurrentEpoch, slot] using late

private theorem sum_filter_map_eq_sum_range {α : Type} (p : α → Bool) (f : α → ℕ) :
    ∀ l : List α, ((l.filter p).map f).sum =
      ∑ j ∈ Finset.range l.length, ((l[j]?.filter p).map f).getD 0
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      ← sum_filter_map_eq_sum_range p f l]
    cases passes : p a
    · simp [passes, Option.filter_some]
    · simp [passes, Option.filter_some]
      omega


/-- What the queued partial withdrawals of one step pay a validator. -/
private def stepQueuePaid {x y : ForkedBeaconState preset} :
    Step config checks x y → ValidatorIndex → ℕ
  | .block (before := before) _ signed _ _, v => blockQueuePaid before signed.message v
  | .slot _, _ => 0

/-- What the queued partial withdrawals of a run pay a validator. -/
private def runQueuePaid {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ValidatorIndex → ℕ
  | _, .nil, _ => 0
  | _, .snoc pre step, v => runQueuePaid pre v + stepQueuePaid step v

/-- A run without blocks pays nothing from the queue. -/
private theorem runQueuePaid_eq_zero {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (none : run.blockCount = 0) (v : ValidatorIndex) :
    runQueuePaid run v = 0 := by
  induction run with
  | nil => rfl
  | snoc pre step ih =>
    cases step with
    | slot ok =>
      simp only [Run.blockCount] at none
      simp [runQueuePaid, ih none, stepQueuePaid]
    | block engine signed due ok => simp [Run.blockCount] at none

/-- Inside one epoch from Electra and before Gloas, the queue of a run's last state is the queue
of its first state, with entries appended that are not yet withdrawable, less a prefix.

The run pays each validator from the consumed prefix, at most the amount of each entry, and only
from entries withdrawable by the epoch. -/
private theorem run_partialLedger {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state) (electra : .pectra ≤ x.fork) :
    ∀ electra' : .pectra ≤ y.fork,
    ∃ (appended : List PendingPartialWithdrawal) (consumed : ℕ) (paid : ℕ → ℕ),
      let ledger := (x.state.pendingPartialWithdrawals electra).data.toList ++ appended
      consumed ≤ ledger.length ∧
      (y.state.pendingPartialWithdrawals electra').data.toList = ledger.drop consumed ∧
      (∀ a ∈ appended, getCurrentEpoch x.state < a.withdrawableEpoch) ∧
      (∀ j, consumed ≤ j → paid j = 0) ∧
      (∀ j < consumed, ∃ w, ledger[j]? = some w ∧ paid j ≤ w.amount.toNat ∧
        (0 < paid j → w.withdrawableEpoch ≤ getCurrentEpoch x.state)) ∧
      ∀ v, runQueuePaid tail v = ∑ j ∈ (Finset.range consumed).filter
        (fun j => ledger[j]?.map (·.validatorIndex) = some v), paid j := by
  refine Run.induction_of_same_epoch
    (motive := fun w r => getCurrentEpoch w.state = getCurrentEpoch x.state →
      ∀ electra' : .pectra ≤ w.fork,
      ∃ (appended : List PendingPartialWithdrawal) (consumed : ℕ) (paid : ℕ → ℕ),
        let ledger := (x.state.pendingPartialWithdrawals electra).data.toList ++ appended
        consumed ≤ ledger.length ∧
        (w.state.pendingPartialWithdrawals electra').data.toList = ledger.drop consumed ∧
        (∀ a ∈ appended, getCurrentEpoch x.state < a.withdrawableEpoch) ∧
        (∀ j, consumed ≤ j → paid j = 0) ∧
        (∀ j < consumed, ∃ w, ledger[j]? = some w ∧ paid j ≤ w.amount.toNat ∧
          (0 < paid j → w.withdrawableEpoch ≤ getCurrentEpoch x.state)) ∧
        ∀ v, runQueuePaid r v = ∑ j ∈ (Finset.range consumed).filter
          (fun j => ledger[j]?.map (·.validatorIndex) = some v), paid j)
    ?_ ?_ ?_ tail early same same
  · intro _ _
    refine ⟨[], 0, fun _ => 0, ?_⟩
    simp [runQueuePaid]
  · intro f s t engine signed due ok pre fEarly ih epochT electraT
    have processed := (applySignedBlock_ok ok).2.1
    have epochS : getCurrentEpoch s = getCurrentEpoch x.state := by
      rw [← epochT]
      simp only [getCurrentEpoch, processBlock_slot processed]
    obtain ⟨appended, consumed, paid, bounded, queue, charged, beyond, entries, sums⟩ :=
      ih epochS electraT
    obtain ⟨headed, partials, next, count, new, headedOk, partialsOk, stepQueue, late⟩ :=
      block_partialLedger electraT fEarly processed
    obtain ⟨pay, counted, stepBeyond, stepEntries, stepSums⟩ :=
      getPendingPartialWithdrawals_ledger partialsOk
    have paidBlock : ∀ v, stepQueuePaid (Step.block engine signed due ok) v =
        ((partials.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum := by
      intro v
      simp only [stepQueuePaid, blockQueuePaid, electraT, ↓reduceDIte, headedOk, partialsOk,
        bind, Except.bind, pure, Except.pure, Except.toOption, Option.getD_some]
      rfl
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    simp only at stepEntries stepSums counted
    generalize ledgerDef : (x.state.pendingPartialWithdrawals electra).data.toList ++
      appended = ledger at bounded queue entries sums
    have middleLength : (s.pendingPartialWithdrawals electraT).data.toList.length =
        ledger.length - consumed := by rw [queue, List.length_drop]
    have within : consumed + count ≤ ledger.length := by omega
    refine ⟨appended ++ new, consumed + count,
      fun j => if j < consumed then paid j else pay (j - consumed), ?_⟩
    have extended : (x.state.pendingPartialWithdrawals electra).data.toList ++
        (appended ++ new) = ledger ++ new := by
      rw [← ledgerDef, List.append_assoc]
    have prefixAt : ∀ j < ledger.length, (ledger ++ new)[j]? = ledger[j]? :=
      fun j small => List.getElem?_append_left small
    intro ledger'
    simp only [ledger', extended]
    refine ⟨by simp only [List.length_append]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [stepQueue, queue, List.drop_drop, List.drop_append_of_le_length within]
    · intro a member
      rcases List.mem_append.mp member with member | member
      · exact charged a member
      · exact epochS ▸ late a member
    · intro j large
      have notOld : ¬ j < consumed := by omega
      simp only [notOld, ↓reduceIte]
      exact stepBeyond _ (by omega)
    · intro j small
      by_cases old : j < consumed
      · obtain ⟨w, found, bound, due⟩ := entries j old
        refine ⟨w, (prefixAt j (by omega)).trans found, by simpa [old] using bound, ?_⟩
        intro positive
        simp only [old, ↓reduceIte] at positive
        exact due positive
      · obtain ⟨w, found, bound, due⟩ := stepEntries (j - consumed) (by omega)
        refine ⟨w, ?_, by simpa [old] using bound, ?_⟩
        · rw [prefixAt j (by omega), ← found, queue, List.getElem?_drop]
          congr 1
          omega
        · intro positive
          simp only [old, ↓reduceIte] at positive
          have := due positive
          simp only [getCurrentEpoch] at this epochS ⊢
          rw [← epochS]
          exact this
    · intro v
      simp only [runQueuePaid, sums v, paidBlock v, stepSums v, Finset.sum_filter,
        Finset.sum_range_add]
      congr 1
      · refine Finset.sum_congr rfl fun j member => ?_
        have small := Finset.mem_range.mp member
        simp [small, prefixAt j (by omega)]
      · refine Finset.sum_congr rfl fun k member => ?_
        have small := Finset.mem_range.mp member
        rw [prefixAt (consumed + k) (by omega), queue, List.getElem?_drop]
        simp
  · intro middle last cached next pre ok lastEq cachedOk epochNext ih epochLast electraLast
    subst lastEq
    have epochMiddle : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      epochNext.symm.trans epochLast
    obtain ⟨appended, consumed, paid, bounded, queue, charged, beyond, entries, sums⟩ :=
      ih epochMiddle electraLast
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    refine ⟨appended, consumed, paid, bounded, ?_, charged, beyond, entries, fun v => ?_⟩
    · rw [← queue, cachedEq]
    · simp only [runQueuePaid, stepQueuePaid, Nat.add_zero]
      exact sums v

/-- Inside one epoch from Electra and before Gloas, a run pays a validator from the queue at most
the entries of its first queue that are withdrawable by the epoch. -/
private theorem runQueuePaid_le {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state) (electra : .pectra ≤ x.fork)
    (electra' : .pectra ≤ y.fork) (v : ValidatorIndex) :
    runQueuePaid tail v ≤
      (((x.state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = v.toNat ∧ w.withdrawableEpoch ≤ getCurrentEpoch x.state).map
          (·.amount.toNat)).sum := by
  obtain ⟨appended, consumed, paid, -, -, charged, -, entries, sums⟩ :=
    run_partialLedger tail early same electra electra'
  generalize getCurrentEpoch x.state = epoch at *
  generalize queueDef : (x.state.pendingPartialWithdrawals electra).data.toList = queue at *
  let due (j : ℕ) := ((queue[j]?.filter fun w =>
    w.validatorIndex.toNat = v.toNat ∧ w.withdrawableEpoch ≤ epoch).map (·.amount.toNat)).getD 0
  have bound : ∀ j ∈ Finset.range consumed,
      (if (queue ++ appended)[j]?.map (·.validatorIndex) = some v then paid j else 0) ≤
        if j < queue.length then due j else 0 := by
    intro j member
    obtain ⟨w, found, cap, paidDue⟩ := entries j (Finset.mem_range.mp member)
    by_cases positive : 0 < paid j
    swap
    · have zero : paid j = 0 := by omega
      simp [zero]
    have withdrawable := paidDue positive
    by_cases old : j < queue.length
    · have read : queue[j]? = some w := by rwa [List.getElem?_append_left old] at found
      simp only [found, read, Option.map_some, Option.some.injEq, old, ↓reduceIte, due,
        Option.filter_some]
      by_cases named : w.validatorIndex = v
      · simp [named, withdrawable, cap]
      · simp [named]
    · exfalso
      rw [List.getElem?_append_right (by omega)] at found
      have late := charged w (List.mem_of_getElem? found)
      exact absurd withdrawable (UInt64.not_le.mpr late)
  rw [sums v, Finset.sum_filter, sum_filter_map_eq_sum_range]
  calc _ ≤ ∑ j ∈ Finset.range consumed, if j < queue.length then due j else 0 :=
      Finset.sum_le_sum bound
    _ ≤ ∑ j ∈ Finset.range queue.length, due j := by
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro j member; exact Finset.mem_range.mpr (Finset.mem_filter.mp member).2)
        (by intros; exact Nat.zero_le _)

/-- From Electra, one block pays at most the partial withdrawals that one sweep may process. -/
private theorem partials_size_le {f : Fork} {s : BeaconState preset f} {electra : .pectra ≤ f}
    {start : WithdrawalIndex} {partials : Array Withdrawal} {next : WithdrawalIndex} {count : ℕ}
    (computed : getPendingPartialWithdrawals s electra start #[] = .ok (partials, next, count)) :
    partials.size ≤ preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat := by
  unfold getPendingPartialWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨room, roomOk, _, fits, loopOk⟩ := computed
  have run := (getPendingPartialWithdrawals_loop_run _ _ _ _ (loopRun_start fits) loopOk).1
  simp only [Array.size_empty, zero_add] at run
  exact run.trans (Nat.min_le_left _ _)

/-- The queued partial withdrawals of one block pay at most the validators that one sweep may pay.
-/
private theorem blockQueuePaid_support {fork : Fork} (before : BeaconState preset fork)
    (block : BeaconBlock preset fork) :
    ∃ indices : Finset ValidatorIndex,
      indices.card ≤ preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat ∧
      ∀ v, blockQueuePaid before block v ≠ 0 → v ∈ indices := by
  by_cases electra : .pectra ≤ fork
  · cases headedOk : processBlockHeader before block with
    | error =>
      exact ⟨∅, by simp, fun v paid => by
        simp [blockQueuePaid, electra, headedOk, bind, Except.bind, Except.toOption] at paid⟩
    | ok headed =>
      cases partialsOk : getPendingPartialWithdrawals headed electra
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] with
      | error =>
        exact ⟨∅, by simp, fun v paid => by
          simp [blockQueuePaid, electra, headedOk, partialsOk, bind, Except.bind,
            Except.toOption] at paid⟩
      | ok result =>
        obtain ⟨partials, next, count⟩ := result
        refine ⟨(partials.toList.map (·.validatorIndex)).toFinset, ?_, fun v paid => ?_⟩
        · refine (List.toFinset_card_le _).trans ?_
          simp only [List.length_map, Array.length_toList]
          exact partials_size_le partialsOk
        · simp only [blockQueuePaid, electra, dite_true, headedOk, partialsOk, bind,
            Except.bind, pure, Except.pure, Except.toOption, Option.getD_some,
            withdrawnFrom] at paid
          obtain ⟨amount, inside, positive⟩ := List.exists_mem_ne_zero_of_sum_ne_zero paid
          obtain ⟨w, kept, rfl⟩ := List.mem_map.mp inside
          obtain ⟨present, named⟩ := List.mem_filter.mp kept
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨w, present, by simpa using named⟩)
  · exact ⟨∅, by simp, fun v paid => by simp [blockQueuePaid, electra] at paid⟩

/-- A run with at most one block pays from the queue at most the validators that one sweep may
pay. -/
private theorem owed_card {x y : ForkedBeaconState preset} (run : Run config checks x y)
    (single : run.blockCount ≤ 1) :
    ∃ owed : Finset ValidatorIndex,
      owed.card ≤ preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat ∧
      ∀ v, runQueuePaid run v ≠ 0 → v ∈ owed := by
  induction run with
  | nil => exact ⟨∅, by simp, fun v paid => by simp [runQueuePaid] at paid⟩
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨owed, card, covers⟩ := ih (by simpa [Run.blockCount] using single)
      exact ⟨owed, card, fun v paid => covers v (by
        simpa [runQueuePaid, stepQueuePaid] using paid)⟩
    | @block f before after engine signed due ok =>
      have none : pre.blockCount = 0 := by simp [Run.blockCount] at single; omega
      obtain ⟨indices, card, covers⟩ := blockQueuePaid_support before signed.message
      refine ⟨indices, card, fun v paid => covers v ?_⟩
      simpa [runQueuePaid, runQueuePaid_eq_zero pre none v, stepQueuePaid] using paid

/-! ## The floor of a balance over the blocks of one epoch -/

/-- A validator unslashed at the end of a step was unslashed before it. -/
private theorem unslashed_before {x y : ForkedBeaconState preset}
    (persists : SlashedPersistence x.state y.state) {i : ℕ}
    (clear : ∀ w, y.state.validators.data[i]? = some w → w.slashed = false) :
    ∀ w, x.state.validators.data[i]? = some w → w.slashed = false := by
  intro w read
  cases flag : w.slashed
  · rfl
  · obtain ⟨w', read', marked⟩ := persists i w read flag
    rw [clear w' read'] at marked
    cases marked

/-- Take a run inside one epoch before Gloas.

Each of its blocks keeps the floor of a validator with a sync amount `S`.

Then the balance falls below the smaller of its start and a reference by at most a sum.

The sum adds those sync amounts and the queued payments.

With one block, the queued payments count only up to the reference above the activation balance.
-/
private theorem run_floor {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    {v : ValidatorIndex} {EB S : ℕ}
    (unslashed : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false)
    (step : ∀ {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
      {signed : SignedBeaconBlock preset f},
      applySignedBlock config checks engine s signed true = .ok t →
      Run config checks x ⟨f, s⟩ → Run config checks x ⟨f, t⟩ → f < .glamsterdam →
      getCurrentEpoch s = getCurrentEpoch x.state →
      (∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) →
      min (actualBalanceAt ⟨f, s⟩ v.toNat) EB ≤ actualBalanceAt ⟨f, t⟩ v.toNat + S +
        min (blockQueuePaid s signed.message v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat)) :
    ∃ extra : ℕ, min (actualBalanceAt x v.toNat) EB ≤
        actualBalanceAt y v.toNat + tail.blockCount * S + extra ∧
      extra ≤ runQueuePaid tail v ∧
      (tail.blockCount ≤ 1 →
        extra ≤ min (runQueuePaid tail v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat)) := by
  refine Run.induction_of_same_epoch
    (motive := fun w r => getCurrentEpoch w.state = getCurrentEpoch x.state →
      (∀ u, w.state.validators.data[v.toNat]? = some u → u.slashed = false) →
      ∃ extra : ℕ, min (actualBalanceAt x v.toNat) EB ≤
          actualBalanceAt w v.toNat + r.blockCount * S + extra ∧
        extra ≤ runQueuePaid r v ∧
        (r.blockCount ≤ 1 →
          extra ≤ min (runQueuePaid r v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat)))
    ?_ ?_ ?_ tail early same same unslashed
  · intro _ _
    exact ⟨0, by simp [Run.blockCount], Nat.zero_le _, fun _ => Nat.zero_le _⟩
  · intro f s t engine signed due ok pre fEarly ih epochT clearT
    have processed := (applySignedBlock_ok ok).2.1
    have epochS : getCurrentEpoch s = getCurrentEpoch x.state := by
      rw [← epochT]
      simp only [getCurrentEpoch, processBlock_slot processed]
    have clearS := unslashed_before (Step.block engine signed due ok).slashedPersistence clearT
    obtain ⟨extra, floor, paid, single⟩ := ih epochS clearS
    have blockFloor := step ok pre (pre.snoc (.block engine signed due ok)) fEarly epochS clearT
    refine ⟨extra + min (blockQueuePaid s signed.message v)
      (EB - preset.MIN_ACTIVATION_BALANCE.toNat), ?_, ?_, ?_⟩
    · simp only [Run.blockCount, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [runQueuePaid, stepQueuePaid]
      have := Nat.min_le_left (blockQueuePaid s signed.message v)
        (EB - preset.MIN_ACTIVATION_BALANCE.toNat)
      omega
    · intro count
      simp only [Run.blockCount] at count
      have none : pre.blockCount = 0 := by omega
      have zero := runQueuePaid_eq_zero pre none v
      have extraZero : extra = 0 := by
        have := single (by omega)
        rw [zero] at this
        omega
      simp only [runQueuePaid, stepQueuePaid, zero, Nat.zero_add, extraZero]
      exact Nat.le_refl _
  · intro middle last cached next pre ok lastEq cachedOk epochNext ih epochLast clearLast
    have clearMiddle := unslashed_before (Step.slot ok).slashedPersistence clearLast
    subst lastEq
    obtain ⟨extra, floor, paid, single⟩ := ih (epochNext.symm.trans epochLast) clearMiddle
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    refine ⟨extra, ?_, ?_, ?_⟩
    · simpa [Run.blockCount, actualBalanceAt, cachedEq] using floor
    · simpa [runQueuePaid, stepQueuePaid] using paid
    · intro count
      simpa [runQueuePaid, stepQueuePaid] using single (by simpa [Run.blockCount] using count)

/-! ## What every reachable state keeps -/

/-- Every state of a run from genesis keeps the invariant of the transition. -/
private theorem reach_invariant {g x : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (run : Run config checks g x) :
    Invariant x.state := by
  obtain ⟨_, _, _, ok⟩ := genesis
  exact run.invariant (initializeBeaconStateFromEth1_invariant ok).2

/-- Justification and finalization keep the registry, the balances, the slot and the scores. -/
private theorem justification_same {f : Fork} {s t : BeaconState preset f}
    (ok : processJustificationAndFinalization s = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances ∧ t.slot = s.slot ∧
      t.inactivityScores = s.inactivityScores := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest]⟩

/-- Inside one epoch before Gloas, a run keeps the inactivity score of each validator of its
first state. -/
private theorem scores_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state) {i : ℕ}
    (inside : i < x.state.validators.data.size) (ax : .altair ≤ x.fork) (ay : .altair ≤ y.fork) :
    (y.state.inactivityScores ay).data[i]? = (x.state.inactivityScores ax).data[i]? :=
  Run.induction_of_same_epoch
    (motive := fun w _ => ∀ aw : .altair ≤ w.fork,
      (w.state.inactivityScores aw).data[i]? = (x.state.inactivityScores ax).data[i]?)
    (fun _ => rfl)
    (fun _ _ _ ok pre _ ih aw => by
      have grows := Nat.lt_of_lt_of_le inside pre.registryLifecycle.size_le
      rw [scoreKept_processBlock (applySignedBlock_ok ok).2.1 grows aw]
      exact ih aw)
    (fun _ _ lastEq cachedOk _ ih aw => by
      subst lastEq
      obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
      subst cachedEq
      exact ih aw)
    tail early same ay

/-- The arithmetic that closes the fall of a credited voter. -/
private theorem fall_credit_arith {EB after gRewarded gTrue gSub gLow c credit q down inc nS : ℕ}
    (fallZ : EB ≤ after + gRewarded) (gapTrue : gRewarded ≤ gTrue) (one : gTrue ≤ gSub)
    (two : gSub ≤ gLow + c + inc + down - 1) (hc : min credit (down + q + nS) = c) :
    EB - after ≤ gLow + (inc + 2 * down + nS + min credit q) := by
  omega

/-! ## The fall of a voter -/

/-- The fall of the effective balance of a voter that is never slashed, over the end of an epoch.

This is the loss bound of the fast confirmation rule, read by `quorumDrift_le_quorumReserve`.

The epoch starts at `R`, right after its epoch transition, where the hysteresis holds.

A boundary run of at most one block leads to `T`, the block state of the target.

One branch leads from `T` to the call's state `P`, inside the epoch.

Another branch leads from `T` to `y` in the next epoch.

Every read is at `P`, except the queue of partial withdrawals, which is read at `T`.

Take a voter whose balance on the branch of `P` rose by at most its sync rewards.

That voter falls by at most the computed fall.

Take a voter credited more on that branch.

It falls by at most one increment, two downward bands, its sync amount and one more term.

That term is the smaller of its credit and a queued amount.

That amount is what the boundary block's queued payments took from it, up to its effective
balance above the activation balance.

Those queued amounts add up to at most what one sweep can pay below the largest effective
balance. -/
theorem effectiveFall_le
    -- TEMPORARY: S13a moves this lemma to RewardDeltas
    (penaltyEntries_le : ∀ {config : Config} {fork : Fork} {state : BeaconState preset fork}
      {total : Gwei} (altair : .altair ≤ fork) (_within : state.RegistryWithinLimit)
      (_active : getTotalActiveBalance state = .ok total)
      {source target head inactivity : Array Gwei × Array Gwei}
      (_sourceOk : getFlagIndexDeltas state altair ⟨0, by decide⟩ = .ok source)
      (_targetOk : getFlagIndexDeltas state altair ⟨1, by decide⟩ = .ok target)
      (_headOk : getFlagIndexDeltas state altair ⟨2, by decide⟩ = .ok head)
      (_inactivityOk : getInactivityPenaltyDeltas config state = .ok inactivity)
      {j : Nat} (inside : j < state.validators.data.size),
      (source.2.getD j 0).toNat + (target.2.getD j 0).toNat + (head.2.getD j 0).toNat +
          (inactivity.2.getD j 0).toNat = 0 ∨
        ∃ base, isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true ∧
          getBaseReward state total j.toUInt64 = .ok base ∧
          (source.2.getD j 0).toNat + (target.2.getD j 0).toNat + (head.2.getD j 0).toNat +
              (inactivity.2.getD j 0).toNat ≤
            base.toNat * (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) /
                WEIGHT_DENOMINATOR.toNat +
              state.validators.data[j].effectiveBalance.toNat *
                (((state.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
                (config.INACTIVITY_SCORE_BIAS.toNat *
                  (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
    -- TEMPORARY: S13a moves this lemma to RewardDeltas
    (toNat_getBaseReward_le : ∀ {fork : Fork} {state : BeaconState preset fork} {total : Gwei}
      (_altair : .altair ≤ fork) {base : Gwei}
      {index : ValidatorIndex} (_computed : getBaseReward state total index = .ok base)
      {validator : Validator} (_found : state.validators.data[index.toNat]? = some validator),
      base.toNat ≤ validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
          total.toNat.sqrt))
    {g R T P y : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (history : Run config checks g R)
    (boundary : Run config checks R T) (tailP : Run config checks T P)
    (tailS : Run config checks T y) (caps : CapOrder preset)
    (bands : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (hysteresis : Hysteresis R.state) (early : y.fork < .glamsterdam)
    (fulu : .fusaka ≤ P.fork)
    (boundaryEpoch : getCurrentEpoch T.state = getCurrentEpoch R.state)
    (callEpoch : getCurrentEpoch P.state = getCurrentEpoch R.state)
    (next : (getCurrentEpoch y.state).toNat = (getCurrentEpoch R.state).toNat + 1)
    (single : boundary.blockCount ≤ 1) {m n : ℕ} (counted : boundary.blockCount + m ≤ n)
    (credit : ValidatorIndex → ℕ) :
    let state := P.state
    let epoch := getCurrentEpoch state
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let slots := preset.SLOTS_PER_EPOCH.toNat
    let p := parameters preset P.fork
    let positions := Finset.range state.validators.data.size
    let validator (i : ℕ) := state.validators.data[i]?
    let effective (i : ℕ) := balanceAt state i
    let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
    let current (i : ℕ) := isActiveAt state epoch i
    let total := max inc (∑ i ∈ positions with current i, effective i)
    let root := (integerSquareroot (UInt64.ofNat total)).toNat
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
    let base (i : ℕ) := if .altair ≤ P.fork then effective i / inc * perIncrement
      else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
    let seatReward := if .altair ≤ P.fork then
        total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
          slots / preset.SYNC_COMMITTEE_SIZE.toNat
      else 0
    let seats (i : ℕ) := if altair : .altair ≤ P.fork then
        ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
          (validator i).any (·.pubkey == key)).length
      else 0
    let sync (i : ℕ) := seats i * seatReward
    let score (i : ℕ) := if altair : .altair ≤ P.fork then
        (((state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
    let delay := (getPreviousEpoch state).toNat - state.finalizedCheckpoint.epoch.toNat
    let inactivity (i : ℕ) := if .altair ≤ P.fork then
        effective i * (score i + config.INACTIVITY_SCORE_BIAS.toNat) /
          (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
      else if preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY.toNat < delay then
        4 * base i + effective i * delay / p.INACTIVITY_PENALTY_QUOTIENT.toNat
      else 0
    let penalty (i : ℕ) :=
      (if .altair ≤ P.fork then base i else 3 * base i) + inactivity i + slots * sync i
    let syncP (i : ℕ) := n * sync i
    let partials (i : ℕ) := if electra : .pectra ≤ T.fork then
        (((T.state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
          w.validatorIndex.toNat = i ∧ w.withdrawableEpoch ≤ epoch).map (·.amount.toNat)).sum
      else 0
    let fall (i : ℕ) :=
      let low := min (actual i - syncP i) (effective i) - (partials i + penalty i)
      if effective i ≤ low + preset.downwardBand then 0 else effective i - (low - low % inc)
    let maskCap := if .pectra ≤ P.fork then
        preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat *
          (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat - preset.MIN_ACTIVATION_BALANCE.toNat)
      else 0
    (∀ v : ValidatorIndex,
      actualBalanceAt P v.toNat ≤ actualBalanceAt T v.toNat + m * sync v.toNat + credit v) →
    ∃ (below : ValidatorIndex → ℕ) (owed : Finset ValidatorIndex),
      (∀ v, v ∉ owed → below v = 0) ∧ ∑ v ∈ owed, below v ≤ maskCap ∧
      ∀ v : ValidatorIndex, current v.toNat = true →
        ((y.state.validators.data[v.toNat]?).map (·.slashed)).getD false = false →
        effective v.toNat - effectiveAt y v.toNat ≤ fall v.toNat +
          (if credit v = 0 then 0
           else inc + 2 * preset.downwardBand + syncP v.toNat + min (credit v) (below v)) := by
  intro state epoch inc slots p positions validator effective actual current total root
    perIncrement base seatReward seats sync score delay inactivity penalty syncP partials fall
    maskCap creditBound
  have altairP : .altair ≤ P.fork := Nat.le_trans (by decide) fulu
  have electraP : .pectra ≤ P.fork := Nat.le_trans (by decide) fulu
  have delayPos : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := withdrawDelay
  -- The branch of `y` leaves the epoch at one slot.
  have nextT : (getCurrentEpoch y.state).toNat = (getCurrentEpoch T.state).toNat + 1 := by
    rw [boundaryEpoch]; exact next
  obtain ⟨z, z', toZ, edge, fromZ', zEpoch, z'Epoch⟩ := Run.split_next tailS nextT
  -- The forks inside the epoch.
  have Tearly : T.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tailS.chainSteps) early
  have RT : T.fork = R.fork := Run.fork_eq_of_same_epoch boundary boundaryEpoch
  have PT : P.fork = T.fork :=
    Run.fork_eq_of_same_epoch tailP (callEpoch.trans boundaryEpoch.symm)
  have ZT : z.fork = T.fork := Run.fork_eq_of_same_epoch toZ zEpoch
  have Rearly : R.fork < .glamsterdam := RT ▸ Tearly
  have Pearly : P.fork < .glamsterdam := PT ▸ Tearly
  have Zearly : z.fork < .glamsterdam := ZT ▸ Tearly
  have z'Early : z'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps fromZ'.chainSteps) early
  have electraT : .pectra ≤ T.fork := PT ▸ electraP
  have electraR : .pectra ≤ R.fork := RT ▸ electraT
  -- What every state of the epoch reads like the state `R`.
  have readsAt : ∀ {w : ForkedBeaconState preset} (run : Run config checks R w),
      w.fork < .glamsterdam → getCurrentEpoch w.state = getCurrentEpoch R.state →
      (w.fork = R.fork ∧ validatorKeys R.state <+: validatorKeys w.state ∧
        ∀ (altair : .altair ≤ w.fork) (altair' : .altair ≤ R.fork),
          (w.state.currentSyncCommittee altair).value.pubkeys.toList =
            (R.state.currentSyncCommittee altair').value.pubkeys.toList) ∧
      EffectiveKept R.state w.state ∧
      R.state.validators.data.size ≤ w.state.validators.data.size ∧
      ∀ i, isActiveAt w.state (getCurrentEpoch R.state) i =
        isActiveAt R.state (getCurrentEpoch R.state) i :=
    fun run wEarly same => ⟨⟨Run.fork_eq_of_same_epoch run same,
        (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).1,
        fun altair altair' => Run.currentSyncCommittee_eq_of_same_epoch run wEarly same altair
          altair'⟩,
      run.effectiveKept_of_same_epoch wEarly same, run.registryLifecycle.size_le,
      fun i => activeKept_of_chainSteps run.chainSteps _
        (getCurrentEpoch_le_activityFixedEpoch _) i⟩
  obtain ⟨⟨-, keysP, committeeP⟩, keptP, growsP, activeP⟩ :=
    readsAt (boundary.append tailP) Pearly callEpoch
  have sumP : ∑ i ∈ positions with current i, effective i =
      ∑ i ∈ (Finset.range R.state.validators.data.size).filter
        (fun i => isActiveAt R.state (getCurrentEpoch R.state) i = true),
        ((R.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
    have := activeSum_eq activeP keptP growsP
    simp only [positions, current, epoch, state, effective, balanceAt, callEpoch]
    exact this
  -- The validators that the boundary block pays from the queue.
  obtain ⟨owed, owedCard, covers⟩ := owed_card boundary single
  refine ⟨fun v => min (runQueuePaid boundary v)
    (effective v.toNat - preset.MIN_ACTIVATION_BALANCE.toNat), owed, ?_, ?_, ?_⟩
  · intro v absent
    have zero : runQueuePaid boundary v = 0 := by
      by_contra paid
      exact absent (covers v paid)
    simp [zero]
  · have each : ∀ v ∈ owed, min (runQueuePaid boundary v)
        (effective v.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat - preset.MIN_ACTIVATION_BALANCE.toNat := by
      intro v _
      refine (Nat.min_le_right _ _).trans (Nat.sub_le_sub_right ?_ _)
      cases read : P.state.validators.data[v.toNat]? with
      | none => simp [effective, balanceAt, state, read]
      | some val =>
        have capped := ((history.append boundary).append tailP).effectiveBalance_capped genesis
          caps.activation caps.compounding Pearly val (Array.mem_of_getElem? read)
        have top : withdrawalMaxEffectiveBalance preset P.fork val ≤
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA := by
          simp only [withdrawalMaxEffectiveBalance, electraP, ↓reduceIte, getMaxEffectiveBalance]
          split
          · exact UInt64.le_refl _
          · exact caps.compounding
        have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans capped top)
        simpa [effective, balanceAt, state, read] using this
    calc _ ≤ ∑ v ∈ owed, (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
          preset.MIN_ACTIVATION_BALANCE.toNat) := Finset.sum_le_sum each
      _ = owed.card * (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
          preset.MIN_ACTIVATION_BALANCE.toNat) := by simp
      _ ≤ maskCap := by
        simp only [maskCap, electraP, ↓reduceIte]
        exact Nat.mul_le_mul_right _ owedCard
  · intro v activeV clearY
    -- The validator is not slashed at `y`, so at no state before it.
    have clearAtY : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false := by
      intro w read
      simpa [read] using clearY
    have clearZ' := unslashed_before fromZ'.slashedPersistence clearAtY
    have clearZ := unslashed_before (Step.slot edge).slashedPersistence clearZ'
    have clearT := unslashed_before tailS.slashedPersistence clearAtY
    -- The validator at `R`, active in the epoch.
    have activeR : isActiveAt R.state (getCurrentEpoch R.state) v.toNat = true := by
      rw [← activeP v.toNat, ← callEpoch]
      exact activeV
    obtain ⟨valR, foundR, isActiveR⟩ := isActiveAt_eq_true_iff.mp activeR
    have insideR := (Array.getElem?_eq_some_iff.mp foundR).1
    have effEq : effective v.toNat = valR.effectiveBalance.toNat := by
      show effectiveAt P v.toNat = _
      rw [keptP v.toNat insideR]
      simp [effectiveAt, foundR]
    generalize hEB : valR.effectiveBalance.toNat = EB at effEq
    -- The downward band at `R`.
    have invR := reach_invariant genesis history
    obtain ⟨balR, readR⟩ : ∃ b, R.state.balances.data[v.toNat]? = some b :=
      ⟨_, Array.getElem?_eq_getElem (by rw [invR.balancesMatch]; exact insideR)⟩
    have hysR := hysteresis.down v.toNat valR balR foundR readR
    have actualR : actualBalanceAt R v.toNat = balR.toNat := by
      simp [actualBalanceAt, readR]
    rw [hEB] at hysR
    -- The sync amount of the validator, read at any state of the epoch.
    have syncAt : ∀ {w : ForkedBeaconState preset} (toW : Run config checks R w)
        (wEarly : w.fork < .glamsterdam) (wEpoch : getCurrentEpoch w.state = getCurrentEpoch R.state)
        (altairW : .altair ≤ w.fork),
        seatsAt w.state altairW v.toNat * seatRewardAt w.state = sync v.toNat := by
      intro w toW wEarly wEpoch altairW
      obtain ⟨⟨fEq, keysW, committeeW⟩, keptW, growsW, activeW⟩ := readsAt toW wEarly wEpoch
      have altairR : .altair ≤ R.fork := fEq ▸ altairW
      have seatsSame : seatsAt w.state altairW v.toNat = seats v.toNat := by
        simp only [seats, altairP, dite_true, seatsAt]
        refine seats_eq altairW altairP ?_ ?_
        · rw [committeeW altairW altairR, committeeP altairP altairR]
        · obtain ⟨u, readW, keyW⟩ := validators_getElem?_of_validatorKeys_prefix keysW foundR
          obtain ⟨u', readP, keyP⟩ := validators_getElem?_of_validatorKeys_prefix keysP foundR
          simp only [state, readW, readP, Option.map_some, keyW, keyP]
      have rewardSame : seatRewardAt w.state = seatReward := by
        have sums := activeSum_eq activeW keptW growsW
        simp only [seatRewardAt, wEpoch, sums, seatReward, altairP, ↓reduceIte, perIncrement,
          root, total, sumP, inc, slots]
      rw [seatsSame, rewardSame]
    -- Each block of the epoch keeps the floor of the balance.
    have stepFloor : ∀ {X : ForkedBeaconState preset} (histX : Run config checks g X)
        (fromR : Run config checks R X), getCurrentEpoch X.state = getCurrentEpoch R.state →
        ∀ {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
          {signed : SignedBeaconBlock preset f},
          applySignedBlock config checks engine s signed true = .ok t →
          Run config checks X ⟨f, s⟩ → Run config checks X ⟨f, t⟩ → f < .glamsterdam →
          getCurrentEpoch s = getCurrentEpoch X.state →
          (∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) →
          min (actualBalanceAt ⟨f, s⟩ v.toNat) EB ≤ actualBalanceAt ⟨f, t⟩ v.toNat +
            sync v.toNat + min (blockQueuePaid s signed.message v)
              (EB - preset.MIN_ACTIVATION_BALANCE.toNat) := by
      intro X histX fromR XEpoch f s t engine signed ok pre post fEarly sEpoch clearAfter
      have toS := fromR.append pre
      have sEpochR : getCurrentEpoch s = getCurrentEpoch R.state := sEpoch.trans XEpoch
      have fEq : f = R.fork := Run.fork_eq_of_same_epoch toS sEpochR
      have electraF : .pectra ≤ f := fEq ▸ electraR
      obtain ⟨-, keptS, -, activeS⟩ := readsAt toS fEarly sEpochR
      have activeAtS : isActiveAt s (getCurrentEpoch R.state) v.toNat = true := by
        rw [show isActiveAt s (getCurrentEpoch R.state) v.toNat =
          isActiveAt R.state (getCurrentEpoch R.state) v.toNat from activeS v.toNat]
        exact activeR
      obtain ⟨valS, foundS, isActiveS⟩ := isActiveAt_eq_true_iff.mp activeAtS
      have effS : valS.effectiveBalance.toNat = EB := by
        have := keptS v.toNat insideR
        simp only [effectiveAt, foundS, foundR, Option.map_some, Option.getD_some] at this
        rw [this, hEB]
      have invS := reach_invariant genesis (histX.append pre)
      have later : getCurrentEpoch s < valS.withdrawableEpoch := by
        have ordered := invS.exitsOrdered valS (Array.mem_of_getElem? foundS)
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActiveS
        rw [sEpochR]
        exact UInt64.lt_of_lt_of_le isActiveS.2 ordered
      have capS := (histX.append pre).effectiveBalance_capped genesis caps.activation
        caps.compounding fEarly valS (Array.mem_of_getElem? foundS)
      have floor := block_floor fEarly electraF invS.balancesMatch
        (applySignedBlock_ok ok).2.1 foundS later capS clearAfter
      have tEpoch : getCurrentEpoch t = getCurrentEpoch R.state := by
        rw [← sEpochR]
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      rw [syncAt (fromR.append post) fEarly tEpoch, effS] at floor
      exact floor
    -- The boundary run, with at most one block.
    obtain ⟨extraRT, floorRT, -, belowRT⟩ := run_floor boundary Tearly boundaryEpoch clearT
      (stepFloor history .nil rfl)
    have belowBound := belowRT single
    -- The blocks of the branch of `y` inside the epoch.
    have histT := history.append boundary
    obtain ⟨extraTZ, floorTZ, paidTZ, -⟩ := run_floor toZ Zearly zEpoch clearZ
      (stepFloor histT boundary boundaryEpoch)
    -- Those blocks pay at most the partial withdrawals queued at `T` and due by the epoch.
    have queueTZ : runQueuePaid toZ v ≤ partials v.toNat := by
      have bound := runQueuePaid_le toZ Zearly zEpoch electraT (ZT ▸ electraT) v
      simp only [partials, electraT, dite_true, epoch, state, callEpoch, ← boundaryEpoch]
      exact bound
    -- The blocks of the epoch fit its slots.
    have blocksTZ : toZ.blockCount ≤ slots := by
      have slotsPos : 0 < slots := by
        by_contra zero
        have zero : slots = 0 := by omega
        have epochY := getCurrentEpoch_toNat y.state
        have epochR := getCurrentEpoch_toNat R.state
        simp only [slots] at zero
        rw [zero, Nat.div_zero] at epochY epochR
        omega
      have epochT := getCurrentEpoch_toNat T.state
      have epochZ := getCurrentEpoch_toNat z.state
      rw [zEpoch] at epochZ
      have sameQuotient : z.state.slot.toNat / slots = T.state.slot.toNat / slots := by
        simp only [slots]
        omega
      have bound := toZ.blocks_le_slots (a := T.state.slot.toNat / slots * slots)
        (b := T.state.slot.toNat / slots * slots + slots - 1) (Nat.div_mul_le_self _ _) (by
          have split := Nat.div_add_mod z.state.slot.toNat slots
          have small := Nat.mod_lt z.state.slot.toNat slotsPos
          rw [sameQuotient, Nat.mul_comm] at split
          omega)
      omega
    -- The validator at the last state of the epoch on the branch of `y`.
    have zEpochR : getCurrentEpoch z.state = getCurrentEpoch R.state := zEpoch.trans boundaryEpoch
    obtain ⟨-, keptZ, growsZ, activeZs⟩ := readsAt (boundary.append toZ) Zearly zEpochR
    have activeZ : isActiveAt z.state (getCurrentEpoch z.state) v.toNat = true := by
      rw [zEpochR, activeZs v.toNat]
      exact activeR
    obtain ⟨valZ, foundZ, -⟩ := isActiveAt_eq_true_iff.mp activeZ
    have insideZ := (Array.getElem?_eq_some_iff.mp foundZ).1
    have effZ : valZ.effectiveBalance.toNat = EB := by
      have := keptZ v.toNat insideR
      simp only [effectiveAt, foundZ, foundR, Option.map_some, Option.getD_some] at this
      rw [this, hEB]
    have histZ := histT.append toZ
    have invZ := reach_invariant genesis histZ
    have capZ := histZ.effectiveBalance_capped genesis caps.activation caps.compounding Zearly valZ
      (Array.mem_of_getElem? foundZ)
    have nextZ : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch z.state).toNat + 1 := by
      rw [z'Epoch, zEpochR]; exact next
    have altairZ : .altair ≤ z.fork := by rw [ZT, ← PT]; exact altairP
    have holdsZ : PendingConsolidationInvariant config z.state :=
      fun electra => Run.pendingConsolidation_invariant histZ genesis Zearly electra delayPos
    obtain ⟨cached, justified, scored, rewarded, cachedOk, justifiedOk, scoredOk, rewardedOk,
      fallZ⟩ := crossing_fall altairZ edge z'Early nextZ bands holdsZ invZ.balancesMatch delayPos
        foundZ activeZ (clearZ valZ foundZ) capZ
    rw [effZ] at fallZ
    -- The effective balance stays through the next epoch.
    have insideZ' : v.toNat < z'.state.validators.data.size :=
      Nat.lt_of_lt_of_le insideZ (Run.nil.snoc (.slot edge)).registryLifecycle.size_le
    have yEff : effectiveAt y v.toNat = effectiveAt z' v.toNat :=
      fromZ'.effectiveKept_of_same_epoch early z'Epoch.symm v.toNat insideZ'
    -- The state that the rewards read is the last state of the epoch, after justification.
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have justifiedSame := justification_same justifiedOk
    have Jvalidators : justified.validators = z.state.validators := by
      rw [justifiedSame.1, cachedEq]
    have Jbalances : justified.balances = z.state.balances := by
      rw [justifiedSame.2.1, cachedEq]
    have Jslot : justified.slot = z.state.slot := by
      rw [justifiedSame.2.2.1, cachedEq]
    have JEpoch : getCurrentEpoch justified = getCurrentEpoch R.state := by
      rw [← zEpochR]
      simp only [getCurrentEpoch, Jslot]
    have insideJ : v.toNat < justified.validators.data.size := by rw [Jvalidators]; exact insideZ
    have effJ : ((justified.validators.data[v.toNat]?).map (·.effectiveBalance.toNat)).getD 0 =
        EB := by
      rw [Jvalidators, foundZ]
      exact effZ
    have balJ : ((justified.balances.data[v.toNat]?).map (·.toNat)).getD 0 =
        actualBalanceAt z v.toNat := by
      simp only [actualBalanceAt, Jbalances]
    have sumJ : ∑ i ∈ (Finset.range justified.validators.data.size).filter
          (fun i => isActiveAt justified (getCurrentEpoch justified) i = true),
          ((justified.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
        ∑ i ∈ positions with current i, effective i := by
      rw [sumP, ← activeSum_eq activeZs keptZ growsZ, JEpoch]
      simp only [isActiveAt, Jvalidators]
      rfl
    have totalJ : max inc (∑ i ∈ (Finset.range justified.validators.data.size).filter
          (fun i => isActiveAt justified (getCurrentEpoch justified) i = true),
          ((justified.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) = total := by
      rw [sumJ]
    have effV : effective v.toNat = EB := effEq
    -- The rewards take at most the penalty of the voter, without the sync penalties.
    have penaltyBound : actualBalanceAt z v.toNat ≤
        actualBalanceAt ⟨z.fork, rewarded⟩ v.toNat + (base v.toNat + inactivity v.toNat) := by
      have altairT : .altair ≤ T.fork := by rw [← ZT]; exact altairZ
      have bound := (processRewardsAndPenalties_balance_le_of_inactivityUpdates penaltyEntries_le
        toNat_getBaseReward_le altairZ (justified.validators.bound Zearly) scoredOk rewardedOk
        v.toNat insideJ).2
      dsimp only at bound
      rw [totalJ, effJ, balJ] at bound
      have scoreJ :
          (((justified.inactivityScores altairZ).data[v.toNat]?).map (·.toNat)).getD 0 =
            score v.toNat := by
        have insideT := Nat.lt_of_lt_of_le insideR boundary.registryLifecycle.size_le
        have zScore := scores_of_same_epoch toZ Zearly zEpoch insideT altairT altairZ
        have pScore := scores_of_same_epoch tailP Pearly (callEpoch.trans boundaryEpoch.symm)
          insideT altairT altairP
        simp only [score, altairP, dite_true, state]
        rw [justifiedSame.2.2.2, pScore, ← zScore, cachedEq]
      rw [scoreJ] at bound
      simp only [base, inactivity, altairP, ↓reduceIte, effV, perIncrement, root, p]
      have quotient : (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat =
          p.INACTIVITY_PENALTY_QUOTIENT.toNat := by
        simp only [p]
        rw [ZT, PT]
      rw [quotient] at bound
      simp only [actualBalanceAt, inc, p, Nat.add_assoc] at bound ⊢
      exact bound
    -- Put the bounds together.
    have fallEq : fall v.toNat = fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        preset.downwardBand (effective v.toNat)
        (min (actual v.toNat - syncP v.toNat) (effective v.toNat) -
          (partials v.toNat + penalty v.toNat)) := rfl
    have penaltyEq : penalty v.toNat = (base v.toNat + inactivity v.toNat) +
        slots * sync v.toNat := by
      simp only [penalty, altairP, ↓reduceIte]
    have syncPEq : syncP v.toNat = n * sync v.toNat := rfl
    have actualEq : actual v.toNat = actualBalanceAt P v.toNat := rfl
    have creditV := creditBound v
    rw [fallEq, syncPEq, actualEq, penaltyEq, yEff]
    rw [effV]
    have tzProduct := Nat.mul_le_mul_right (sync v.toNat) blocksTZ
    have rtProduct : boundary.blockCount * sync v.toNat + m * sync v.toNat ≤ n * sync v.toNat := by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right _ counted
    have increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := bands.1
    -- The balance after the rewards is at least the balance that the fall reads, lowered.
    generalize hLow : min (actualBalanceAt T v.toNat) EB - (partials v.toNat +
      ((base v.toNat + inactivity v.toNat) + slots * sync v.toNat)) = lowTrue
    have rewardedLow : lowTrue ≤ actualBalanceAt ⟨z.fork, rewarded⟩ v.toNat := by omega
    have gapTrue :=
      fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand EB rewardedLow
    generalize hlow : min (actualBalanceAt P v.toNat - n * sync v.toNat) EB -
      (partials v.toNat + ((base v.toNat + inactivity v.toNat) + slots * sync v.toNat)) = low
    by_cases zero : credit v = 0
    · -- Without other credits, the balance read at `T` covers the one that the fall reads.
      simp only [zero, ↓reduceIte, add_zero]
      have covered : low ≤ lowTrue := by omega
      have := fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand EB covered
      omega
    · -- With them, the downward band at `R` bounds what they can hide.
      simp only [zero, ↓reduceIte]
      generalize hc : min (credit v) (preset.downwardBand +
        min (runQueuePaid boundary v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat) +
          n * sync v.toNat) = c
      have covered : low - c ≤ lowTrue := by omega
      have one :=
        fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand EB covered
      have two := fallGap_sub increment preset.downwardBand EB low c
      exact fall_credit_arith fallZ gapTrue one two (by rw [effV]; exact hc)

end EthLib.Consensus
