module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import EthLib.Consensus.Proofs.Transition.BlockRewards
public import EthLib.Consensus.Proofs.Transition.ExitReserve
public import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
public import EthLib.Consensus.Proofs.Transition.SlashedPersistence
-- The private step lemmas `StepKeeps` and `stepKeeps_*` keep activity through each block step.
import all EthLib.Consensus.Proofs.Transition.ActiveKept
-- This import gives the private lemmas `effectiveKept_*` and `Run.induction_of_same_epoch`.
--
-- They keep effective balances through each block step.
import all EthLib.Consensus.Proofs.Transition.BalanceDrift
-- The private sweep and queue lemmas, such as `withdrawnFrom_of_sweepPays`, read each withdrawal.
import all EthLib.Consensus.Proofs.Transition.WithdrawalAmounts
-- The private step `PendingConsolidationInvariant.step` keeps the pending sources.
import all EthLib.Consensus.Proofs.Transition.PendingConsolidations
-- The private frames of the pending attestations keep their epochs.
import all EthLib.Consensus.Proofs.Transition.TargetPending
-- The private lemma `upgradeNext_altair` reads the fork of an upgrade.
import all EthLib.Consensus.Proofs.Transition.TargetUpgrades
-- The private relation `SameSyncCommittees` keeps the sync committees through a block.
import all EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Bounds for the sources of balance drift

These contracts use the amounts computed by the transition, not arbitrary accounting caps.

Epoch-interval bounds sum the per-call amounts, including queues inherited at the first state.

Deposits to withdrawn validators bypass the Electra churn and are accounted separately.

Consolidations count both their debit and credit even though their net balance change is zero.

The branch corrections cover a branch inside one epoch.

They read every balance change from the last state.

Withdrawals and conversions debit a counted set.

The sync committee moves each member by its seats.

The other credits go to the proposers of the blocks and to the recipients of deposits.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def sumAmounts (values : Array Gwei) : Nat := (values.toList.map (·.toNat)).sum

def totalBalance {fork : Fork} (s : BeaconState preset fork) : Nat := sumAmounts s.balances.data

/-- Positive changes are summed per index, so a transfer cannot cancel a loss elsewhere. -/
def balanceCredits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)

def balanceDebits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range s.balances.data.size,
    (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i)

private theorem credits_increase {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s i amount = .ok t) :
    balanceCredits s t = amount.toNat ∧ balanceDebits s t = 0 := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  have point (j : Nat) :
      actualBalanceAt ⟨fork, s.putBalance i.toNat inside (s.balances.data[i.toNat] + amount)⟩ j =
        actualBalanceAt ⟨fork, s⟩ j + if j = i.toNat then amount.toNat else 0 := by
    by_cases same : j = i.toNat
    · subst j
      simp [actualBalanceAt, BeaconState.putBalance, inside, toNat_add_of_lt fits]
    · simp [actualBalanceAt, BeaconState.putBalance, same, Ne.symm same]
  have size : (s.putBalance i.toNat inside
      (s.balances.data[i.toNat] + amount)).balances.data.size =
        s.balances.data.size := by simp [BeaconState.putBalance]
  simp [balanceCredits, balanceDebits, size, point, Finset.sum_ite_eq', inside]

private theorem debits_decrease {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s i amount = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤ amount.toNat := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  have point (j : Nat) :
      actualBalanceAt ⟨fork, s.putBalance i.toNat inside
        (saturatingSub s.balances.data[i.toNat] amount)⟩ j =
        actualBalanceAt ⟨fork, s⟩ j - if j = i.toNat then amount.toNat else 0 := by
    by_cases same : j = i.toNat
    · subst j
      simp [actualBalanceAt, BeaconState.putBalance, inside, toNat_saturatingSub]
    · simp [actualBalanceAt, BeaconState.putBalance, same, Ne.symm same]
  have size : (s.putBalance i.toNat inside
      (saturatingSub s.balances.data[i.toNat] amount)).balances.data.size =
        s.balances.data.size := by simp [BeaconState.putBalance]
  constructor
  · simp [balanceCredits, size, point]
  · unfold balanceDebits
    simp only [point]
    calc
      _ ≤ ∑ j ∈ Finset.range s.balances.data.size,
          if j = i.toNat then amount.toNat else 0 := by
        apply Finset.sum_le_sum
        intro j _
        omega
      _ = amount.toNat := by simp [Finset.sum_ite_eq', inside]

private theorem credits_triangle {fork : Fork} (s u t : BeaconState preset fork)
    (size : t.balances.data.size = u.balances.data.size) :
    balanceCredits s t ≤ balanceCredits s u + balanceCredits u t := by
  unfold balanceCredits
  rw [← size, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

private theorem debits_triangle {fork : Fork} (s u t : BeaconState preset fork)
    (size : s.balances.data.size = u.balances.data.size) :
    balanceDebits s t ≤ balanceDebits s u + balanceDebits u t := by
  unfold balanceDebits
  rw [← size, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

private theorem credits_triangle_growing {fork : Fork} (s u t : BeaconState preset fork)
    (size : u.balances.data.size ≤ t.balances.data.size) :
    balanceCredits s t ≤ balanceCredits s u + balanceCredits u t := by
  -- Indices beyond the intermediate array contribute zero to its credits.
  have extend : (∑ i ∈ Finset.range t.balances.data.size,
      (actualBalanceAt ⟨fork, u⟩ i - actualBalanceAt ⟨fork, s⟩ i)) = balanceCredits s u := by
    symm
    apply Finset.sum_subset (Finset.range_mono size)
    intro i _ outside
    simp only [Finset.mem_range, not_lt] at outside
    simp [actualBalanceAt, Array.getElem?_eq_none outside]
  unfold balanceCredits at *
  rw [← extend, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

private theorem debits_triangle_growing {fork : Fork} (s u t : BeaconState preset fork)
    (size : s.balances.data.size ≤ u.balances.data.size) :
    balanceDebits s t ≤ balanceDebits s u + balanceDebits u t := by
  have upper : (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨fork, u⟩ i - actualBalanceAt ⟨fork, t⟩ i)) ≤ balanceDebits u t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono size)
    intros
    omega
  unfold balanceDebits at *
  have point : (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i)) ≤
        (∑ i ∈ Finset.range s.balances.data.size,
          (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, u⟩ i)) +
        (∑ i ∈ Finset.range s.balances.data.size,
          (actualBalanceAt ⟨fork, u⟩ i - actualBalanceAt ⟨fork, t⟩ i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    omega
  omega

/-- Rewards and ordinary penalties are kept separate from the inactivity pass. -/
def rewardPasses {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError (List (Array Gwei × Array Gwei)) := do
  if getCurrentEpoch s = GENESIS_EPOCH then return []
  if altair : .altair ≤ fork then
    (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM (getFlagIndexDeltas s altair)
  else
    let early := Nat.lt_of_not_le altair
    return [← getSourceDeltas s early, ← getTargetDeltas s early,
      ← getHeadDeltas s early, ← getInclusionDelayDeltas s early]

theorem epoch_rewards_penalties {fork : Fork} (s t : BeaconState preset fork)
    (ordinary : List (Array Gwei × Array Gwei)) (inactivity : Array Gwei × Array Gwei)
    (rewards : rewardPasses s = .ok ordinary)
    (leak : getInactivityPenaltyDeltas config s = .ok inactivity)
    (ok : processRewardsAndPenalties config s = .ok t) :
    balanceCredits s t ≤ (ordinary.map fun p => sumAmounts p.1).sum ∧
    balanceDebits s t ≤ (ordinary.map fun p => sumAmounts p.2).sum +
      sumAmounts inactivity.2 := by
  have sumLookup (xs : List Gwei) (n : Nat) :
      ((List.range n).map fun i => (xs[i]?.getD 0).toNat).sum ≤
        (xs.map fun x => x.toNat).sum := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
        rw [List.range_succ_eq_map]
        simpa [List.map_map, Function.comp_def] using Nat.add_le_add_left (ih n) x.toNat
  have sumArray (xs : Array Gwei) (n : Nat) :
      ((List.range n).map fun i => (xs.getD i 0).toNat).sum ≤ sumAmounts xs := by
    simpa [sumAmounts, Array.getD_eq_getD_getElem?] using sumLookup xs.toList n
  have apply (s t : BeaconState preset fork) (p : Array Gwei × Array Gwei)
      (ok : applyAllDeltas s p = .ok t) :
      balanceCredits s t ≤ sumAmounts p.1 ∧ balanceDebits s t ≤ sumAmounts p.2 := by
    have fold (is : List Nat) (s t : BeaconState preset fork)
        (ok : is.foldlM (applyDeltas p.1 p.2) s = .ok t) :
        t.balances.data.size = s.balances.data.size ∧
        balanceCredits s t ≤ (is.map fun i => (p.1.getD i 0).toNat).sum ∧
        balanceDebits s t ≤ (is.map fun i => (p.2.getD i 0).toNat).sum := by
      induction is generalizing s with
      | nil => cases ok; simp [balanceCredits, balanceDebits]
      | cons i is ih =>
        simp only [List.foldlM_cons, bind_ok_iff] at ok
        obtain ⟨u, first, last⟩ := ok
        have later := ih u last
        have sizes := (sameSizes_applyDeltas first).2
        simp only [applyDeltas, liftAccessor_ok, bind_ok_iff] at first
        obtain ⟨index, _, raised, raise, lower⟩ := first
        have up := credits_increase raise
        have down := debits_decrease lower
        have oneC := credits_triangle s raised u (sameSizes_decreaseBalance lower).2
        have oneD := debits_triangle s raised u (sameSizes_increaseBalance raise).2.symm
        have allC := credits_triangle s u t later.1
        have allD := debits_triangle s u t sizes.symm
        simp only [List.map_cons, List.sum_cons]
        exact ⟨later.1.trans sizes, by omega, by omega⟩
    have facts := fold _ s t ok
    have rewards := sumArray p.1 s.validators.data.size
    have penalties := sumArray p.2 s.validators.data.size
    exact ⟨facts.2.1.trans rewards, facts.2.2.trans penalties⟩
  have passes (ps : List (Array Gwei × Array Gwei)) (s t : BeaconState preset fork)
      (ok : ps.foldlM applyAllDeltas s = .ok t) :
      t.balances.data.size = s.balances.data.size ∧
      balanceCredits s t ≤ (ps.map fun p => sumAmounts p.1).sum ∧
      balanceDebits s t ≤ (ps.map fun p => sumAmounts p.2).sum := by
    induction ps generalizing s with
    | nil => cases ok; simp [balanceCredits, balanceDebits]
    | cons p ps ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have a := apply s u p first
      have b := ih u last
      have sizes := (sameSizes_applyAllDeltas first).2
      have credits := credits_triangle s u t b.1
      have debits := debits_triangle s u t sizes.symm
      simp only [List.map_cons, List.sum_cons]
      exact ⟨b.1.trans sizes, by omega, by omega⟩
  have sumFour (a b c d result : Array Gwei)
      (ok : sumDeltas a b c d = .ok result) :
      sumAmounts result ≤ sumAmounts a + sumAmounts b + sumAmounts c + sumAmounts d := by
    have equality : ((List.range result.size).map fun i => (result.getD i 0).toNat).sum =
        sumAmounts result := by
      have eq (xs : List Gwei) :
          ((List.range xs.length).map fun i => (xs[i]?.getD 0).toNat) =
            xs.map fun x => x.toNat := by
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using ih
      simpa [sumAmounts, Array.getD_eq_getD_getElem?] using congrArg List.sum (eq result.toList)
    rw [← equality]
    have point (i : Nat) : (result.getD i 0).toNat ≤
        (a.getD i 0).toNat + (b.getD i 0).toNat + (c.getD i 0).toNat +
          (d.getD i 0).toNat := by
      rw [sumDeltas_getD ok i]
      split <;> omega
    have bound := List.sum_le_sum (l := List.range result.size) (fun i _ => point i)
    simp only [List.sum_map_add] at bound
    have ha := sumArray a result.size
    have hb := sumArray b result.size
    have hc := sumArray c result.size
    have hd := sumArray d result.size
    omega
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · simp only [processRewardsAndPenalties, genesis, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at ok
    subst t
    simp [balanceCredits, balanceDebits]
  · by_cases altair : .altair ≤ fork
    · simp only [rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte] at rewards
      simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte,
        rewards, leak, bind, Except.bind] at ok
      have facts := (passes _ s t ok).2
      have zero : sumAmounts inactivity.1 = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.mp hv
        have z := getInactivityPenaltyDeltas_rewards leak i
        simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi),
          ← h] using congrArg UInt64.toNat z
      simpa [zero] using facts
    · simp only [rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte,
        bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rewards
      obtain ⟨source, sourceOk, target, targetOk, head, headOk, inclusion, inclusionOk,
        rfl⟩ := rewards
      simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte,
        bind_ok_iff] at ok
      obtain ⟨pair, deltas, applied⟩ := ok
      simp only [getAttestationDeltas, sourceOk, targetOk, headOk, inclusionOk, leak,
        bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at deltas
      obtain ⟨rs, rsOk, ps, psOk, rfl⟩ := deltas
      have bounds := apply s t (rs, ps) applied
      dsimp only at bounds
      -- Phase0 sums before applying; checked additions preserve the natural-number sums.
      have cr := sumFour _ _ _ _ _ rsOk
      have db := sumFour _ _ _ _ _ psOk
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega

/-- Both recipient credits are included, also when proposer and whistleblower coincide. -/
theorem initial_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (i : ValidatorIndex) (whistleblower : Option ValidatorIndex) (v : Validator)
    (found : getValidator s i = .ok v)
    (ok : slashValidator config s i whistleblower = .ok t) :
    balanceDebits s t ≤ v.effectiveBalance.toNat /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    balanceCredits s t ≤ v.effectiveBalance.toNat /
      (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  obtain ⟨exited, validator, withdrawable, marked, slashed, total, slashings, lowered,
    proposer, reward, raised, last, exit, validatorOk, _, mark, _, _, _, lower, _, share,
    raise, lastOk, final⟩ := slashValidator_ok ok
  have exitFacts : exited.balances = s.balances ∧
      validator.effectiveBalance = v.effectiveBalance := by
    obtain ⟨v', found', exitedAlready | ⟨_, queued, epoch, withdrawable, queue, _, set⟩⟩ :=
      initiateValidatorExit_ok exit
    · have vv : v' = v := Except.ok.inj (found'.symm.trans found)
      subst v'
      rcases exitedAlready with ⟨_, rfl⟩
      have vv : validator = v := Except.ok.inj (validatorOk.symm.trans found)
      exact ⟨rfl, congrArg Validator.effectiveBalance vv⟩
    · have vv : v' = v := Except.ok.inj (found'.symm.trans found)
      subst v'
      have vv := getValidator_setValidator_self set
      have veq := Except.ok.inj (validatorOk.symm.trans vv)
      have effective := congrArg (fun x => x.effectiveBalance) veq
      obtain ⟨_, rfl⟩ := setValidator_ok set
      exact ⟨(exitQueue_validators queue).2, effective⟩
  have markedBalance : marked.balances = s.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok mark
    exact exitFacts.1
  have shareLe : reward.toNat ≤
      (validator.effectiveBalance /
        (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    unfold proposerShare at share
    split at share
    · simp only [bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq] at share
      obtain ⟨product, productOk, rfl⟩ := share
      have productEq := (mulChecked_ok_iff.mp productOk).2
      rw [UInt64.toNat_div, productEq]
      change _ * 8 / 64 ≤ _
      omega
    · simp only [pure, Except.pure, Except.ok.injEq] at share
      subst reward
      exact Nat.div_le_self _ _
  have lo := debits_decrease lower
  have up := credits_increase raise
  have tail := credits_increase lastOk
  have firstCredits := credits_triangle { marked with slashings } lowered raised
    (sameSizes_increaseBalance raise).2
  have firstDebits := debits_triangle { marked with slashings } lowered raised
    (sameSizes_decreaseBalance lower).2.symm
  have secondCredits := credits_triangle { marked with slashings } raised last
    (sameSizes_increaseBalance lastOk).2
  have secondDebits := debits_triangle { marked with slashings } raised last
    ((sameSizes_increaseBalance raise).2.trans (sameSizes_decreaseBalance lower).2).symm
  have leftReward : (validator.effectiveBalance /
      (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT - reward).toNat =
        (validator.effectiveBalance /
          (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat -
            reward.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe)
  have bound : balanceDebits { marked with slashings } last ≤
      (validator.effectiveBalance /
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT).toNat ∧
      balanceCredits { marked with slashings } last ≤
      (validator.effectiveBalance /
        (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    omega
  have finalBalance : t.balances = last.balances := by
    rw [final]
    split <;> rfl
  simpa only [balanceDebits, balanceCredits, actualBalanceAt, finalBalance, markedBalance,
    UInt64.toNat_div, exitFacts.2] using bound

/-- Sum only due penalties, with the fork's actual rounding and adjusted slashing balance. -/
def delayedSlashingLimit {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError Nat := do
  let total ← liftAccessor (getTotalActiveBalance s)
  let slashed ← slashingsSum s
  let adjusted := min (slashed.toNat *
    (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  return (s.validators.data.toList.map fun v =>
    if SlashingPenaltyDue preset (getCurrentEpoch s) v then
      if .pectra ≤ fork then
        adjusted / (total.toNat / increment) * (v.effectiveBalance.toNat / increment)
      else v.effectiveBalance.toNat / increment * adjusted / total.toNat * increment
    else 0).sum

/-- No penalty is charged merely because a validator has effective stake. -/
theorem delayed_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (within : s.RegistryWithinLimit)
    (ok : processSlashings s = .ok t) :
    ∃ limit, delayedSlashingLimit s = .ok limit ∧
      balanceCredits s t = 0 ∧ balanceDebits s t ≤ limit := by
  have sumLookup (xs : List Nat) (n : Nat) :
      (∑ i ∈ Finset.range n, xs[i]?.getD 0) ≤ xs.sum := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
        rw [Finset.sum_range_succ']
        simpa [Nat.add_comm] using Nat.add_le_add_right (ih n) x
  have aggregate (penalty : Validator → Nat)
      (point : ∀ i, actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i -
        ((s.validators.data[i]?).map penalty).getD 0) :
      balanceCredits s t = 0 ∧
      balanceDebits s t ≤ (s.validators.data.toList.map penalty).sum := by
    constructor
    · simp [balanceCredits, point]
    · calc
        balanceDebits s t ≤ ∑ i ∈ Finset.range s.balances.data.size,
            ((s.validators.data[i]?).map penalty).getD 0 := by
          unfold balanceDebits
          apply Finset.sum_le_sum
          intro i _
          rw [point]
          omega
        _ ≤ _ := by
          simpa using sumLookup (s.validators.data.toList.map penalty) s.balances.data.size
  have pointOf (penalty : Validator → Nat)
      (each : ∀ i, (i < s.validators.data.size → ∃ v,
        s.validators.data[i]? = some v ∧
        t.balances.data[i]?.map UInt64.toNat = s.balances.data[i]?.map
          (fun b => b.toNat - penalty v)) ∧
        (s.validators.data.size ≤ i → t.balances.data[i]? = s.balances.data[i]?)) :
      ∀ i, actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i -
        ((s.validators.data[i]?).map penalty).getD 0 := by
    intro i
    -- The slashing pass leaves balances beyond the registry unchanged.
    by_cases inside : i < s.validators.data.size
    · obtain ⟨v, found, h⟩ := (each i).1 inside
      unfold actualBalanceAt
      rw [h, found]
      cases s.balances.data[i]? <;> simp
    · simp [actualBalanceAt, (each i).2 (Nat.le_of_not_gt inside),
        Array.getElem?_eq_none (Nat.le_of_not_gt inside)]
  by_cases electra : .pectra ≤ fork
  · obtain ⟨total, slashed, totalOk, slashedOk, _, each⟩ :=
      processSlashings_balances_toNat_of_electra electra within ok
    let penalty (v : Validator) : Nat :=
      if SlashingPenaltyDue preset (getCurrentEpoch s) v then
        min (slashed.toNat *
          (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat)
          total.toNat / (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
            (v.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      else 0
    refine ⟨(s.validators.data.toList.map penalty).sum, ?_,
      aggregate penalty (pointOf penalty each)⟩
    simp [delayedSlashingLimit, liftAccessor, totalOk, slashedOk, electra, penalty,
      bind, Except.bind, pure, Except.pure, Except.mapError]
  · obtain ⟨total, slashed, totalOk, slashedOk, _, each⟩ :=
      processSlashings_balances_toNat_of_lt_electra (Nat.lt_of_not_le electra) ok
    let penalty (v : Validator) : Nat :=
      if SlashingPenaltyDue preset (getCurrentEpoch s) v then
        v.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          min (slashed.toNat *
            (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat)
            total.toNat / total.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      else 0
    refine ⟨(s.validators.data.toList.map penalty).sum, ?_,
      aggregate penalty (pointOf penalty each)⟩
    simp [delayedSlashingLimit, liftAccessor, totalOk, slashedOk, electra, penalty,
      bind, Except.bind, pure, Except.pure, Except.mapError]

theorem delayed_slashing_limit_zero {fork : Fork} (s : BeaconState preset fork)
    (noneDue : ∀ v ∈ s.validators.data.toList,
      ¬ SlashingPenaltyDue preset (getCurrentEpoch s) v)
    (limit : Nat) (computed : delayedSlashingLimit s = .ok limit) : limit = 0 := by
  unfold delayedSlashingLimit at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨total, _, slashed, _, computed⟩ := computed
  rw [← computed]
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
  simp [noneDue v hv]

theorem sync_reward_bounds {fork : Fork} (s t : BeaconState preset fork)
    (reward proposerReward : Gwei) (proposer : Except AccessorError ValidatorIndex)
    (member : ValidatorIndex × Bool)
    (ok : applySyncReward reward proposerReward proposer s member = .ok t) :
    balanceCredits s t ≤ (if member.2 then reward.toNat + proposerReward.toNat else 0) ∧
    balanceDebits s t ≤ (if member.2 then 0 else reward.toNat) := by
  unfold applySyncReward at ok
  split at ok
  · rename_i signed
    simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨u, first, p, _, last⟩ := ok
    have firstBounds := credits_increase first
    have lastBounds := credits_increase last
    have credits := credits_triangle s u t (sameSizes_increaseBalance last).2
    have debits := debits_triangle s u t (sameSizes_increaseBalance first).2.symm
    simp only [signed, ↓reduceIte]
    omega
  · rename_i absent
    have bounds := debits_decrease (liftAccessor_ok.mp ok)
    simpa [absent] using bounds

/-- Recompute the proposer credit from the newly set participation flags. -/
def attestationCredit {fork : Fork} (s : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) : Except TransitionError Nat := do
  if altair : .altair ≤ fork then
    let earned ← liftAccessor
      (getAttestationParticipationFlagIndices s att.data (s.slot - att.data.slot) parent)
    let participation := if att.data.target.epoch == getCurrentEpoch s then
        s.currentEpochParticipation altair else s.previousEpochParticipation altair
    let total ← liftAccessor (getTotalActiveBalance s)
    let attesters ← liftAccessor (getAttestingIndices s att)
    let (_, numerator) ← attesters.foldlM (addAttesterFlags s total earned) (participation, 0)
    let denominator :=
      (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT
    return (numerator / denominator).toNat
  else return 0

/-- Attestation proposer rewards are the checked numerator divided by the protocol denominator. -/
theorem attestation_proposer_bound {fork : Fork} (s t : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) (early : fork < .glamsterdam)
    (ok : processAttestation config checks s parent att = .ok t) :
    ∃ credit, attestationCredit s att parent = .ok credit ∧
      balanceDebits s t = 0 ∧ balanceCredits s t ≤ credit := by
  by_cases altair : .altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair,
      bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _, total,
      totalOk, attesters, attestersOk, pair, flagsOk, proposer, _, u, raised, final⟩ := ok
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
    simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
    subst t
    refine ⟨(pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat,
      ?_, ?_⟩
    · simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
        attestersOk, Except.mapError, bind, Except.bind, flagsOk]
      rfl
    · have bounds := credits_increase raised
      have kept : (setEpochParticipation s
          (att.data.target.epoch == getCurrentEpoch s) pair.1).balances = s.balances := by
        unfold setEpochParticipation
        split <;> rfl
      simpa only [balanceCredits, balanceDebits, actualBalanceAt, kept]
        using And.intro bounds.2 bounds.1.le
  · obtain ⟨_, _, _, _, _, recorded, _⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) ok
    have kept : t.balances = s.balances := by
      have h := recordPendingAttestation_ok recorded
      split at h <;> have eq := congrArg (fun x => x.balances) h.2 <;> exact eq
    refine ⟨0, by simp [attestationCredit, altair, pure, Except.pure], ?_⟩
    simp [balanceDebits, balanceCredits, actualBalanceAt, kept]

/-- The amount is an input, so top-ups are not silently bounded by activation churn. -/
theorem deposit_credit_bound {fork : Fork} (s t : BeaconState preset fork)
    («matches» : BalancesMatch s)
    (deposit : PendingDeposit) (ok : applyPendingDeposit config checks s deposit = .ok t) :
    balanceDebits s t = 0 ∧ balanceCredits s t ≤ deposit.amount.toNat := by
  have append {t : BeaconState preset fork}
      (balances : t.balances.data = s.balances.data.push deposit.amount) :
      balanceDebits s t = 0 ∧ balanceCredits s t ≤ deposit.amount.toNat := by
    -- Matching lengths makes a new validator append, rather than overwrite, a balance.
    have old (j : Nat) (hj : j < s.balances.data.size) :
        actualBalanceAt ⟨fork, t⟩ j = actualBalanceAt ⟨fork, s⟩ j := by
      simp [actualBalanceAt, balances, Array.getElem?_push, hj, Nat.ne_of_lt hj]
    constructor
    · apply Finset.sum_eq_zero
      intro j hj
      simp [old j (Finset.mem_range.mp hj)]
    · unfold balanceCredits
      have size : t.balances.data.size = s.balances.data.size + 1 := by
        simp [balances]
      rw [size, Finset.sum_range_succ]
      have zero : (∑ j ∈ Finset.range s.balances.data.size,
          (actualBalanceAt ⟨fork, t⟩ j - actualBalanceAt ⟨fork, s⟩ j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [old j (Finset.mem_range.mp hj)]
      rw [zero]
      simp [actualBalanceAt, balances]
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok
      simp [balanceCredits, balanceDebits]
    · simp only [bind, Except.bind] at ok
      split at ok
      · cases ok
      · split at ok
        · exact append (addValidatorToRegistry_push ok «matches»).2
        · cases ok
          simp [balanceCredits, balanceDebits]
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨i, _, added⟩ := ok
    have bounds := credits_increase added
    exact ⟨bounds.2, bounds.1.le⟩

/-- Deposits retained or postponed by the real pass are not charged in this interval. -/
def consumedDeposits {fork : Fork} (s t : BeaconState preset fork) (electra : .pectra ≤ fork) :
    Nat :=
  ((s.pendingDeposits electra).data.toList.map fun d => d.amount.toNat).sum -
    ((t.pendingDeposits electra).data.toList.map fun d => d.amount.toNat).sum

/-- This covers top-ups and withdrawn-key exceptions without charging an unprocessed queue. -/
theorem pending_deposit_bound {fork : Fork} (s t : BeaconState preset fork)
    («matches» : BalancesMatch s)
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    balanceDebits s t = 0 ∧ balanceCredits s t ≤ consumedDeposits s t electra := by
  have fold (ds : List PendingDeposit) (s t : BeaconState preset fork)
      (hm : BalancesMatch s)
      (ok : ds.foldlM (applyPendingDeposit config checks) s = .ok t) :
      balanceDebits s t = 0 ∧
        balanceCredits s t ≤ (ds.map fun d => d.amount.toNat).sum ∧
        s.balances.data.size ≤ t.balances.data.size := by
    induction ds generalizing s with
    | nil =>
      cases ok
      simp [balanceCredits, balanceDebits]
    | cons d ds ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have hu := (applyPendingDeposit_kept first).1 hm
      have sizes : s.balances.data.size ≤ u.balances.data.size := by
        unfold applyPendingDeposit at first
        split at first
        · split at first
          · cases first; exact Nat.le_refl _
          · simp only [bind, Except.bind] at first
            split at first
            · cases first
            · split at first
              · rw [(addValidatorToRegistry_push first hm).2, Array.size_push]
                omega
              · cases first; exact Nat.le_refl _
        · simp only [liftAccessor_ok, bind_ok_iff] at first
          obtain ⟨_, _, first⟩ := first
          exact (sameSizes_increaseBalance first).2.ge
      have a := deposit_credit_bound s u hm d first
      have b := ih u hu last
      have credits := credits_triangle_growing s u t b.2.2
      have debits := debits_triangle_growing s u t sizes
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, sizes.trans b.2.2⟩
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, _, _, _,
    perm, steps, rfl⟩ := processPendingDeposits_applied ok
  have bounds := fold applied s next «matches» steps
  have amounts := (perm.map (fun d => d.amount.toNat)).sum_eq
  -- Postponed deposits return to the queue, so only applied amounts are consumed.
  have consumed : consumedDeposits s
      { next with
        pendingDeposits := fun _ => pending
        depositBalanceToConsume := fun _ => carried } electra =
      (applied.map fun d => d.amount.toNat).sum := by
    unfold consumedDeposits
    rw [queue]
    change _ - (pending.data.toList.map _).sum = _
    rw [kept]
    simp only [List.map_append, List.sum_append] at amounts ⊢
    omega
  rw [consumed]
  exact ⟨bounds.1, bounds.2.1⟩

/-- The real pass removes a prefix; slashed entries are dropped without a transfer. -/
def consumedConsolidations {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) : Nat :=
  (((s.pendingConsolidations electra).data.toList.take
    ((s.pendingConsolidations electra).data.size - (t.pendingConsolidations electra).data.size)).map
      fun c => match s.validators.data[c.sourceIndex.toNat]? with
        | none => 0
        | some v => if v.slashed then 0 else v.effectiveBalance.toNat).sum

/-- Consolidations cannot mint balance, but a target can gain all the source's moved balance. -/
theorem consolidation_transfer_bound {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (ok : processPendingConsolidations s electra = .ok t) :
    totalBalance t = totalBalance s ∧
    balanceCredits s t ≤ consumedConsolidations s t electra ∧
    balanceDebits s t ≤ consumedConsolidations s t electra := by
  let cost (s : BeaconState preset fork) (c : PendingConsolidation) : Nat :=
    match s.validators.data[c.sourceIndex.toNat]? with
    | none => 0
    | some v => if v.slashed then 0 else v.effectiveBalance.toNat
  have pass (cs : List PendingConsolidation) (epoch : Epoch)
      (s t : BeaconState preset fork) (read : Nat)
      (ok : passPendingConsolidations epoch s cs = .ok (t, read)) :
      read ≤ cs.length ∧ t.balances.data.size = s.balances.data.size ∧
      balanceCredits s t ≤ ((cs.take read).map (cost s)).sum ∧
      balanceDebits s t ≤ ((cs.take read).map (cost s)).sum := by
    induction cs generalizing s read with
    | nil =>
      cases ok
      simp [balanceCredits, balanceDebits]
    | cons c cs ih =>
      simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨v, found, ok⟩ := ok
      have found' : s.validators.data[c.sourceIndex.toNat]? = some v := by
        unfold getValidator at found
        split at found <;> cases found
        assumption
      split at ok
      · rename_i slashed
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨⟨u, n⟩, rest, rfl, rfl⟩ := ok
        have later := ih s n rest
        have head : cost s c = 0 := by simp [cost, found', slashed]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, head, Nat.zero_add]
        exact ⟨Nat.succ_le_succ later.1, later.2⟩
      · rename_i notSlashed
        split at ok
        · cases ok
          simp [balanceCredits, balanceDebits]
        · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at ok
          obtain ⟨balance, readBalance, lowered, lower, raised, raise,
            ⟨u, n⟩, rest, rfl, rfl⟩ := ok
          have later := ih raised n rest
          dsimp only at later
          have kept := (increaseBalance_validators raise).trans (decreaseBalance_validators lower)
          -- Transfers keep the registry, so every later cost uses the original effective balance.
          have costs : cost raised = cost s := by simp only [cost, kept]
          rw [costs] at later
          have lo := debits_decrease lower
          have up := credits_increase raise
          have size1 := (sameSizes_decreaseBalance lower).2
          have size2 := (sameSizes_increaseBalance raise).2
          have firstCredits := credits_triangle s lowered raised size2
          have firstDebits := debits_triangle s lowered raised size1.symm
          have nextCredits := credits_triangle s raised u later.2.1
          have nextDebits := debits_triangle s raised u (size2.trans size1).symm
          have cap : (min balance v.effectiveBalance).toNat ≤ v.effectiveBalance.toNat := by
            rw [toNat_min]
            exact Nat.min_le_right _ _
          have head : cost s c = v.effectiveBalance.toNat := by
            simp [cost, found', notSlashed]
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons, head]
          exact ⟨by simpa using Nat.succ_le_succ later.1,
            later.2.1.trans (size2.trans size1), by omega, by omega⟩
  obtain ⟨⟨u, n⟩, processed, balances, queue⟩ := processPendingConsolidations_pass ok
  have facts := pass _ _ s u n processed
  have count : (s.pendingConsolidations electra).data.size -
      (t.pendingConsolidations electra).data.size = n := by
    have lengths := congrArg List.length queue
    simp only [Array.length_toList, List.length_drop] at lengths
    have le := facts.1
    simp only [Array.length_toList] at le
    omega
  refine ⟨(processPendingConsolidations_kept ok).2, ?_, ?_⟩
  · simpa only [consumedConsolidations, count, balanceCredits, actualBalanceAt, balances]
      using facts.2.2.1
  · simpa only [consumedConsolidations, count, balanceDebits, actualBalanceAt, balances]
      using facts.2.2.2

theorem withdrawal_debit_bound {fork : Fork} (s t : BeaconState preset fork)
    (withdrawals : Array Withdrawal) (ok : applyWithdrawals s withdrawals = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤
      (withdrawals.toList.map fun w => w.amount.toNat).sum := by
  have one {s t : BeaconState preset fork} (w : Withdrawal)
      (ok : applyWithdrawal s w = .ok t) :
      balanceCredits s t = 0 ∧ balanceDebits s t ≤ w.amount.toNat := by
    unfold applyWithdrawal at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨builder, _, set⟩ := ok
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      simp [balanceCredits, balanceDebits, actualBalanceAt, BeaconState.putBuilder]
    · exact debits_decrease ok
  have fold (ws : List Withdrawal) (s t : BeaconState preset fork)
      (ok : ws.foldlM applyWithdrawal s = .ok t) :
      balanceCredits s t = 0 ∧
        balanceDebits s t ≤ (ws.map fun w => w.amount.toNat).sum ∧
        t.balances.data.size = s.balances.data.size := by
    induction ws generalizing s with
    | nil =>
      cases ok
      simp [balanceCredits, balanceDebits]
    | cons w ws ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have a := one w first
      have b := ih u last
      have sizes := (sameSizes_applyWithdrawal first).2
      have credits := credits_triangle s u t b.2.2
      have debits := debits_triangle s u t sizes.symm
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, b.2.2.trans sizes⟩
  exact (fold withdrawals.toList s t (by simpa [applyWithdrawals,
    ← Array.foldlM_toList] using ok)).imp_right And.left

theorem excess_queue_debit {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i : ValidatorIndex) (balance : Gwei)
    (read : getBalance s i = .ok balance)
    (ok : queueExcessActiveBalance s electra i = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤
      (balance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  simp only [queueExcessActiveBalance, read, bind_ok_iff, Except.ok.injEq,
    exists_eq_left'] at ok
  split at ok
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨validator, _, pending, _, u, set, rfl⟩ := ok
    have decreased : decreaseBalance s i
        (balance - preset.MIN_ACTIVATION_BALANCE) = .ok u := by
      simp only [decreaseBalance, read, bind, Except.bind]
      have eq : saturatingSub balance (balance - preset.MIN_ACTIVATION_BALANCE) =
          preset.MIN_ACTIVATION_BALANCE := by
        apply UInt64.toNat_inj.mp
        rw [toNat_saturatingSub, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)]
        have := UInt64.lt_iff_toNat_lt.mp above
        omega
      simpa [eq] using set
    have bounds := debits_decrease decreased
    simpa [balanceCredits, balanceDebits, actualBalanceAt,
      UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)] using bounds
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst t
    simp [balanceCredits, balanceDebits]

/-- The crossing queues balance instead of losing it; the debit is counted before later credits. -/
theorem electra_upgrade_debit (s : BeaconState preset .dencun) (t : BeaconState preset .pectra)
    (ok : upgradeToElectra config s = .ok t) :
    (∑ i ∈ Finset.range t.balances.data.size,
      (actualBalanceAt ⟨.pectra, t⟩ i - actualBalanceAt ⟨.dencun, s⟩ i)) = 0 ∧
    (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨.dencun, s⟩ i - actualBalanceAt ⟨.pectra, t⟩ i)) ≤
      ((t.pendingDeposits (by decide)).data.toList.map fun d => d.amount.toNat).sum := by
  let queued (s : BeaconState preset .pectra) :=
    ((s.pendingDeposits (by decide)).data.toList.map fun d => d.amount.toNat).sum
  let bound (s t : BeaconState preset .pectra) :=
    t.balances.data.size = s.balances.data.size ∧ balanceCredits s t = 0 ∧
      balanceDebits s t + queued s ≤ queued t
  -- Each upgrade pass pays for its debit by appending the same amount to the queue.
  have excess (s t : BeaconState preset .pectra) (i : ValidatorIndex)
      (ok : queueExcessActiveBalance s (by decide) i = .ok t) : bound s t := by
    have read : ∃ b, getBalance s i = .ok b := by
      have steps := ok
      simp only [queueExcessActiveBalance, bind_ok_iff] at steps
      obtain ⟨b, read, _⟩ := steps
      exact ⟨b, read⟩
    obtain ⟨b, read⟩ := read
    have bounds := excess_queue_debit s t (by decide) i b read ok
    obtain ⟨_, added, queue, amount⟩ := queueExcessActiveBalance_balance read ok
    have sum : queued t = queued s + (added.map fun d => d.amount.toNat).sum := by
      simp only [queued, queue, List.map_append, List.sum_append]
    have minimum : (min b preset.MIN_ACTIVATION_BALANCE).toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat := by
      rw [toNat_min]
      exact Nat.min_le_right _ _
    exact ⟨(sameSizes_queueExcessActiveBalance ok).2, bounds.1, by omega⟩
  have pre (s t : BeaconState preset .pectra) (i : ValidatorIndex)
      (ok : queuePreActivation s (by decide) i = .ok t) : bound s t := by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨v, _, b, read, pending, appended, u, setBalance, w, setValidator, rfl⟩ := ok
    have decreased : decreaseBalance s i b = .ok u := by
      simpa [decreaseBalance, read, bind, Except.bind, saturatingSub] using setBalance
    have bounds := debits_decrease decreased
    have size := (sameSizes_decreaseBalance decreased).2
    obtain ⟨_, rfl⟩ := setValidator_ok setValidator
    have sum : (pending.data.toList.map fun d => d.amount.toNat).sum = queued s + b.toNat := by
      rw [appendWithinLimit_data appended]
      simp [queued]
    refine ⟨size, bounds.1, ?_⟩
    change balanceDebits s u + queued s ≤ _
    change balanceDebits s u + queued s ≤
      (pending.data.toList.map fun d => d.amount.toNat).sum
    omega
  have compound (s t : BeaconState preset .pectra) (i : Nat)
      (ok : queueCompoundingExcess s (by decide) i = .ok t) : bound s t := by
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · exact excess s t _ (liftAccessor_ok.mp ok)
      · cases ok
        simp [bound, balanceCredits, balanceDebits]
    · cases ok
      simp [bound, balanceCredits, balanceDebits]
  have fold {α : Type} (f : BeaconState preset .pectra → α →
      Except TransitionError (BeaconState preset .pectra))
      (step : ∀ s t a, f s a = .ok t → bound s t)
      (xs : List α) (s t : BeaconState preset .pectra)
      (ok : xs.foldlM f s = .ok t) : bound s t := by
    induction xs generalizing s with
    | nil => cases ok; simp [bound, balanceCredits, balanceDebits]
    | cons x xs ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have a := step s u x first
      have b := ih u last
      have credits := credits_triangle s u t b.1
      have debits := debits_triangle s u t a.1.symm
      exact ⟨b.1.trans a.1, by omega, by omega⟩
  simp only [upgradeToElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨activationExit, _, earliestExit, _, exitChurn, _, consolidationChurn, _,
    u, first, last⟩ := ok
  have firstBound := fold _ pre _ _ u first
  have lastBound := fold _ compound _ u t last
  have trans {s u t : BeaconState preset .pectra} (a : bound s u) (b : bound u t) :
      bound s t := by
    have credits := credits_triangle s u t b.1
    have debits := debits_triangle s u t a.1.symm
    exact ⟨b.1.trans a.1, by omega, by omega⟩
  have combined := trans firstBound lastBound
  have before : ¬ Fork.pectra ≤ Fork.dencun := by decide
  simpa [bound, queued, balanceCredits, balanceDebits, actualBalanceAt,
    carryFields, carryList, before] using combined.2

/-- The proposer search reads only the effective balances of the validators it draws.

Each candidate is one of the indices, or index zero when the order leaves them. -/
private theorem proposerSearch_congr_validators {fork : Fork} {first second : Array Validator}
    {indices : Array ValidatorIndex} {order : Nat → Nat} {seed : Bytes32}
    (positive : 0 < first.size) (inside : ∀ index ∈ indices, index.toNat < first.size)
    (agree : ∀ j < first.size, (first[j]?).map (·.effectiveBalance) =
      (second[j]?).map (·.effectiveBalance)) :
    ∀ {i : Nat}, proposerSearch preset fork first indices order seed i =
      proposerSearch preset fork second indices order seed i := by
  intro i
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
    unfold proposerSearch
    have small : (indices.getD (order (i % indices.size)) 0).toNat < first.size := by
      rw [Array.getD_eq_getD_getElem?]
      by_cases within : order (i % indices.size) < indices.size
      · rw [Array.getElem?_eq_getElem within, Option.getD_some]
        exact inside _ (Array.getElem_mem within)
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt within), Option.getD_none]
        exact positive
    have same := agree _ small
    generalize indices.getD (order (i % indices.size)) 0 = candidate at same ⊢
    cases hf : first[candidate.toNat]? <;> cases hs : second[candidate.toNat]? <;>
      simp only [hf, hs, Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq] at same
    · simp only [hf, hs]
    · simp only [hf, hs, same]
      by_cases next : i + 1 < 2 ^ 64
      · rw [ih (2 ^ 64 - (i + 1)) (by omega) rfl]
      · have far : ¬ i + 1 < 18446744073709551616 := by omega
        simp only [far, dite_false]

/-- The proposer of a slot reads the slot, the RANDAO mixes and the proposer lookahead.

It also reads the active validators of the epoch and their effective balances. -/
private theorem getBeaconProposerIndex_congr {fork : Fork} {s w : BeaconState preset fork}
    (slot : w.slot = s.slot) (mixes : w.randaoMixes = s.randaoMixes)
    (lookahead : ∀ fulu : .fusaka ≤ fork, w.proposerLookahead fulu = s.proposerLookahead fulu)
    (active : getActiveValidatorIndicesChecked w (getCurrentEpoch s) =
      getActiveValidatorIndicesChecked s (getCurrentEpoch s))
    (effective : ∀ j < s.validators.data.size, (s.validators.data[j]?).map (·.effectiveBalance) =
      (w.validators.data[j]?).map (·.effectiveBalance)) :
    getBeaconProposerIndex w = getBeaconProposerIndex s := by
  have epoch : getCurrentEpoch w = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  unfold getBeaconProposerIndex
  split
  · rename_i fulu
    simp only [slot, lookahead fulu]
  · have seed : getSeed w (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER =
        getSeed s (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER := by
      unfold getSeed getRandaoMix
      rw [mixes]
    dsimp only
    rw [epoch, seed, active, slot]
    cases checked : getActiveValidatorIndicesChecked s (getCurrentEpoch s) with
    | error => simp only [bind, Except.bind]
    | ok indices =>
      simp only [bind, Except.bind]
      cases getSeed s (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER with
      | error => simp only
      | ok mix =>
        simp only
        unfold computeProposerIndex
        by_cases empty : indices.toArray.size = 0
        · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
            MonadExceptOf.throw]
        have inside : ∀ index ∈ indices.toArray, index.toNat < s.validators.data.size := by
          intro index member
          obtain ⟨v, found, _⟩ :=
            (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp (by simpa using member)
          exact (Array.getElem?_eq_some_iff.mp found).1
        have positive : 0 < s.validators.data.size := by
          obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil indices
            (fun nil => empty (by simp [nil]))
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) (inside index (by simpa using member))
        simp only [empty, ↓reduceIte]
        rw [proposerSearch_congr_validators positive inside effective]

/-! ## The balance ledger of a block -/

/-- How the balances move from one state to another, read at each validator.

A balance rises by at most its participant sync amount and its other credits.

Off the paid and converted validators, a balance falls by at most the sum of two amounts.

These are its participant sync amount and its slashing penalty.

A converted validator falls only to the activation balance, and then rises by its credits.

Off the converted validators, whether the credentials compound stays.

A converted validator did not compound before, and compounds after. -/
private structure Ledger {fork : Fork} (s t : BeaconState preset fork)
    (paid conv : Finset ValidatorIndex) (sync other slash : ValidatorIndex → ℕ) : Prop where
  up : ∀ v, actualBalanceAt ⟨fork, t⟩ v.toNat ≤
    actualBalanceAt ⟨fork, s⟩ v.toNat + sync v + other v
  down : ∀ v, v ∉ paid → v ∉ conv →
    actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat + sync v + slash v
  converted : ∀ v ∈ conv, actualBalanceAt ⟨fork, t⟩ v.toNat ≤
    preset.MIN_ACTIVATION_BALANCE.toNat + sync v + other v
  lowered : ∀ v ∈ conv, v ∉ paid → min (actualBalanceAt ⟨fork, s⟩ v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat + sync v + slash v
  kept : ∀ (v : ValidatorIndex) validator, v ∉ conv → s.validators.data[v.toNat]? = some validator →
    ∃ later, t.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator
  fresh : ∀ v ∈ conv, ∀ validator, s.validators.data[v.toNat]? = some validator →
    hasCompoundingWithdrawalCredential validator = false
  switched : ∀ v ∈ conv, ∃ later, t.validators.data[v.toNat]? = some later ∧
    hasCompoundingWithdrawalCredential later = true

private theorem Ledger.trans {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv paid' conv' : Finset ValidatorIndex} {sync other slash sync' other' slash' :
      ValidatorIndex → ℕ}
    (one : Ledger s u paid conv sync other slash)
    (two : Ledger u t paid' conv' sync' other' slash') :
    Ledger s t (paid ∪ paid') (conv ∪ conv') (sync + sync') (other + other') (slash + slash') where
  up v := by have := one.up v; have := two.up v; simp only [Pi.add_apply]; omega
  down v notPaid notConv := by
    simp only [Finset.mem_union, not_or] at notPaid notConv
    have := one.down v notPaid.1 notConv.1
    have := two.down v notPaid.2 notConv.2
    simp only [Pi.add_apply]; omega
  converted v member := by
    simp only [Pi.add_apply]
    rcases Finset.mem_union.mp member with first | second
    · have := one.converted v first; have := two.up v; omega
    · have := two.converted v second; omega
  lowered v member notPaid := by
    simp only [Pi.add_apply]
    simp only [Finset.mem_union, not_or] at notPaid
    -- No validator is converted twice: the first conversion makes it compound.
    have apart : v ∈ conv → v ∉ conv' := by
      intro first second
      obtain ⟨later, found, compounds⟩ := one.switched v first
      rw [two.fresh v second later found] at compounds
      cases compounds
    rcases Finset.mem_union.mp member with first | second
    · have := one.lowered v first notPaid.1
      have := two.down v notPaid.2 (apart first)
      omega
    · have first : v ∉ conv := fun first => apart first second
      have := one.down v notPaid.1 first
      have := two.lowered v second notPaid.2
      omega
  kept v validator notConv found := by
    simp only [Finset.mem_union, not_or] at notConv
    obtain ⟨middle, middleFound, same⟩ := one.kept v validator notConv.1 found
    obtain ⟨later, laterFound, same'⟩ := two.kept v middle notConv.2 middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  fresh v member validator found := by
    rcases Finset.mem_union.mp member with first | second
    · exact one.fresh v first validator found
    · by_cases converted : v ∈ conv
      · exact one.fresh v converted validator found
      · obtain ⟨middle, middleFound, same⟩ := one.kept v validator converted found
        rw [← same]
        exact two.fresh v second middle middleFound
  switched v member := by
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨middle, middleFound, compounds⟩ := one.switched v first
      by_cases again : v ∈ conv'
      · exact two.switched v again
      · obtain ⟨later, laterFound, same⟩ := two.kept v middle again middleFound
        exact ⟨later, laterFound, same.trans compounds⟩
    · exact two.switched v second

/-- A step that keeps every balance and whether each existing validator compounds. -/
private theorem Ledger.of_kept {fork : Fork} {s t : BeaconState preset fork}
    (balances : t.balances.data = s.balances.data)
    (kept : ∀ (v : ValidatorIndex) validator, s.validators.data[v.toNat]? = some validator →
      ∃ later, t.validators.data[v.toNat]? = some later ∧
        hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator) :
    Ledger s t ∅ ∅ 0 0 0 where
  up v := by simp [actualBalanceAt, balances]
  down v _ _ := by simp [actualBalanceAt, balances]
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := kept v validator found
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- A step that keeps every balance and every validator. -/
private theorem Ledger.of_eq {fork : Fork} {s t : BeaconState preset fork}
    (balances : t.balances.data = s.balances.data)
    (validators : t.validators.data = s.validators.data) : Ledger s t ∅ ∅ 0 0 0 :=
  Ledger.of_kept balances fun v validator found =>
    ⟨validator, by rw [validators]; exact found, rfl⟩

private theorem Ledger.refl {fork : Fork} (s : BeaconState preset fork) : Ledger s s ∅ ∅ 0 0 0 :=
  Ledger.of_eq rfl rfl

/-- A ledger with larger sets and amounts. -/
private theorem Ledger.mono {fork : Fork} {s t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash other' slash' : ValidatorIndex → ℕ}
    (ledger : Ledger s t paid conv sync other slash) (paid' : Finset ValidatorIndex)
    (morePaid : paid ⊆ paid') (moreOther : ∀ v, other v ≤ other' v)
    (moreSlash : ∀ v, slash v ≤ slash' v) : Ledger s t paid' conv sync other' slash' where
  up v := by have := ledger.up v; have := moreOther v; omega
  down v notPaid notConv := by
    have := ledger.down v (fun member => notPaid (morePaid member)) notConv
    have := moreSlash v; omega
  converted v member := by have := ledger.converted v member; have := moreOther v; omega
  lowered v member notPaid := by
    have := ledger.lowered v member (fun inside => notPaid (morePaid inside))
    have := moreSlash v; omega
  kept := ledger.kept
  fresh := ledger.fresh
  switched := ledger.switched

private theorem Ledger.zero_left {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (one : Ledger s u ∅ ∅ 0 0 0) (two : Ledger u t paid conv sync other slash) :
    Ledger s t paid conv sync other slash := by
  simpa using one.trans two

private theorem Ledger.zero_right {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (one : Ledger s u paid conv sync other slash) (two : Ledger u t ∅ ∅ 0 0 0) :
    Ledger s t paid conv sync other slash := by
  simpa using one.trans two

/-- The seats of a validator in the current sync committee: the members that hold its key. -/
private def seatsOf {fork : Fork} (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (v : ValidatorIndex) : ℕ :=
  ((s.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
    (s.validators.data[v.toNat]?).any (·.pubkey == key)).length

/-! ### The steps of a block, one by one -/

section Steps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem ledger_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Ledger.of_eq rfl rfl

private theorem ledger_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact Ledger.of_eq rfl rfl

private theorem ledger_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact Ledger.of_eq (by rw [← rest]) (by rw [← rest])

/-- Applying the expected withdrawals keeps the registry of validators. -/
private theorem applyExpectedWithdrawals_validators {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals s capella expected = .ok t) :
    t.validators = s.validators := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : applied.validators = s.validators := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM_ok_invariant (fun x : BeaconState preset fork => x.validators = s.validators)
      (fun _ _ _ same ok => by rw [applyWithdrawal_eq ok]; exact same) rfl appliedOk
  have two : indexed.validators = applied.validators := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk
      rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → finished.validators = kept.validators := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        rfl
    · cases ok
      rfl
  have three := swept _ sweptOk
  have queued : (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed).validators = indexed.validators := by
    split <;> split <;> rfl
  have four : t.validators = finished.validators := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      rfl
  rw [four, three, queued, two, one]

/-- Before Gloas, the withdrawal step pays only some validators.

These are the validators that the withdrawals of the payload name. -/
private theorem ledger_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)} (early : fork < .glamsterdam)
    (computed : processWithdrawals s capella payload = .ok t) :
    Ledger s t (((payload early).withdrawals capella).data.toList.map (·.validatorIndex)).toFinset
      ∅ 0 0 0 := by
  obtain ⟨expected, -, -, appliedOk⟩ := processWithdrawals_expected early computed
  have validators := applyExpectedWithdrawals_validators appliedOk
  have sizes := (sameSizes_processWithdrawals computed).2
  have balance : ∀ v : ValidatorIndex, actualBalanceAt ⟨fork, t⟩ v.toNat =
      actualBalanceAt ⟨fork, s⟩ v.toNat -
        withdrawnFrom ((payload early).withdrawals capella).data v := by
    intro v
    cases found : s.balances.data[v.toNat]? with
    | none =>
      have missing : t.balances.data[v.toNat]? = none := by
        rw [Array.getElem?_eq_none_iff] at found ⊢
        omega
      simp [actualBalanceAt, found, missing]
    | some balance =>
      have lowered := processWithdrawals_balance early computed found
      cases later : t.balances.data[v.toNat]? <;> simp_all [actualBalanceAt]
  exact {
    up := fun v => by simp only [balance v, Pi.zero_apply]; omega
    down := fun v notPaid _ => by
      rw [balance v, withdrawnFrom_eq_zero fun w member same =>
        notPaid (List.mem_toFinset.mpr (List.mem_map.mpr ⟨w, member, same⟩))]
      simp
    converted := fun v member => absurd member (Finset.notMem_empty v)
    lowered := fun v member => absurd member (Finset.notMem_empty v)
    kept := fun v validator _ found => ⟨validator, by rw [validators]; exact found, rfl⟩
    fresh := fun v member => absurd member (Finset.notMem_empty v)
    switched := fun v member => absurd member (Finset.notMem_empty v) }

/-- The withdrawals of a payload pay at most as many validators as the payload has withdrawals. -/
private theorem ledger_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ paid : Finset ValidatorIndex, Ledger s t paid ∅ 0 0 0 ∧
      paid.card ≤ if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0 := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at computed
  split at computed
  · rename_i capella
    simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    have ledger := (ledger_processWithdrawals early withdrawnOk).trans
      (Ledger.of_eq (t := { middle with latestExecutionPayloadHeader := fun _ => header })
        rfl rfl)
    rw [Finset.union_empty, Finset.union_empty, add_zero] at ledger
    refine ⟨_, ledger, ?_⟩
    simp only [capella, ↓reduceIte]
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, Array.length_toList]
    exact ((body.executionPayload _).withdrawals capella).bound early
  · rename_i capella
    simp only [capella, ↓reduceIte, nonpos_iff_eq_zero, Finset.card_eq_zero, exists_eq_right]
    split at computed
    · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
      exact Ledger.of_eq rfl rfl
    · cases computed
      exact Ledger.refl s

/-- A balance increase adds its amount at its own index and keeps every other balance. -/
private theorem actualBalanceAt_increaseBalance {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j + if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, _, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨raised, located, value⟩ := balance_increaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]

/-- A balance decrease subtracts its amount at its own index and keeps every other balance. -/
private theorem actualBalanceAt_decreaseBalance {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j - if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨lowered, located, value⟩ := balance_decreaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]
    split <;> omega

/-- Replace a validator by one with the same credentials.

This keeps the credentials of every validator. -/
private theorem credentials_setValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {old new : Validator} (found : getValidator u index = .ok old)
    (set : u.setValidator index new = .ok w)
    (same : new.withdrawalCredentials = old.withdrawalCredentials) (j : ValidatorIndex)
    (before : Validator) (read : getValidator u j = .ok before) :
    ∃ later, getValidator w j = .ok later ∧
      later.withdrawalCredentials = before.withdrawalCredentials := by
  by_cases equal : j = index
  · subst equal
    have := Except.ok.inj (read.symm.trans found)
    subst this
    exact ⟨new, getValidator_setValidator_self set, same⟩
  · exact ⟨before, (getValidator_setValidator_of_ne set equal).trans read, rfl⟩

/-- Slashing a validator keeps the withdrawal credentials of every validator. -/
private theorem credentials_slashValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config u index whistleblower = .ok w) (j : ValidatorIndex)
    (before : Validator) (read : u.validators.data[j.toNat]? = some before) :
    ∃ later, w.validators.data[j.toNat]? = some later ∧
      later.withdrawalCredentials = before.withdrawalCredentials := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitOk,
    validatorOk, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok computed
  have exitedRead : ∃ middle, getValidator exited j = .ok middle ∧
      middle.withdrawalCredentials = before.withdrawalCredentials := by
    obtain ⟨old, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
      initiateValidatorExit_ok exitOk
    · exact ⟨before, getValidator_eq_ok_iff.mpr read, rfl⟩
    · have same := getValidator_of_validators_eq (exitQueue_validators queue).1
      exact credentials_setValidator ((same index).trans found) set rfl j before
        ((same j).trans (getValidator_eq_ok_iff.mpr read))
  obtain ⟨middle, middleRead, middleSame⟩ := exitedRead
  obtain ⟨later, laterRead, laterSame⟩ :=
    credentials_setValidator validatorOk markedOk rfl j middle middleRead
  have registry : w.validators = marked.validators := by
    have cancelled := slashValidator_last (last := last) (after := w) (index := index)
      (by subst done; rfl)
    rw [cancelled.1, increaseBalance_validators lastOk, increaseBalance_validators raisedOk,
      decreaseBalance_validators loweredOk]
  refine ⟨later, ?_, laterSame.trans middleSame⟩
  rw [registry]
  exact getValidator_eq_ok_iff.mp laterRead

/-- A state reads the same proposer as an earlier state when it keeps four things of it.

These are the slot, the payload inputs, activity and effective balances. -/
private theorem getBeaconProposerIndex_of_kept {r w : BeaconState preset fork}
    (keeps : StepKeeps r w) (inputs : PayloadInputs r w) (effective : EffectiveKept r w) :
    getBeaconProposerIndex w = getBeaconProposerIndex r := by
  apply getBeaconProposerIndex_congr inputs.slot inputs.randaoMixes
    (fun fulu => by rw [inputs.proposerLookahead])
    (keeps.2.2.getActiveValidatorIndicesChecked_eq (getCurrentEpoch_le_activityFixedEpoch r))
  intro j inside
  have same := effective j inside
  have inside' := Nat.lt_of_lt_of_le inside keeps.1
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside',
    Option.map_some, Option.getD_some] at same
  rw [Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside', Option.map_some,
    Option.map_some, UInt64.toNat_inj.mp same]

/-- A slashing with the proposer as whistleblower debits the slashed validator its initial penalty.

It credits the whistleblower reward to the proposer that an earlier kept state reads. -/
private theorem ledger_slashValidator {r u w : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (early : fork < .glamsterdam)
    (keeps : StepKeeps r u) (inputs : PayloadInputs r u) (effective : EffectiveKept r u)
    (found : u.validators.data[index.toNat]? = some validator)
    (computed : slashValidator config u index none = .ok w) :
    ∃ proposer, getBeaconProposerIndex r = .ok proposer ∧
      Ledger u w ∅ ∅ 0
        (fun v => if v = proposer then validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v = index then validator.effectiveBalance.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  obtain ⟨exited, current, _, marked, _, _, slashings, lowered, proposer, reward, raised, last,
    exitOk, currentOk, _, markedOk, _, _, _, lowerOk, proposerOk, share, raiseOk, lastOk,
    final⟩ := slashValidator_ok computed
  have inside : index.toNat < u.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have sameEffective : current.effectiveBalance = validator.effectiveBalance := by
    have kept := effectiveKept_exit exitOk index.toNat inside
    simp only [effectiveAt, getValidator_eq_ok_iff.mp currentOk, found, Option.map_some,
      Option.getD_some] at kept
    exact UInt64.toNat_inj.mp kept
  -- The proposer is read after the exit, the slashed mark, the slashings write and the debit.
  have exitGrows := (frame_initiateValidatorExit exitOk).registryGrows
  have markedSize := (sameSizes_setValidator markedOk).1
  have keepsLowered : StepKeeps r lowered :=
    ((keeps.trans (stepKeeps_initiateValidatorExit exitOk)).trans
      ((stepKeeps_setValidator currentOk (fun _ _ => by rfl) markedOk).trans
        (StepKeeps.of_validators (state := marked) (after := { marked with slashings })))).trans
      (stepKeeps_decreaseBalance lowerOk)
  have inputsLowered : PayloadInputs r lowered :=
    ((inputs.trans (payloadInputs_initiateValidatorExit exitOk)).trans
      ((payloadInputs_setValidator markedOk).trans
        (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :
          PayloadInputs marked { marked with slashings }))).trans
      (payloadInputs_decreaseBalance lowerOk)
  have effectiveLowered : EffectiveKept r lowered :=
    effectiveKept_trans effective
      (effectiveKept_trans
        (effectiveKept_trans (effectiveKept_exit exitOk)
          (effectiveKept_setValidator currentOk markedOk rfl) exitGrows)
        (effectiveKept_trans (effectiveKept_data (s := marked) (t := { marked with slashings }))
          (effectiveKept_decrease lowerOk) (Nat.le_refl _))
        (exitGrows.trans (Nat.le_of_eq markedSize.symm)))
      keeps.1
  have proposerRead : getBeaconProposerIndex r = .ok proposer := by
    rw [← getBeaconProposerIndex_of_kept keepsLowered inputsLowered effectiveLowered]
    exact proposerOk
  refine ⟨proposer, proposerRead, ?_⟩
  -- The balances move only by the debit and the two credits.
  have exitBalances : exited.balances = u.balances := by
    obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok exitOk
    · rfl
    · obtain ⟨_, rfl⟩ := setValidator_ok set
      exact (exitQueue_validators queue).2
  have markedBalances : marked.balances = u.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    exact exitBalances
  have shareLe : reward.toNat ≤
      (current.effectiveBalance /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    unfold proposerShare at share
    split at share
    · simp only [bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq] at share
      obtain ⟨product, productOk, rfl⟩ := share
      have productEq := (mulChecked_ok_iff.mp productOk).2
      rw [UInt64.toNat_div, productEq]
      change _ * 8 / 64 ≤ _
      omega
    · simp only [pure, Except.pure, Except.ok.injEq] at share
      subst reward
      exact Nat.div_le_self _ _
  have leftReward : (current.effectiveBalance /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT - reward).toNat =
        (current.effectiveBalance /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat - reward.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at final
  subst w
  have point (v : ValidatorIndex) :
      actualBalanceAt ⟨fork, last⟩ v.toNat =
        (actualBalanceAt ⟨fork, u⟩ v.toNat - if v = index then
          validator.effectiveBalance.toNat /
            (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) +
          (if v = proposer then reward.toNat else 0) +
          (if v = proposer then validator.effectiveBalance.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - reward.toNat
            else 0) := by
    rw [actualBalanceAt_increaseBalance lastOk, actualBalanceAt_increaseBalance raiseOk,
      actualBalanceAt_decreaseBalance lowerOk, leftReward]
    have start : actualBalanceAt ⟨fork, { marked with slashings }⟩ v.toNat =
        actualBalanceAt ⟨fork, u⟩ v.toNat := by
      simp only [actualBalanceAt, markedBalances]
    simp only [start, Option.getD_none, UInt64.toNat_inj, eq_comm (a := index),
      eq_comm (a := proposer), UInt64.toNat_div, sameEffective]
  have shareLe' : reward.toNat ≤ validator.effectiveBalance.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    simpa only [UInt64.toNat_div, sameEffective] using shareLe
  exact {
    up := fun v => by
      rw [point v]
      simp only [Pi.zero_apply]
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = penalty at *
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = whistle at *
      split_ifs <;> omega
    down := fun v _ _ => by
      rw [point v]
      simp only [Pi.zero_apply]
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = penalty at *
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = whistle at *
      split_ifs <;> omega
    converted := fun v member => absurd member (Finset.notMem_empty v)
    lowered := fun v member => absurd member (Finset.notMem_empty v)
    kept := fun v before _ read => by
      obtain ⟨later, laterRead, same⟩ := credentials_slashValidator computed v before read
      exact ⟨later, laterRead, by simp only [hasCompoundingWithdrawalCredential, same]⟩
    fresh := fun v member => absurd member (Finset.notMem_empty v)
    switched := fun v member => absurd member (Finset.notMem_empty v) }

/-- A proposer slashing debits the slashed validator its initial penalty.

The penalty is read at the effective balance of that validator.

The slashing credits the whistleblower reward to the proposer of the slot. -/
private theorem ledger_processProposerSlashing {slashing : ProposerSlashing}
    (early : fork < .glamsterdam)
    (computed : processProposerSlashing config checks s slashing = .ok t) :
    ∃ (proposer slashed : ValidatorIndex) (validator : Validator),
      getBeaconProposerIndex s = .ok proposer ∧
      s.validators.data[slashed.toNat]? = some validator ∧ validator.slashed = false ∧
      (∃ later, t.validators.data[slashed.toNat]? = some later ∧ later.slashed = true) ∧
      Ledger s t ∅ ∅ 0
        (fun v => if v = proposer then validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v = slashed then validator.effectiveBalance.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, validator, found, _, slashable, _, _, _, _, slashed⟩ := computed
  have read := getValidator_eq_ok_iff.mp found
  obtain ⟨proposer, proposerRead, ledger⟩ := ledger_slashValidator early (StepKeeps.refl s)
    (PayloadInputs.refl s) (effectiveKept_refl s) read slashed
  refine ⟨proposer, _, validator, proposerRead, read, ?_, ?_, ledger⟩
  · simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
    exact slashable.1.1
  · have flag := (slashValidator_slashedFlag slashed).1
    cases later : t.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? with
    | none => simp [slashedFlag, getValidator, later, Except.map] at flag
    | some entry =>
      simp only [slashedFlag, getValidator, later, Except.map, Except.ok.injEq] at flag
      exact ⟨entry, rfl, flag⟩

/-- Take a state that keeps what the proposer of an earlier state reads.

From it, slashing each slashable index of a list in turn debits each slashed validator.

It also credits the proposer of the earlier state. -/
private theorem ledger_foldSlashIfSlashable {r : BeaconState preset fork}
    (early : fork < .glamsterdam) (chosen : ValidatorIndex)
    (choice : ∀ p, getBeaconProposerIndex r = .ok p → p = chosen) :
    ∀ (indices : List ValidatorIndex) {u w : BeaconState preset fork} {flag flag' : Bool},
      StepKeeps r u → PayloadInputs r u → EffectiveKept r u →
      u.validators.data.size = r.validators.data.size →
      indices.foldlM (slashIfSlashable config) (u, flag) = .ok (w, flag') →
      ∃ slashed : Finset ValidatorIndex,
        (slashed.Nonempty → getBeaconProposerIndex r = .ok chosen) ∧
        (∀ v ∈ slashed, ∃ validator later, u.validators.data[v.toNat]? = some validator ∧
          validator.slashed = false ∧ w.validators.data[v.toNat]? = some later ∧
          later.slashed = true) ∧
        Ledger u w ∅ ∅ 0
          (fun v => if v = chosen then ∑ x ∈ slashed, effectiveAt ⟨fork, r⟩ x.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
          (fun v => if v ∈ slashed then effectiveAt ⟨fork, r⟩ v.toNat /
            (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0)
  | [], u, w, flag, flag', _, _, _, _, ok => by
    cases ok
    refine ⟨∅, fun empty => absurd empty Finset.not_nonempty_empty,
      fun v member => absurd member (Finset.notMem_empty v), ?_⟩
    exact (Ledger.refl u).mono ∅ (subset_refl _) (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
  | index :: rest, u, w, flag, flag', keeps, inputs, effective, size, ok => by
    obtain ⟨⟨middle, nextFlag⟩, first, tail⟩ := bind_ok_iff.mp ok
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨validator, found, first⟩ := first
    split at first
    · rename_i slashable
      simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at first
      obtain ⟨next, slashed, rfl, rfl⟩ := first
      have read := getValidator_eq_ok_iff.mp found
      obtain ⟨proposer, proposerRead, one⟩ :=
        ledger_slashValidator early keeps inputs effective read slashed
      rw [choice proposer proposerRead] at one proposerRead
      obtain ⟨set, _, marks, two⟩ := ledger_foldSlashIfSlashable early chosen choice rest
        (keeps.trans (stepKeeps_slashValidator slashed))
        (inputs.trans (payloadInputs_slashValidator slashed))
        (effectiveKept_trans effective (effectiveKept_slash slashed) keeps.1)
        ((sameSizes_slashValidator slashed).1.trans size) tail
      have flagNext := slashValidator_slashedFlag slashed
      -- Each later member is unslashed when its fold starts, while this index is slashed by now.
      have fresh : index ∉ set := by
        intro member
        obtain ⟨entry, _, entryRead, entrySlashed, _⟩ := marks index member
        have marked := flagNext.1
        simp [slashedFlag, getValidator, entryRead, Except.map, entrySlashed] at marked
      have unslashed : validator.slashed = false := by
        simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
        exact slashable.1.1
      have effectiveIndex : effectiveAt ⟨fork, r⟩ index.toNat =
          validator.effectiveBalance.toNat := by
        rw [← effective index.toNat (size ▸ (Array.getElem?_eq_some_iff.mp read).1)]
        simp [effectiveAt, read]
      refine ⟨insert index set, fun _ => proposerRead, ?_, ?_⟩
      · intro v member
        rcases Finset.mem_insert.mp member with rfl | inside
        · have persist := (foldlM_slashIfSlashable rest tail).2.1 v flagNext.1
          cases later : w.validators.data[v.toNat]? with
          | none => simp [slashedFlag, getValidator, later, Except.map] at persist
          | some entry =>
            simp only [slashedFlag, getValidator, later, Except.map, Except.ok.injEq] at persist
            exact ⟨validator, entry, read, unslashed, rfl, persist⟩
        · obtain ⟨entry, later, entryRead, entrySlashed, laterRead, laterSlashed⟩ :=
            marks v inside
          have apart : v ≠ index := fun equal => fresh (equal ▸ inside)
          have before := flagNext.2 v apart
          cases old : u.validators.data[v.toNat]? with
          | none => simp [slashedFlag, getValidator, old, entryRead, Except.map] at before
          | some original =>
            simp [slashedFlag, getValidator, old, entryRead, Except.map, entrySlashed] at before
            exact ⟨original, later, rfl, before, laterRead, laterSlashed⟩
      · have both := one.trans two
        rw [add_zero] at both
        refine both.mono ∅ (subset_refl _) (fun v => ?_) (fun v => ?_)
        · simp only [Pi.add_apply, Finset.sum_insert fresh, effectiveIndex]
          split_ifs <;> omega
        · simp only [Pi.add_apply, Finset.mem_insert]
          by_cases equal : v = index
          · subst equal
            simp [fresh, effectiveIndex]
          · simp [equal]
    · cases first
      exact ledger_foldSlashIfSlashable early chosen choice rest keeps inputs effective size tail

/-- An attester slashing slashes some validators, each not slashed before.

It debits each its initial penalty and credits the whistleblower rewards to the proposer. -/
private theorem ledger_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (early : fork < .glamsterdam)
    (computed : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ (proposer : ValidatorIndex) (slashed : Finset ValidatorIndex),
      (slashed.Nonempty → getBeaconProposerIndex s = .ok proposer) ∧
      (∀ v ∈ slashed, ∃ validator later, s.validators.data[v.toNat]? = some validator ∧
        validator.slashed = false ∧ t.validators.data[v.toNat]? = some later ∧
        later.slashed = true) ∧
      Ledger s t ∅ ∅ 0
        (fun v => if v = proposer then ∑ x ∈ slashed, effectiveAt ⟨fork, s⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v ∈ slashed then effectiveAt ⟨fork, s⟩ v.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := computed
  obtain ⟨chosen, choice⟩ : ∃ chosen : ValidatorIndex,
      ∀ p, getBeaconProposerIndex s = .ok p → p = chosen := by
    cases read : getBeaconProposerIndex s with
    | ok p => exact ⟨p, fun q found => (Except.ok.inj found).symm⟩
    | error _ => exact ⟨0, fun q found => by cases found⟩
  obtain ⟨slashed, nonempty, marks, ledger⟩ := ledger_foldSlashIfSlashable early chosen choice _
    (StepKeeps.refl s) (PayloadInputs.refl s) (effectiveKept_refl s) rfl folded
  exact ⟨chosen, slashed, nonempty, marks, ledger⟩

/-- A step that keeps every validator, lowers no balance and raises each by at most its credit. -/
private theorem Ledger.of_rise {other : ValidatorIndex → ℕ}
    (validators : t.validators.data = s.validators.data)
    (rise : ∀ v : ValidatorIndex, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
      actualBalanceAt ⟨fork, t⟩ v.toNat ∧
      actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat + other v) :
    Ledger s t ∅ ∅ 0 other 0 where
  up v := by have := (rise v).2; simp only [Pi.zero_apply]; omega
  down v _ _ := by have := (rise v).1; simp only [Pi.zero_apply]; omega
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := ⟨validator, by rw [validators]; exact found, rfl⟩
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- From Altair an attestation credits the proposer of the slot its recomputed reward.

Before Altair it moves no balance. -/
private theorem ledger_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (early : fork < .glamsterdam)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    ∃ (proposer : ValidatorIndex) (credit : ℕ),
      attestationCredit s attestation parent = .ok credit ∧
      (0 < credit → getBeaconProposerIndex s = .ok proposer) ∧
      Ledger s t ∅ ∅ 0 (fun v => if v = proposer then credit else 0) 0 := by
  have registry := (processAttestation_registry computed).1
  by_cases altair : .altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair,
      bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _, total,
      totalOk, attesters, attestersOk, pair, flagsOk, proposer, proposerOk, u, raised, final⟩ :=
      computed
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
    simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
    subst t
    rw [getBeaconProposerIndex_setEpochParticipation] at proposerOk
    refine ⟨proposer, (pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat,
      ?_, fun _ => proposerOk, ?_⟩
    · simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
        attestersOk, Except.mapError, bind, Except.bind, flagsOk]
      rfl
    · have kept : (setEpochParticipation s
          (attestation.data.target.epoch == getCurrentEpoch s) pair.1).balances = s.balances := by
        unfold setEpochParticipation
        split <;> rfl
      have sizes := (sameSizes_increaseBalance raised).2
      rw [kept] at sizes
      refine Ledger.of_rise (by rw [registry]) fun v => ?_
      cases found : s.balances.data[v.toNat]? with
      | none =>
        have missing : u.balances.data[v.toNat]? = none := by
          rw [Array.getElem?_eq_none_iff] at found ⊢
          omega
        simp [actualBalanceAt, found, missing]
      | some balance =>
        obtain ⟨final, finalFound, finalValue⟩ :=
          balance_increaseBalance raised (j := v.toNat) (by rw [kept]; exact found)
        have same : proposer.toNat = v.toNat ↔ v = proposer :=
          ⟨fun h => (UInt64.toNat_inj.mp h).symm, fun h => h ▸ rfl⟩
        simp only [actualBalanceAt, found, finalFound, Option.map_some, Option.getD_some,
          finalValue]
        by_cases equal : v = proposer <;> simp [equal, same]
  · obtain ⟨_, _, _, _, _, recorded, _⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) computed
    have kept : t.balances = s.balances := by
      have h := recordPendingAttestation_ok recorded
      split at h <;> have eq := congrArg (fun x => x.balances) h.2 <;> exact eq
    refine ⟨0, 0, by simp [attestationCredit, altair, pure, Except.pure], fun zero => absurd zero
      (Nat.lt_irrefl 0), ?_⟩
    exact (Ledger.of_eq (by rw [kept]) (by rw [registry])).mono ∅ (subset_refl _)
      (fun _ => Nat.zero_le _) (fun _ => le_rfl)

/-- Take a step that keeps the registry or appends one validator.

If it moves each balance by at most a credit, it gives a ledger with only that credit. -/
private theorem Ledger.of_append {credit : ValidatorIndex → ℕ}
    (validators : t.validators.data = s.validators.data ∨
      ∃ added, t.validators.data = s.validators.data.push added)
    (balances : ∀ v : ValidatorIndex,
      actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat + credit v ∧
      actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat) :
    Ledger s t ∅ ∅ 0 credit 0 where
  up v := by have := (balances v).1; simp only [Pi.zero_apply]; omega
  down v _ _ := by have := (balances v).2; simp only [Pi.zero_apply]; omega
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := by
    refine ⟨validator, ?_, rfl⟩
    rcases validators with same | ⟨added, pushed⟩
    · rw [same]; exact found
    · rw [pushed, Array.getElem?_push]
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.ne_of_lt inside))]
      exact found
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- Appending a balance keeps every balance below and reads the new one at the end. -/
private theorem actualBalanceAt_push {balance : Gwei}
    (pushed : t.balances.data = s.balances.data.push balance) (i : ℕ) :
    actualBalanceAt ⟨fork, t⟩ i = if i = s.balances.data.size then balance.toNat
      else actualBalanceAt ⟨fork, s⟩ i := by
  simp only [actualBalanceAt, pushed, Array.getElem?_push]
  split
  · simp
  · rfl

/-- Before Electra a deposit credits its amount to one validator, maybe a new one.

From Electra it moves no balance, since it only queues the amount.

The balances must match the validators, so that a new validator gets a new balance. -/
private theorem ledger_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (matched : BalancesMatch s)
    (computed : processDeposit config checks before s deposit = .ok t) :
    ∃ recipient : ValidatorIndex,
      (t.eth1DepositIndex before).toNat = (s.eth1DepositIndex before).toNat + 1 ∧
      Ledger s t ∅ ∅ 0 (fun v => if v = recipient ∧ fork < .pectra then
        deposit.data.amount.toNat else 0) 0 := by
  obtain ⟨-, index, next, -, applied⟩ := processDeposit_ok computed
  generalize hs' : { s with eth1DepositIndex := fun _ => next } = s' at applied
  have balances' : s'.balances = s.balances := by rw [← hs']
  have validators' : s'.validators = s.validators := by rw [← hs']
  have matched' : BalancesMatch s' := by
    unfold BalancesMatch at matched ⊢; rw [balances', validators']; exact matched
  have actual' (i : ℕ) : actualBalanceAt ⟨fork, s'⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
    simp only [actualBalanceAt, balances']
  -- An appended zero balance reads like no balance.
  have zero {u : BeaconState preset fork} (pushed : u.balances.data = s'.balances.data.push 0)
      (v : ValidatorIndex) :
      actualBalanceAt ⟨fork, u⟩ v.toNat = actualBalanceAt ⟨fork, s⟩ v.toNat := by
    rw [actualBalanceAt_push pushed, ← actual' v.toNat]
    split
    · rename_i at_end
      simp [actualBalanceAt, at_end]
    · rfl
  unfold applyDeposit at applied
  split at applied
  · rename_i electra
    have notBefore : ¬ fork < .pectra := Nat.not_lt_of_le electra
    refine ⟨0, index, ?_⟩
    simp only [notBefore, and_false, ↓reduceIte]
    unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨registered, added, queued⟩ := applied
        obtain ⟨_, queuedEq⟩ := addPendingDeposit_eq queued
        obtain ⟨validatorsPushed, balancesPushed⟩ := addValidatorToRegistry_push added matched'
        have finalBalances : t.balances.data = s'.balances.data.push 0 := by
          rw [queuedEq]; exact balancesPushed
        refine Ledger.of_append (.inr ⟨_, by rw [queuedEq, ← validators']; exact validatorsPushed⟩)
          fun v => ?_
        have := zero finalBalances v
        exact ⟨by omega, by omega⟩
      · cases applied
        exact Ledger.of_append (.inl (by rw [validators'])) fun v => by
          have := actual' v.toNat; exact ⟨by omega, by omega⟩
    · obtain ⟨_, queuedEq⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      have finalBalances : t.balances = s'.balances := by rw [queuedEq]
      exact Ledger.of_append (.inl (by rw [queuedEq, validators'])) fun v => by
        have := actual' v.toNat
        simp only [actualBalanceAt, finalBalances] at this ⊢
        exact ⟨by omega, by omega⟩
  · rename_i electra
    have earlier : fork < .pectra := Nat.lt_of_not_le electra
    rcases applyPendingDeposit_cases applied with rfl | ⟨recipient, raised⟩ | ⟨_, added⟩
    · refine ⟨0, index, Ledger.of_append (.inl (by rw [validators'])) fun v => ?_⟩
      have := actual' v.toNat
      omega
    · refine ⟨recipient, index, Ledger.of_append
        (.inl (by rw [increaseBalance_validators raised, validators'])) fun v => ?_⟩
      obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
      have := actual' v.toNat
      by_cases same : v = recipient
      · subst same
        simp only [actualBalanceAt, BeaconState.putBalance, Array.getElem?_set_self,
          Array.getElem?_eq_getElem inside, Option.map_some, Option.getD_some, earlier, and_self,
          ↓reduceIte, toNat_add_of_lt fits] at this ⊢
        omega
      · have different : recipient.toNat ≠ v.toNat := fun equal =>
          same (UInt64.toNat_inj.mp equal).symm
        simp only [actualBalanceAt, BeaconState.putBalance, Array.getElem?_set, different,
          same, false_and, ↓reduceIte] at this ⊢
        exact ⟨by omega, by omega⟩
    · obtain ⟨validatorsPushed, balancesPushed⟩ := addValidatorToRegistry_push added matched'
      refine ⟨UInt64.ofNat s'.balances.data.size, index, Ledger.of_append
        (.inr ⟨_, by simpa [validators'] using validatorsPushed⟩) fun v => ?_⟩
      rw [actualBalanceAt_push balancesPushed, ← actual' v.toNat]
      split
      · rename_i at_end
        have same : v = UInt64.ofNat s'.balances.data.size := by
          rw [← at_end]; simp
        have absent : actualBalanceAt ⟨fork, s'⟩ v.toNat = 0 := by
          simp [actualBalanceAt, at_end]
        rw [absent]
        simp [same, earlier]
      · omega

/-- Writing a validator that compounds exactly when the old one did moves no balance. -/
private theorem Ledger.setValidator {i : ValidatorIndex} {old new : Validator}
    (found : getValidator s i = .ok old)
    (same : hasCompoundingWithdrawalCredential new = hasCompoundingWithdrawalCredential old)
    (set : s.setValidator i new = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read := getValidator_eq_ok_iff.mp found
  refine Ledger.of_kept rfl fun v validator located => ?_
  by_cases eq : v.toNat = i.toNat
  · rw [eq, read, Option.some.injEq] at located
    subst located
    exact ⟨new, by simp [BeaconState.putValidator, eq], same⟩
  · exact ⟨validator, by simpa [BeaconState.putValidator, Ne.symm eq] using located, rfl⟩

/-- The start of an exit moves no balance, and keeps the credentials. -/
private theorem Ledger.exit {i : ValidatorIndex}
    (computed : initiateValidatorExit config s i = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Ledger.refl _
  · have same := exitQueue_validators queue
    have one : Ledger s queued ∅ ∅ 0 0 0 := Ledger.of_eq (by rw [same.2]) (by rw [same.1])
    have two := Ledger.setValidator (old := validator)
      (by rw [getValidator_of_validators_eq same.1]; exact found) (by rfl) set
    simpa only [Finset.empty_union, add_zero] using one.trans two

private theorem ledger_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact Ledger.exit exited

/-- A fold whose every step moves no balance and keeps the credentials does the same. -/
private theorem Ledger.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {items : List α}
    (kept : ∀ u x u', step u x = .ok u' → Ledger u u' ∅ ∅ 0 0 0)
    (computed : items.foldlM step s = .ok t) : Ledger s t ∅ ∅ 0 0 0 :=
  foldlM_ok_invariant (fun u => Ledger s u ∅ ∅ 0 0 0)
    (fun _ _ _ before ok => by
      simpa only [Finset.empty_union, add_zero] using before.trans (kept _ _ _ ok))
    (Ledger.refl s) computed

private theorem ledger_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    refine Ledger.foldlM (fun u signed u' ok => ?_) computed
    obtain ⟨validator, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
    -- Credentials of either prefix do not compound.
    refine Ledger.setValidator found ?_ set
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      executionCredentials_prefix, BLS_WITHDRAWAL_PREFIX, ETH1_ADDRESS_WITHDRAWAL_PREFIX,
      COMPOUNDING_WITHDRAWAL_PREFIX]
  · cases computed
    exact Ledger.refl _

/-- Queueing the excess caps one balance at the activation balance, and keeps the registry. -/
private theorem queueExcessActiveBalance_capped {electra : .pectra ≤ fork} {i : ValidatorIndex}
    (computed : queueExcessActiveBalance s electra i = .ok t) :
    t.validators.data = s.validators.data ∧ ∀ j, actualBalanceAt ⟨fork, t⟩ j =
      if j = i.toNat then min (actualBalanceAt ⟨fork, s⟩ j) preset.MIN_ACTIVATION_BALANCE.toNat
      else actualBalanceAt ⟨fork, s⟩ j := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨balance, read, computed⟩ := computed
  rw [getBalance_eq_ok_iff] at read
  split at computed
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨inside, rfl⟩ := setBalance_ok set
    have := UInt64.lt_iff_toNat_lt.mp above
    refine ⟨rfl, fun j => ?_⟩
    by_cases eq : j = i.toNat
    · subst eq
      simp [actualBalanceAt, BeaconState.putBalance, read]
      omega
    · simp [actualBalanceAt, BeaconState.putBalance, eq, Ne.symm eq]
  · rename_i below
    cases computed
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp below)
    refine ⟨rfl, fun j => ?_⟩
    by_cases eq : j = i.toNat
    · subst eq
      simp [actualBalanceAt, read]
      omega
    · simp [eq]

/-- A switch to compounding converts one validator that did not compound before. -/
private theorem Ledger.switch {electra : .pectra ≤ fork} {i : ValidatorIndex}
    {validator : Validator}
    (found : s.validators.data[i.toNat]? = some validator)
    (fresh : hasCompoundingWithdrawalCredential validator = false)
    (computed : switchToCompoundingValidator s electra i = .ok t) : Ledger s t ∅ {i} 0 0 0 := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨old, read, _, set, queued⟩ := computed
  rw [getValidator_eq_ok_iff, found, Option.some.injEq] at read
  subst read
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  obtain ⟨same, capped⟩ := queueExcessActiveBalance_capped queued
  have balances : ∀ j, actualBalanceAt ⟨fork, t⟩ j = if j = i.toNat then
      min (actualBalanceAt ⟨fork, s⟩ j) preset.MIN_ACTIVATION_BALANCE.toNat
      else actualBalanceAt ⟨fork, s⟩ j := capped
  have apart {v : ValidatorIndex} (notConv : v ∉ ({i} : Finset ValidatorIndex)) :
      v.toNat ≠ i.toNat := fun eq =>
    notConv (Finset.mem_singleton.mpr (UInt64.toNat_inj.mp eq))
  constructor
  · intro v
    rw [balances]
    split <;> simp
  · intro v _ notConv
    simp [balances, apart notConv]
  · intro v member
    rw [Finset.mem_singleton.mp member, balances]
    simp
  · intro v member _
    rw [Finset.mem_singleton.mp member, balances]
    simp
  · intro v validator' notConv located
    exact ⟨validator', by
      simpa [same, BeaconState.putValidator, Ne.symm (apart notConv)] using located, rfl⟩
  · intro v member validator' located
    rw [Finset.mem_singleton.mp member, found, Option.some.injEq] at located
    exact located ▸ fresh
  · intro v member
    rw [Finset.mem_singleton.mp member, same]
    simp [BeaconState.putValidator, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]

/-- Queueing a consolidation moves no balance, and keeps the credentials. -/
private theorem Ledger.consolidate {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churned, epoch⟩, churn, _, _, marked, set, pending, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have same := computeConsolidationEpochAndUpdateChurn_earliest churn
  have one : Ledger s churned ∅ ∅ 0 0 0 := Ledger.of_eq (by rw [same.2.2]) (by rw [same.2.1])
  have two := Ledger.setValidator (old := source)
    (by rw [getValidator_eq_ok_iff, same.2.1]; exact found) (by rfl) set
  simpa only [Finset.empty_union, add_zero] using (one.trans two).trans
    (Ledger.of_eq (t := { marked with pendingConsolidations := fun _ => pending }) rfl rfl)

/-- A consolidation request converts at most one validator, and moves no other balance. -/
private theorem ledger_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧ conv.card ≤ 1 := by
  -- A validator valid for a switch has the execution address prefix, so it does not compound.
  have fresh : ∀ validator, isValidSwitchToCompoundingRequest s request validator = true →
      hasCompoundingWithdrawalCredential validator = false := by
    intro validator valid
    simp only [isValidSwitchToCompoundingRequest, hasEth1WithdrawalCredential, Bool.and_eq_true,
      beq_iff_eq] at valid
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, valid.1.1.2,
      ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals try first
    | (cases computed; done)
    | (cases computed; exact ⟨∅, Ledger.refl _, by simp⟩)
  · rename_i checked valid
    exact ⟨_, Ledger.switch (getElem?_toNat_of_ofNatChecked checked) (fresh _ valid)
      (liftAccessor_ok.mp computed), (Finset.card_singleton _).le⟩
  · rename_i checked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨∅, Ledger.consolidate (getElem?_toNat_of_ofNatChecked checked) computed, by simp⟩

/-- The requests of the execution layer convert at most one validator per consolidation request.

They move no other balance. -/
private theorem ledger_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := computed
  have one : Ledger s deposited ∅ ∅ 0 0 0 := Ledger.foldlM (fun _ _ _ ok =>
    Ledger.of_eq (by rw [(processDepositRequest_ok ok).2.2])
      (by rw [(processDepositRequest_ok ok).2.1])) deposits
  have two : Ledger deposited withdrawn ∅ ∅ 0 0 0 := by
    refine Ledger.foldlM (fun _ _ _ ok => ?_) withdrawals
    unfold processWithdrawalRequest at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals try first
      | (cases ok; done)
      | (cases ok; exact Ledger.refl _)
      | exact Ledger.exit (liftAccessor_ok.mp ok)
    -- A partial withdrawal only spends exit churn and queues the withdrawal.
    simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
    obtain ⟨_, _, _, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
      obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
      have same := computeExitEpochAndUpdateChurn_earliest churned
      exact Ledger.of_eq (by rw [same.2.2]) (by rw [same.2.1])
    · cases ok
      exact Ledger.refl _
  -- Each consolidation request converts at most one validator.
  have three : ∀ (requests : List ConsolidationRequest) (u : BeaconState preset fork),
      requests.foldlM (processConsolidationRequest config · electra.1 ·) u = .ok t →
      ∃ conv : Finset ValidatorIndex, Ledger u t ∅ conv 0 0 0 ∧ conv.card ≤ requests.length := by
    intro requests
    induction requests with
    | nil =>
      intro u ok
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at ok
      exact ⟨∅, ok ▸ Ledger.refl u, by simp⟩
    | cons request rest ih =>
      intro u ok
      rw [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨middle, first, others⟩ := ok
      obtain ⟨conv, ledger, card⟩ := ledger_processConsolidationRequest first
      obtain ⟨conv', ledger', card'⟩ := ih middle others
      refine ⟨conv ∪ conv', ?_, ?_⟩
      · simpa only [Finset.empty_union, add_zero] using ledger.trans ledger'
      have := Finset.card_union_le conv conv'
      simp only [List.length_cons]
      omega
  obtain ⟨conv, ledger, card⟩ := three _ _ consolidations
  have bound := (body.executionRequests electra).consolidations.bound electra.2
  refine ⟨conv, ?_, ?_⟩
  · simpa only [Finset.empty_union, add_zero] using (one.trans two).trans ledger
  simp only [Array.length_toList] at card
  omega

/-- The sync aggregate step keeps the registry and the current sync committee. -/
private theorem processSyncAggregate_kept {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    t.validators = s.validators ∧ t.currentSyncCommittee = s.currentSyncCommittee := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun x : BeaconState preset fork =>
    x.validators = s.validators ∧ x.currentSyncCommittee = s.currentSyncCommittee)
    (fun _ _ _ held ok => ?_) ⟨rfl, rfl⟩ folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    obtain ⟨_, set⟩ := increaseBalance_ok raised
    obtain ⟨_, rfl⟩ := setBalance_ok set
    obtain ⟨_, set'⟩ := increaseBalance_ok paid
    obtain ⟨_, rfl⟩ := setBalance_ok set'
    exact held
  · obtain ⟨_, set⟩ := decreaseBalance_ok (liftAccessor_ok.mp ok)
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact held

/-- Each member index found for a list of keys stands for one of those keys.

Its validator holds that key. -/
private theorem countP_validatorIndexOfPubkey_le (v : ValidatorIndex) :
    ∀ {keys : List Cryptography.Bls.BLSPubkey} {members : List ValidatorIndex},
      keys.mapM (validatorIndexOfPubkey s) = .ok members →
      members.countP (fun m => m.toNat = v.toNat) ≤
        (keys.filter fun key => (s.validators.data[v.toNat]?).any (·.pubkey == key)).length
  | [], members, ok => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    simp
  | key :: keys, members, ok => by
    obtain ⟨m, rest, head, tail, rfl⟩ := mapM_cons_ok.mp ok
    have ih := countP_validatorIndexOfPubkey_le v tail
    by_cases same : m.toNat = v.toNat
    · have holds : (s.validators.data[v.toNat]?).any (·.pubkey == key) = true := by
        unfold validatorIndexOfPubkey at head
        split at head
        · rename_i position found
          simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at head
          have position_eq := (Base.Uint64.ofNatChecked_ok_iff.mp head).2
          obtain ⟨inside, matching, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
          rw [← same, position_eq, Array.getElem?_eq_getElem inside]
          simpa using matching
        · cases head
      simp only [List.countP_cons, same, decide_true, ↓reduceIte, List.filter_cons, holds,
        List.length_cons]
      omega
    · simp only [List.countP_cons, same, decide_false, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero, List.filter_cons]
      split <;> (try simp only [List.length_cons]) <;> omega

/-- Pairing a list with another counts no more matches of the first entries than the list has. -/
private theorem countP_zip_fst_le {α β : Type} (p : α → Bool) :
    ∀ (first : List α) (second : List β),
      (first.zip second).countP (fun m => p m.1) ≤ first.countP p
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: first, b :: second => by
    have := countP_zip_fst_le p first second
    simp only [List.zip_cons_cons, List.countP_cons]
    split <;> omega

/-- In the fold of the sync rewards, a balance moves by at most the reward for each seat.

These seats are the seats of its validator.

When that validator is the proposer, the bound adds the proposer share for each signed seat. -/
private theorem foldl_syncReward_bounds (r p : ℕ) (chosen : ValidatorIndex) (j : ℕ) :
    ∀ (members : List (ValidatorIndex × Bool)) (b : ℕ),
      members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then r else 0) +
            (if chosen.toNat = j then p else 0)
          else if member.1.toNat = j then balance - r else balance) b ≤
        b + r * members.countP (fun m => m.1.toNat = j) +
          (if chosen.toNat = j then p * members.countP (·.2) else 0) ∧
      b ≤ members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then r else 0) +
            (if chosen.toNat = j then p else 0)
          else if member.1.toNat = j then balance - r else balance) b +
        r * members.countP (fun m => m.1.toNat = j)
  | [], b => by simp
  | ⟨index, signed⟩ :: members, b => by
    obtain ⟨up, down⟩ := foldl_syncReward_bounds r p chosen j members
      (if signed then b + (if index.toNat = j then r else 0) +
        (if chosen.toNat = j then p else 0)
      else if index.toNat = j then b - r else b)
    simp only [List.foldl_cons, List.countP_cons]
    cases signed <;> by_cases h1 : index.toNat = j <;> by_cases h2 : chosen.toNat = j <;>
      simp only [h1, h2, Bool.false_eq_true, decide_true, decide_false, ↓reduceIte,
        Nat.mul_add, Nat.mul_one, Nat.add_zero] at up down ⊢ <;>
      omega

/-- The sync aggregate pays each member the participant reward for each seat it signed.

It charges each member for each seat it did not sign.

The proposer of the slot earns its share for each signed seat, which no participant amount counts.
-/
private theorem ledger_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ (proposer : ValidatorIndex) (reward : Gwei) (share : ℕ) (sync : ValidatorIndex → ℕ),
      syncParticipantReward s = .ok reward ∧
      (0 < share → getBeaconProposerIndex s = .ok proposer) ∧
      share ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
        (reward.toNat * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) ∧
      (∀ v, sync v ≤ seatsOf t altair v * reward.toNat) ∧
      Ledger s t ∅ ∅ sync (fun v => if v = proposer then share else 0) 0 := by
  obtain ⟨reward, proposerReward, members, chosen, rewardOk, proposerValue, membersOk, signed,
    balances⟩ := processSyncAggregate_balance computed
  have kept := processSyncAggregate_kept computed
  have sizes := (sameSizes_processSyncAggregate computed).2
  obtain ⟨pairs, pairsDef⟩ :
      ∃ pairs, pairs = (members.zip aggregate.syncCommitteeBits.bits.toArray).toList := ⟨_, rfl⟩
  rw [← pairsDef] at signed balances
  have membersSize := (array_mapM_ok membersOk).1
  rw [Vector.size_toArray] at membersSize
  have pairsLength : pairs.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat := by
    rw [pairsDef, Array.length_toList, Array.size_zip]
    exact (Nat.min_le_left _ _).trans membersSize.le
  refine ⟨chosen, reward, proposerReward.toNat * pairs.countP (·.2),
    fun v => reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat), rewardOk, ?_, ?_, ?_, ?_⟩
  · intro positive
    apply signed
    have count : 0 < pairs.countP (·.2) :=
      Nat.pos_of_ne_zero fun zero => by simp [zero] at positive
    obtain ⟨member, member_in, holds⟩ := List.countP_pos_iff.mp count
    exact ⟨member, member_in, by simpa using holds⟩
  · rw [← proposerValue, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ ((List.countP_le_length).trans pairsLength)
  · intro v
    dsimp only
    rw [Nat.mul_comm (seatsOf t altair v)]
    apply Nat.mul_le_mul_left
    rw [Array.mapM_eq_mapM_toList] at membersOk
    cases listed : (s.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
        (validatorIndexOfPubkey s) with
    | error => rw [listed] at membersOk; cases membersOk
    | ok list =>
      rw [listed] at membersOk
      have same : list.toArray = members := Except.ok.inj membersOk
      subst same
      have zipped := countP_zip_fst_le (fun m : ValidatorIndex => decide (m.toNat = v.toNat))
        list aggregate.syncCommitteeBits.bits.toArray.toList
      have seats := countP_validatorIndexOfPubkey_le v listed
      rw [pairsDef, Array.toList_zip]
      simp only [seatsOf, kept.1, kept.2]
      exact zipped.trans seats
  · have bounds := fun v : ValidatorIndex =>
      foldl_syncReward_bounds reward.toNat proposerReward.toNat chosen v.toNat pairs
    have equal : ∀ v : ValidatorIndex, chosen.toNat = v.toNat ↔ v = chosen :=
      fun v => ⟨fun h => (UInt64.toNat_inj.mp h).symm, fun h => h ▸ rfl⟩
    have moved : ∀ v : ValidatorIndex,
        actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat +
          reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat) +
          (if v = chosen then proposerReward.toNat * pairs.countP (·.2) else 0) ∧
        actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat +
          reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat) := by
      intro v
      cases found : s.balances.data[v.toNat]? with
      | none =>
        have missing : t.balances.data[v.toNat]? = none := by
          rw [Array.getElem?_eq_none_iff] at found ⊢
          omega
        simp [actualBalanceAt, found, missing]
      | some balance =>
        obtain ⟨final, finalFound, finalValue⟩ := balances v.toNat balance found
        obtain ⟨up, down⟩ := bounds v balance.toNat
        rw [← finalValue] at up down
        simp only [actualBalanceAt, found, finalFound, Option.map_some, Option.getD_some]
        by_cases isChosen : v = chosen
        · subst isChosen
          simp only [↓reduceIte] at up ⊢
          exact ⟨up, down⟩
        · simp only [isChosen, ↓reduceIte, Nat.add_zero] at up ⊢
          simp only [mt (equal v).mp isChosen, ↓reduceIte, Nat.add_zero] at up
          exact ⟨up, down⟩
    exact {
      up := fun v => (moved v).1
      down := fun v _ _ => by have := (moved v).2; simp only [Pi.zero_apply]; omega
      converted := fun v member => absurd member (Finset.notMem_empty v)
      lowered := fun v member => absurd member (Finset.notMem_empty v)
      kept := fun v validator _ found => ⟨validator, by rw [kept.1]; exact found, rfl⟩
      fresh := fun v member => absurd member (Finset.notMem_empty v)
      switched := fun v member => absurd member (Finset.notMem_empty v) }

end Steps

/-! ### The participation flags behind the proposer rewards of attestations -/

/-- The weight of the flags that a byte of participation flags has set. -/
private def flagWeight (flags : ParticipationFlags) : ℕ :=
  ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
    if hasFlag flags flag.val.toUInt64 then PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum

/-- The flags of both epochs at the first positions, each weighed by a base reward. -/
private def flagPotential {fork : Fork} (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (base : ℕ → ℕ) (count : ℕ) : ℕ :=
  ∑ i ∈ Finset.range count, base i *
    (flagWeight (((s.previousEpochParticipation altair).data[i]?).getD 0) +
      flagWeight (((s.currentEpochParticipation altair).data[i]?).getD 0))

/-- No flag is cleared, in either epoch. -/
private def FlagsGrow {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (i : ℕ) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length),
    (hasFlag (((s.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true) ∧
    (hasFlag (((s.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true)

private theorem FlagsGrow.refl {fork : Fork} (s : BeaconState preset fork) : FlagsGrow s s :=
  fun _ _ _ => ⟨id, id⟩

private theorem FlagsGrow.trans {fork : Fork} {s u t : BeaconState preset fork}
    (one : FlagsGrow s u) (two : FlagsGrow u t) : FlagsGrow s t :=
  fun altair i flag => ⟨fun set => (two altair i flag).1 ((one altair i flag).1 set),
    fun set => (two altair i flag).2 ((one altair i flag).2 set)⟩

/-- A step that keeps both flag lists, or appends to them, clears no flag. -/
private theorem FlagsGrow.of_prefix {fork : Fork} {s t : BeaconState preset fork}
    (previous : ∀ altair : .altair ≤ fork, (s.previousEpochParticipation altair).data.toList <+:
      (t.previousEpochParticipation altair).data.toList)
    (current : ∀ altair : .altair ≤ fork, (s.currentEpochParticipation altair).data.toList <+:
      (t.currentEpochParticipation altair).data.toList) : FlagsGrow s t := by
  intro altair i flag
  have read {a b : Array ParticipationFlags} (pre : a.toList <+: b.toList) :
      ∀ x, a[i]? = some x → b[i]? = some x := by
    intro x found
    obtain ⟨rest, joined⟩ := pre
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    rw [← Array.getElem?_toList, ← joined, List.getElem?_append_left (by simpa using inside),
      Array.getElem?_toList]
    exact found
  have zero : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
      hasFlag 0 flag.val.toUInt64 = false := by decide
  constructor
  · intro set
    cases found : ((s.previousEpochParticipation altair).data[i]?) with
    | none => simp [found, zero] at set
    | some x => rw [read (previous altair) x found]; simpa [found] using set
  · intro set
    cases found : ((s.currentEpochParticipation altair).data[i]?) with
    | none => simp [found, zero] at set
    | some x => rw [read (current altair) x found]; simpa [found] using set

/-- Flags that grow raise the potential. -/
private theorem flagPotential_mono {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagsGrow s t) (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ) :
    flagPotential s altair base count ≤ flagPotential t altair base count := by
  unfold flagPotential
  apply Finset.sum_le_sum
  intro i _
  apply Nat.mul_le_mul_left
  have weight (a b : ParticipationFlags)
      (more : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
        hasFlag a flag.val.toUInt64 = true → hasFlag b flag.val.toUInt64 = true) :
      flagWeight a ≤ flagWeight b := by
    unfold flagWeight
    apply List.sum_le_sum
    intro flag _
    by_cases set : hasFlag a flag.val.toUInt64 = true
    · simp [set, more flag set]
    · simp only [Bool.not_eq_true] at set
      simp [set]
  exact Nat.add_le_add (weight _ _ fun flag => (grow altair i flag).1)
    (weight _ _ fun flag => (grow altair i flag).2)

/-- No flag of an existing validator is cleared, in either epoch. -/
private def FlagsGrowBelow {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (i : ℕ) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length),
    i < s.validators.data.size →
    (hasFlag (((s.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true) ∧
    (hasFlag (((s.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true)

private theorem FlagsGrow.below {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagsGrow s t) : FlagsGrowBelow s t := fun altair i flag _ => grow altair i flag

private theorem FlagsGrowBelow.trans {fork : Fork} {s u t : BeaconState preset fork}
    (one : FlagsGrowBelow s u) (two : FlagsGrowBelow u t)
    (grows : s.validators.data.size ≤ u.validators.data.size) : FlagsGrowBelow s t :=
  fun altair i flag inside =>
    ⟨fun set => (two altair i flag (Nat.lt_of_lt_of_le inside grows)).1
        ((one altair i flag inside).1 set),
      fun set => (two altair i flag (Nat.lt_of_lt_of_le inside grows)).2
        ((one altair i flag inside).2 set)⟩

/-- Flags of existing validators that grow raise a potential weighed on existing validators. -/
private theorem flagPotential_mono_below {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagsGrowBelow s t) (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ)
    (support : ∀ i, s.validators.data.size ≤ i → base i = 0) :
    flagPotential s altair base count ≤ flagPotential t altair base count := by
  unfold flagPotential
  apply Finset.sum_le_sum
  intro i _
  by_cases inside : i < s.validators.data.size
  · apply Nat.mul_le_mul_left
    have weight (a b : ParticipationFlags)
        (more : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
          hasFlag a flag.val.toUInt64 = true → hasFlag b flag.val.toUInt64 = true) :
        flagWeight a ≤ flagWeight b := by
      unfold flagWeight
      apply List.sum_le_sum
      intro flag _
      by_cases set : hasFlag a flag.val.toUInt64 = true
      · simp [set, more flag set]
      · simp only [Bool.not_eq_true] at set
        simp [set]
    exact Nat.add_le_add (weight _ _ fun flag => (grow altair i flag inside).1)
      (weight _ _ fun flag => (grow altair i flag inside).2)
  · rw [support i (Nat.le_of_not_lt inside)]
    simp

section Grow

variable {fork : Fork} {s t : BeaconState preset fork}

/-- A step that keeps both lists of flags clears no flag. -/
private theorem FlagsGrow.of_eq
    (previous : t.previousEpochParticipation = s.previousEpochParticipation := by rfl)
    (current : t.currentEpochParticipation = s.currentEpochParticipation := by rfl) :
    FlagsGrow s t := fun _ _ _ => by
  rw [previous, current]
  exact ⟨id, id⟩

/-- A fold whose every step clears no flag clears no flag. -/
private theorem FlagsGrow.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (grow : ∀ u x u', step u x = .ok u' → FlagsGrow u u') {items : List α}
    (computed : items.foldlM step s = .ok t) : FlagsGrow s t :=
  foldlM_ok_invariant (FlagsGrow s) (fun _ _ _ before ok => before.trans (grow _ _ _ ok))
    (FlagsGrow.refl s) computed

/-- A balance increase clears no flag. -/
private theorem grow_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance s index delta = .ok t) : FlagsGrow s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact FlagsGrow.of_eq

/-- A balance decrease clears no flag. -/
private theorem grow_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance s index delta = .ok t) : FlagsGrow s t := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact FlagsGrow.of_eq

/-- A validator write clears no flag. -/
private theorem grow_setValidator {index : ValidatorIndex} {validator : Validator}
    (computed : s.setValidator index validator = .ok t) : FlagsGrow s t := by
  obtain ⟨_, rfl⟩ := setValidator_ok computed
  exact FlagsGrow.of_eq

/-- The exit queue clears no flag. -/
private theorem grow_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config s exitBalance = .ok (t, exitEpoch)) : FlagsGrow s t := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact FlagsGrow.of_eq
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact FlagsGrow.refl _

/-- Starting an exit clears no flag. -/
private theorem grow_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config s index = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact FlagsGrow.refl _
  · exact (grow_exitQueue queue).trans (grow_setValidator set)

/-- Slashing a validator clears no flag. -/
private theorem grow_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config s slashedIndex whistleblowerIndex = .ok t) :
    FlagsGrow s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -,
    loweredOk, -, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  refine (grow_initiateValidatorExit exitedOk).trans <| (grow_setValidator markedOk).trans <|
    (FlagsGrow.of_eq (s := marked) (t := { marked with slashings })).trans <|
    (grow_decreaseBalance loweredOk).trans <| (grow_increaseBalance raisedOk).trans <|
    (grow_increaseBalance lastOk).trans ?_
  subst done
  split
  · exact FlagsGrow.of_eq
  · exact FlagsGrow.refl _

private theorem grow_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact FlagsGrow.of_eq

/-- One withdrawal clears no flag. -/
private theorem grow_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal s withdrawal = .ok t) : FlagsGrow s t := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact FlagsGrow.of_eq
  · exact grow_decreaseBalance computed

/-- The withdrawals that a block expects clear no flag. -/
private theorem grow_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals s capella expected = .ok t) : FlagsGrow s t := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : FlagsGrow s applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact FlagsGrow.foldlM (fun _ _ _ ok => grow_applyWithdrawal ok) appliedOk
  have two : FlagsGrow applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact FlagsGrow.of_eq
    · cases indexedOk
      exact FlagsGrow.refl _
  have queued : ∀ kept : BeaconState preset fork,
      FlagsGrow kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact FlagsGrow.of_eq
    · exact FlagsGrow.refl _
  have partials : ∀ kept : BeaconState preset fork,
      FlagsGrow kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact FlagsGrow.of_eq
    · exact FlagsGrow.refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → FlagsGrow kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact FlagsGrow.of_eq
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact FlagsGrow.of_eq
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ FlagsGrow.refl _
  have final : FlagsGrow finished t := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact FlagsGrow.of_eq
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans final

/-- The withdrawals of a block clear no flag. -/
private theorem grow_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals s capella payload = .ok t) : FlagsGrow s t := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact grow_applyExpectedWithdrawals applied
    · cases computed
      exact FlagsGrow.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact grow_applyExpectedWithdrawals applied

/-- The execution payload of a block clears no flag. -/
private theorem grow_processExecutionPayload {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine s body bellatrix = .ok t) :
    FlagsGrow s t := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact FlagsGrow.of_eq

private theorem grow_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    FlagsGrow s t := by
  unfold processBlockExecution at computed
  split at computed
  · exact absurd early (Nat.not_lt_of_le (by assumption))
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (grow_processWithdrawals withdrawnOk).trans (grow_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact grow_processExecutionPayload computed
    · cases computed
      exact FlagsGrow.refl _

private theorem grow_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact FlagsGrow.of_eq

private theorem grow_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact FlagsGrow.of_eq

private theorem grow_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : FlagsGrow s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact grow_slashValidator slashed

/-- Slashing a validator if it is slashable clears no flag. -/
private theorem grow_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    FlagsGrow step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact grow_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ FlagsGrow.refl _

private theorem grow_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : FlagsGrow s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step : BeaconState preset fork × Bool => FlagsGrow s step.1)
    (fun _ _ _ before ok => FlagsGrow.trans before (grow_slashIfSlashable ok))
    (show FlagsGrow s (s, false).1 from FlagsGrow.refl s) folded

/-- Adding a participation flag sets it. -/
private theorem hasFlag_addFlag_self (flags : ParticipationFlags)
    (added : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    hasFlag (addFlag flags added.val.toUInt64) added.val.toUInt64 = true := by
  simp only [hasFlag, addFlag, beq_iff_eq]
  apply UInt8.toBitVec_inj.mp
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or]
  ext k
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases (flags.toBitVec)[k] <;> cases (flagBit added.val.toUInt64).toBitVec[k] <;> rfl

/-- Adding a participation flag clears no flag. -/
private theorem hasFlag_addFlag_of_hasFlag {flags : ParticipationFlags}
    (added : Fin PARTICIPATION_FLAG_WEIGHTS.length) {other : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    (set : hasFlag flags other.val.toUInt64 = true) :
    hasFlag (addFlag flags added.val.toUInt64) other.val.toUInt64 = true := by
  by_cases same : other = added
  · subst same
    exact hasFlag_addFlag_self flags other
  · rw [hasFlag_addFlag_of_ne flags same]
    exact set

/-- Adding a flag that was not set adds its weight. -/
private theorem flagWeight_addFlag {flags : ParticipationFlags}
    {added : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    (unset : hasFlag flags added.val.toUInt64 = false) :
    flagWeight (addFlag flags added.val.toUInt64) =
      flagWeight flags + PARTICIPATION_FLAG_WEIGHTS[added].toNat := by
  have self := hasFlag_addFlag_self flags added
  have other : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, flag ≠ added →
      hasFlag (addFlag flags added.val.toUInt64) flag.val.toUInt64 =
        hasFlag flags flag.val.toUInt64 := fun _ different => hasFlag_addFlag_of_ne flags different
  unfold flagWeight
  have range : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide
  rw [range]
  match added with
  | ⟨0, _⟩ =>
    have one := other ⟨1, by decide⟩ (by simp)
    have two := other ⟨2, by decide⟩ (by simp)
    simp only at self one two unset
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, self, one, two, unset]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega
  | ⟨1, _⟩ =>
    have zero := other ⟨0, by decide⟩ (by simp)
    have two := other ⟨2, by decide⟩ (by simp)
    simp only at self zero two unset
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, self, zero, two, unset]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega
  | ⟨2, _⟩ =>
    have zero := other ⟨0, by decide⟩ (by simp)
    have one := other ⟨1, by decide⟩ (by simp)
    simp only at self zero one unset
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, self, zero, one, unset]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega

/-- Setting the flags of one attester clears none of them.

Weighed by its base reward, the flags gain at least the added numerator. -/
private theorem foldlM_addFlagReward_grow {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {base : ℕ} :
    ∀ {flagList : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)} {flags flags' : ParticipationFlags}
      {numerator numerator' : Gwei},
      flagList.foldlM (addFlagReward s total earned index) (flags, numerator) =
        .ok (flags', numerator') →
      (∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, hasFlag flags flag.val.toUInt64 = true →
        hasFlag flags' flag.val.toUInt64 = true) ∧
      ((∀ reward, getBaseReward s total index = .ok reward → reward.toNat = base) →
        numerator'.toNat + base * flagWeight flags ≤ numerator.toNat + base * flagWeight flags')
  | [], flags, flags', numerator, numerator', computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    exact ⟨fun _ => id, fun _ => Nat.le_refl _⟩
  | flag :: flagList, flags, flags', numerator, numerator', computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middleFlags, middle⟩, stepped, folded⟩ := computed
    obtain ⟨kept, gained⟩ := foldlM_addFlagReward_grow folded
    simp only [addFlagReward] at stepped
    split at stepped
    · rename_i newly
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨reward, rewardOk, weighted, weightedOk, added, addedOk, rfl, rfl⟩ := stepped
      rw [mulChecked_ok_iff] at weightedOk
      rw [addChecked_ok_iff] at addedOk
      refine ⟨fun other set => kept other (hasFlag_addFlag_of_hasFlag flag set), fun reads => ?_⟩
      have more := gained reads
      have weight := flagWeight_addFlag newly.2
      rw [weight] at more
      rw [addedOk.2, weightedOk.2, reads reward rewardOk] at more
      rw [Nat.mul_add] at more
      omega
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨rfl, rfl⟩ := stepped
      exact ⟨kept, gained⟩

/-- Setting the flags of attesters in turn clears none of them.

Suppose that each attester is in range and that its weight is its base reward.

Then the weighed flags gain at least the added numerator. -/
private theorem foldlM_addAttesterFlags_grow {total : Gwei} {earned : List UInt64}
    {base : ℕ → ℕ} {count : ℕ} :
    ∀ {attesters : List ValidatorIndex}
      {participation participation' : EpochParticipation preset fork}
      {numerator numerator' : Gwei},
      attesters.foldlM (addAttesterFlags s total earned) (participation, numerator) =
        .ok (participation', numerator') →
      (∀ (i : ℕ) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length),
        hasFlag ((participation.data[i]?).getD 0) flag.val.toUInt64 = true →
          hasFlag ((participation'.data[i]?).getD 0) flag.val.toUInt64 = true) ∧
      ((∀ attester ∈ attesters, attester.toNat < count ∧
          ∀ reward, getBaseReward s total attester = .ok reward →
            reward.toNat = base attester.toNat) →
        numerator'.toNat + ∑ i ∈ Finset.range count,
            base i * flagWeight ((participation.data[i]?).getD 0) ≤
          numerator.toNat + ∑ i ∈ Finset.range count,
            base i * flagWeight ((participation'.data[i]?).getD 0))
  | [], participation, participation', numerator, numerator', computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    exact ⟨fun _ _ => id, fun _ => Nat.le_refl _⟩
  | attester :: attesters, participation, participation', numerator, numerator', computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleNumerator⟩, stepped, folded⟩ := computed
    obtain ⟨kept, gained⟩ := foldlM_addAttesterFlags_grow (base := base) (count := count) folded
    unfold addAttesterFlags at stepped
    dsimp only at stepped
    split at stepped
    · rename_i inside
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨⟨flags, raised⟩, loop, written, rfl⟩ := stepped
      subst written
      obtain ⟨flagsKept, flagsGained⟩ :=
        foldlM_addFlagReward_grow (base := base attester.toNat) loop
      have read : ∀ i, (((participation.data.set attester.toNat flags inside)[i]?).getD 0) =
          if i = attester.toNat then flags else (participation.data[i]?).getD 0 := by
        intro i
        by_cases same : i = attester.toNat
        · subst same
          simp [inside]
        · simp [Ne.symm same, same]
      have own : (participation.data[attester.toNat]?).getD 0 =
          participation.data[attester.toNat] := by
        rw [Array.getElem?_eq_getElem inside]
        rfl
      refine ⟨fun i flag set => ?_, fun facts => ?_⟩
      · apply kept i flag
        dsimp only
        rw [read i]
        split
        · rename_i same
          subst same
          rw [own] at set
          exact flagsKept flag set
        · exact set
      · obtain ⟨below, reads⟩ := facts attester List.mem_cons_self
        have rest := gained fun later member => facts later (List.mem_cons_of_mem _ member)
        have step := flagsGained reads
        have member : attester.toNat ∈ Finset.range count := Finset.mem_range.mpr below
        dsimp only at rest
        have others : ∑ i ∈ (Finset.range count).erase attester.toNat,
            base i * flagWeight
              (((participation.data.set attester.toNat flags inside)[i]?).getD 0) =
            ∑ i ∈ (Finset.range count).erase attester.toNat,
              base i * flagWeight ((participation.data[i]?).getD 0) := by
          apply Finset.sum_congr rfl
          intro i erased
          rw [read i, ite_eq_right_iff.mpr fun same => absurd same (Finset.ne_of_mem_erase erased)]
        have after := (Finset.add_sum_erase _ (fun i => base i * flagWeight
          (((participation.data.set attester.toNat flags inside)[i]?).getD 0)) member).symm
        have before := (Finset.add_sum_erase _ (fun i => base i * flagWeight
          ((participation.data[i]?).getD 0)) member).symm
        rw [others, read attester.toNat] at after
        simp only [↓reduceIte] at after
        rw [own] at before
        omega
    · cases stepped

private theorem grow_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (early : fork < .glamsterdam)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    FlagsGrow s t := by
  unfold processAttestation at computed
  split at computed
  · simp only [processAttestationAltair, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨updated, numerator⟩, folded, _, _, raised, raisedOk, final⟩ := computed
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
    simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
    subst final
    obtain ⟨kept, -⟩ := foldlM_addAttesterFlags_grow (base := fun _ => 0) (count := 0) folded
    refine FlagsGrow.trans (fun _ i flag => ?_) (grow_increaseBalance raisedOk)
    unfold setEpochParticipation
    split
    · rename_i current
      simp only [current, ↓reduceIte] at kept
      exact ⟨id, kept i flag⟩
    · rename_i current
      simp only [current, Bool.false_eq_true, ↓reduceIte] at kept
      exact ⟨kept i flag, id⟩
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  all_goals
    obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact FlagsGrow.of_eq

/-- A new validator clears no flag of an existing validator. -/
private theorem growBelow_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry s pubkey withdrawalCredentials amount = .ok t) :
    FlagsGrowBelow s t := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨index, indexOk, _, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ :=
      computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    intro _ i _ inside
    have other : i ≠ index.toNat := by omega
    refine ⟨fun set => ?_, fun set => ?_⟩
    · dsimp only
      simpa only [setOrAppendList_getElem? previousOk, other, ↓reduceIte] using set
    · dsimp only
      simpa only [setOrAppendList_getElem? currentOk, other, ↓reduceIte] using set
  split at computed
  · cases computed
    exact (FlagsGrow.of_eq).below
  · cases computed

/-- Take a step that clears no existing flag, and then a step that clears no flag.

Together they clear no existing flag. -/
private theorem FlagsGrowBelow.trans_grow {u : BeaconState preset fork}
    (one : FlagsGrowBelow s u) (two : FlagsGrow u t) : FlagsGrowBelow s t :=
  fun altair i flag inside =>
    ⟨fun set => (two altair i flag).1 ((one altair i flag inside).1 set),
      fun set => (two altair i flag).2 ((one altair i flag inside).2 set)⟩

/-- Applying a deposit clears no flag of an existing validator. -/
private theorem growBelow_applyDeposit {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDeposit config checks s pubkey withdrawalCredentials amount signature =
      .ok t) : FlagsGrowBelow s t := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (growBelow_addValidatorToRegistry added).trans_grow FlagsGrow.of_eq
      · cases computed
        exact (FlagsGrow.refl _).below
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact (FlagsGrow.of_eq).below
  · rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact (FlagsGrow.refl _).below
    · exact (grow_increaseBalance raised).below
    · exact growBelow_addValidatorToRegistry added

/-- A deposit clears no flag of an existing validator.

A new validator writes its zero flags at the position after the registry.

That position may already hold flags when the lists are longer than the registry. -/
private theorem grow_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before s deposit = .ok t) :
    FlagsGrowBelow s t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact FlagsGrowBelow.trans (u := { s with eth1DepositIndex := fun _ => next })
    (FlagsGrow.of_eq).below (growBelow_applyDeposit applied) (Nat.le_refl _)

private theorem grow_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : FlagsGrow s t := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact grow_initiateValidatorExit exited

private theorem grow_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) : FlagsGrow s t := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    refine FlagsGrow.foldlM (fun _ _ _ ok => ?_) computed
    obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
    exact grow_setValidator set
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ FlagsGrow.refl _

/-- A deposit request clears no flag. -/
private theorem grow_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest s electra request = .ok t) : FlagsGrow s t := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact FlagsGrow.of_eq

/-- The churn of exits clears no flag. -/
private theorem grow_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed : computeExitEpochAndUpdateChurn config s electra exitBalance = .ok (t, epoch)) :
    FlagsGrow s t := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact FlagsGrow.of_eq

/-- The churn of consolidations clears no flag. -/
private theorem grow_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    FlagsGrow s t := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact FlagsGrow.of_eq

/-- A partial withdrawal request clears no flag. -/
private theorem grow_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    FlagsGrow s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (grow_computeExitEpochAndUpdateChurn churned).trans FlagsGrow.of_eq
  · cases computed
    exact FlagsGrow.refl _

/-- A withdrawal request clears no flag. -/
private theorem grow_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config s electra request = .ok t) : FlagsGrow s t := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact FlagsGrow.refl _)
    | exact grow_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact grow_requestPartialWithdrawal computed

/-- Moving the excess balance to the deposit queue clears no flag. -/
private theorem grow_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance s electra index = .ok t) : FlagsGrow s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact FlagsGrow.of_eq
  · cases computed
    exact FlagsGrow.refl _

/-- Switching to compounding credentials clears no flag. -/
private theorem grow_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator s electra index = .ok t) : FlagsGrow s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  exact (grow_setValidator set).trans (grow_queueExcessActiveBalance queued)

/-- Queueing a consolidation clears no flag. -/
private theorem grow_queueConsolidation {electra : .pectra ≤ fork} {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    FlagsGrow s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (grow_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (grow_setValidator set).trans FlagsGrow.of_eq

/-- A consolidation request clears no flag. -/
private theorem grow_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) : FlagsGrow s t := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact FlagsGrow.refl _)
    | exact grow_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact grow_queueConsolidation computed

private theorem grow_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : FlagsGrow s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (FlagsGrow.foldlM (fun _ _ _ ok => grow_processDepositRequest ok) depositsOk).trans <|
    (FlagsGrow.foldlM (fun _ _ _ ok => grow_processWithdrawalRequest ok) withdrawalsOk).trans <|
    FlagsGrow.foldlM (fun _ _ _ ok => grow_processConsolidationRequest ok) consolidationsOk

/-- The reward or penalty of one member of the sync committee clears no flag. -/
private theorem grow_applySyncReward {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward proposer s member = .ok t) :
    FlagsGrow s t := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, raised, _, _, paid⟩ := computed
    exact (grow_increaseBalance raised).trans (grow_increaseBalance paid)
  · exact grow_decreaseBalance (liftAccessor_ok.mp computed)

private theorem grow_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    FlagsGrow s t := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact FlagsGrow.foldlM (fun _ _ _ ok => grow_applySyncReward ok) folded

/-- An attester of an attestation holds a validator at its position.

That validator is active in the epoch of the slot. -/
private theorem isActiveAt_of_getAttestingIndices {attestation : Attestation preset fork}
    {attesters : List ValidatorIndex} (computed : getAttestingIndices s attestation = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    isActiveAt s (computeEpochAtSlot preset attestation.data.slot) attester.toNat = true := by
  obtain ⟨_, _, -, committeeOk, -⟩ :=
    exists_mem_getBeaconCommittee_of_getAttestingIndices computed mem
  obtain ⟨_, _, shuffleOk⟩ := attesterShuffle_ok_of_getBeaconCommittee committeeOk
  simp only [attesterShuffle, bind_ok_iff] at shuffleOk
  obtain ⟨_, _, indices, indicesOk, _⟩ := shuffleOk
  have member : attester ∈ indices := by
    rw [getActiveValidatorIndicesChecked_ok indicesOk]
    exact mem_getActiveValidatorIndices_of_getAttestingIndices computed mem
  exact isActiveAt_eq_true_iff.mpr
    ((mem_iff_of_getActiveValidatorIndicesChecked_ok indicesOk).mp member)

/-- From Altair, this bounds the proposer reward of an attestation by its newly set flags.

448 times that reward is at most what those flags add to the potential.

Take each validator active in the previous or the current epoch.

Its weight must be the base reward that the attestation reads for it. -/
private theorem attestationCredit_potential {attestation : Attestation preset fork}
    {parent : Slot} (altair : .altair ≤ fork) (early : fork < .glamsterdam)
    (computed : processAttestation config checks s parent attestation = .ok t)
    {credit : ℕ} (credited : attestationCredit s attestation parent = .ok credit)
    (base : ℕ → ℕ) {count : ℕ} (big : 2 ^ 64 ≤ count)
    (reads : ∀ (index : ValidatorIndex) (total reward : Gwei),
      (isActiveAt s (getPreviousEpoch s) index.toNat = true ∨
        isActiveAt s (getCurrentEpoch s) index.toNat = true) →
      getTotalActiveBalance s = .ok total → getBaseReward s total index = .ok reward →
      reward.toNat = base index.toNat) :
    credit * ((WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
        PROPOSER_WEIGHT.toNat) + flagPotential s altair base count ≤
      flagPotential t altair base count := by
  simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair, bind_ok_iff,
    ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _,
    total, totalOk, attesters, attestersOk, ⟨updated, numerator⟩, folded, _, _, raised, raisedOk,
    final⟩ := computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
  subst final
  -- The credit is the numerator over 448, rounded down.
  have value : attestationCredit s attestation parent = .ok (numerator /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat := by
    simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
      attestersOk, Except.mapError, bind, Except.bind, folded]
    rfl
  rw [value, Except.ok.injEq] at credited
  subst credited
  have denominator : ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT).toNat = 448 := by decide
  have denominatorNat : (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) *
      WEIGHT_DENOMINATOR.toNat / PROPOSER_WEIGHT.toNat = 448 := by decide
  rw [UInt64.toNat_div, denominator, denominatorNat]
  have key : ∀ a b c d : ℕ, a + c ≤ d → a / 448 * 448 + (c + b) ≤ d + b := by
    intro a b c d le
    calc a / 448 * 448 + (c + b) ≤ a + (c + b) :=
          Nat.add_le_add_right (Nat.div_mul_le_self a 448) _
      _ = a + c + b := (Nat.add_assoc _ _ _).symm
      _ ≤ d + b := Nat.add_le_add_right le b
  -- Each attester is inside the range and reads its weight as its base reward.
  have facts : ∀ attester ∈ attesters, attester.toNat < count ∧
      ∀ reward, getBaseReward s total attester = .ok reward →
        reward.toNat = base attester.toNat := by
    intro attester member
    refine ⟨Nat.lt_of_lt_of_le attester.toNat_lt big, fun reward rewardOk => ?_⟩
    have active := isActiveAt_of_getAttestingIndices attestersOk member
    rw [← slotEpoch] at active
    refine reads attester total reward ?_ totalOk rewardOk
    rcases recent with previous | current
    · exact .inl (previous ▸ active)
    · exact .inr (current ▸ active)
  obtain ⟨-, gained⟩ := foldlM_addAttesterFlags_grow (base := base) (count := count) folded
  have more := gained facts
  -- The balance step keeps both lists of flags.
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [UInt64.toNat_zero, Nat.zero_add] at more
  unfold flagPotential
  simp only [Nat.mul_add, Finset.sum_add_distrib]
  unfold setEpochParticipation
  split
  · rename_i current
    simp only [current, ↓reduceIte] at more
    dsimp only [BeaconState.putBalance]
    rw [Nat.add_comm (∑ x ∈ Finset.range count, _ * flagWeight
      (((s.previousEpochParticipation altair).data[x]?).getD 0)),
      Nat.add_comm _ (∑ x ∈ Finset.range count, _ * flagWeight
        ((updated.data[x]?).getD 0))]
    exact key _ _ _ _ more
  · rename_i current
    simp only [current, Bool.false_eq_true, ↓reduceIte] at more
    dsimp only [BeaconState.putBalance]
    exact key _ _ _ _ more

end Grow

/-! ### Steps that keep the proposer, the active validators and the base rewards -/

section Kept

variable {fork : Fork} {s u t : BeaconState preset fork}

/-- A step that keeps the inputs of the proposer draw, activity and effective balances. -/
private structure Kept (s t : BeaconState preset fork) : Prop where
  frame : Frame s t
  inputs : PayloadInputs s t
  keeps : StepKeeps s t
  effective : EffectiveKept s t

private theorem Kept.refl (s : BeaconState preset fork) : Kept s s :=
  ⟨Frame.refl s, PayloadInputs.refl s, StepKeeps.refl s, effectiveKept_refl s⟩

private theorem Kept.trans (one : Kept s u) (two : Kept u t) : Kept s t :=
  ⟨one.frame.trans two.frame, one.inputs.trans two.inputs, one.keeps.trans two.keeps,
    effectiveKept_trans one.effective two.effective one.keeps.1⟩

/-- A step that keeps the slot, activity up to the fixed epoch and effective balances. -/
private structure Steady (s t : BeaconState preset fork) : Prop where
  keeps : StepKeeps s t
  effective : EffectiveKept s t

private theorem Steady.trans (one : Steady s u) (two : Steady u t) : Steady s t :=
  ⟨one.keeps.trans two.keeps, effectiveKept_trans one.effective two.effective one.keeps.1⟩

private theorem Kept.steady (kept : Kept s t) : Steady s t := ⟨kept.keeps, kept.effective⟩

/-- The effective balances below the old registry size, read as options. -/
private theorem Steady.effective_map (kept : Steady s t) (j : ℕ)
    (inside : j < s.validators.data.size) :
    (s.validators.data[j]?).map (·.effectiveBalance) =
      (t.validators.data[j]?).map (·.effectiveBalance) := by
  have same := kept.effective j inside
  have later : j < t.validators.data.size := Nat.lt_of_lt_of_le inside kept.keeps.1
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem later,
    Option.map_some, Option.getD_some] at same ⊢
  exact congrArg some (UInt64.toNat_inj.mp same.symm)

/-- A steady step keeps the epochs. -/
private theorem Steady.epoch (kept : Steady s t) : getCurrentEpoch t = getCurrentEpoch s := by
  simp only [getCurrentEpoch, kept.keeps.2.1]

/-- A steady step keeps the total active balance. -/
private theorem Steady.total (kept : Steady s t) :
    getTotalActiveBalance t = getTotalActiveBalance s :=
  ExitChurn.totalActiveBalance_eq kept.epoch
    (fun epoch le => kept.keeps.2.2 epoch (UInt64.le_trans le
      (getCurrentEpoch_le_activityFixedEpoch s))) kept.keeps.1
    fun i v found => by
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have same := kept.effective_map i inside
      rw [found] at same
      cases later : t.validators.data[i]? with
      | none => simp [later] at same
      | some w =>
        simp only [later, Option.map_some, Option.some.injEq] at same
        exact ⟨w, rfl, same.symm⟩

/-- The base reward reads only the effective balance of its validator and the total. -/
private theorem getBaseReward_congr {total : Gwei} {index : ValidatorIndex}
    (same : (t.validators.data[index.toNat]?).map (·.effectiveBalance) =
      (s.validators.data[index.toNat]?).map (·.effectiveBalance)) :
    getBaseReward t total index = getBaseReward s total index := by
  unfold getBaseReward getValidator
  cases hs : s.validators.data[index.toNat]? <;> cases ht : t.validators.data[index.toNat]? <;>
    simp only [hs, ht, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at same
  · simp
  · simp only [bind, Except.bind, same]

/-- The base rewards that a kept step reads at the active validators.

These validators are active in the previous or the current epoch. -/
private def Reads (s : BeaconState preset fork) (base : ℕ → ℕ) : Prop :=
  ∀ (index : ValidatorIndex) (total reward : Gwei),
    (isActiveAt s (getPreviousEpoch s) index.toNat = true ∨
      isActiveAt s (getCurrentEpoch s) index.toNat = true) →
    getTotalActiveBalance s = .ok total → getBaseReward s total index = .ok reward →
    reward.toNat = base index.toNat

private theorem Steady.reads (kept : Steady s t) {base : ℕ → ℕ} (reads : Reads s base) :
    Reads t base := by
  intro index total reward recent totalOk rewardOk
  have previous : getPreviousEpoch t = getPreviousEpoch s := by
    unfold getPreviousEpoch; rw [kept.epoch]
  have fixed := getCurrentEpoch_le_activityFixedEpoch s
  have previousLe : getPreviousEpoch s ≤ activityFixedEpoch s := by
    exact UInt64.le_trans (getPreviousEpoch_le s) fixed
  rw [previous, kept.epoch, kept.keeps.2.2 _ previousLe, kept.keeps.2.2 _ fixed] at recent
  -- An active validator is in the old registry.
  have inside : index.toNat < s.validators.data.size := by
    rcases recent with active | active <;>
    · unfold isActiveAt at active
      cases found : s.validators.data[index.toNat]? with
      | none => simp [found] at active
      | some _ => exact (Array.getElem?_eq_some_iff.mp found).1
  rw [kept.total] at totalOk
  rw [getBaseReward_congr (kept.effective_map _ inside).symm] at rewardOk
  exact reads index total reward recent totalOk rewardOk


private theorem Kept.effective_map (kept : Kept s t) (j : ℕ) (inside : j < s.validators.data.size) :
    (s.validators.data[j]?).map (·.effectiveBalance) =
      (t.validators.data[j]?).map (·.effectiveBalance) := kept.steady.effective_map j inside

private theorem Kept.reads (kept : Kept s t) {base : ℕ → ℕ} (reads : Reads s base) :
    Reads t base := kept.steady.reads reads

/-- A kept step keeps the proposer of the slot. -/
private theorem Kept.proposer (kept : Kept s t) :
    getBeaconProposerIndex t = getBeaconProposerIndex s :=
  getBeaconProposerIndex_congr kept.inputs.slot kept.inputs.randaoMixes
    (fun fulu => by rw [kept.inputs.proposerLookahead])
    (kept.keeps.2.2.getActiveValidatorIndicesChecked_eq (getCurrentEpoch_le_activityFixedEpoch s))
    kept.effective_map

end Kept

section Index

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem index_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) (before : fork < .hegota) :
    t.eth1DepositIndex before = s.eth1DepositIndex before := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  rfl

/-- A fold whose every step keeps the next deposit index keeps it. -/
private theorem depositIndex_foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ a x b, step a x = .ok b → b.eth1DepositIndex = a.eth1DepositIndex)
    {items : List α} {u w : BeaconState preset fork} (computed : items.foldlM step u = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex :=
  foldlM_ok_invariant (fun x : BeaconState preset fork => x.eth1DepositIndex = u.eth1DepositIndex)
    (fun _ _ _ before ok => (each _ _ _ ok).trans before) rfl computed

/-- Applying the expected withdrawals keeps the next deposit index. -/
private theorem depositIndex_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals} {u w : BeaconState preset fork}
    (computed : applyExpectedWithdrawals u capella expected = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : applied.eth1DepositIndex = u.eth1DepositIndex := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact depositIndex_foldlM (fun _ _ _ ok => by rw [applyWithdrawal_eq ok]) appliedOk
  have two : indexed.eth1DepositIndex = applied.eth1DepositIndex := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      rfl
    · cases indexedOk
      rfl
  have three : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → finished.eth1DepositIndex = kept.eth1DepositIndex := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        rfl
      · obtain ⟨_, _, built⟩ := bind_ok_iff.mp ok
        cases built
        rfl
    · cases ok
      rfl
  have queued : (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed).eth1DepositIndex = indexed.eth1DepositIndex := by
    split <;> split <;> rfl
  have four : w.eth1DepositIndex = finished.eth1DepositIndex := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last
      rfl
  exact four.trans ((three _ sweptOk).trans (queued.trans (two.trans one)))

private theorem index_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t)
    (before : fork < .hegota) : t.eth1DepositIndex before = s.eth1DepositIndex before := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    obtain ⟨_, -, -, appliedOk⟩ := processWithdrawals_expected early withdrawnOk
    exact congrFun (depositIndex_applyExpectedWithdrawals appliedOk) before
  · split at computed
    · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
      rfl
    · cases computed
      rfl

private theorem index_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) (before : fork < .hegota) :
    t.eth1DepositIndex before = s.eth1DepositIndex before := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  rfl

private theorem index_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) :
    t.eth1DepositIndex before = s.eth1DepositIndex before := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]

/-- A balance write keeps the next deposit index. -/
private theorem depositIndex_setBalance {u w : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} (set : u.setBalance index balance = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- A balance increase keeps the next deposit index. -/
private theorem depositIndex_increaseBalance {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance u index delta = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  exact depositIndex_setBalance set

/-- A balance decrease keeps the next deposit index. -/
private theorem depositIndex_decreaseBalance {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance u index delta = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  exact depositIndex_setBalance set

/-- A validator write keeps the next deposit index. -/
private theorem depositIndex_setValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (set : u.setValidator index validator = .ok w) : w.eth1DepositIndex = u.eth1DepositIndex := by
  rw [setValidator_eq_setValidatorAt] at set
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  rfl

/-- An exit keeps the next deposit index. -/
private theorem depositIndex_initiateValidatorExit {u w : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config u index = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  refine (depositIndex_setValidator set).trans ?_
  unfold exitQueue at queue
  split at queue
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := queue
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, rfl, _⟩ := queue
    rfl

/-- Slashing a validator keeps the next deposit index. -/
private theorem depositIndex_slashValidator {u w : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config u slashedIndex whistleblowerIndex = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -, loweredOk, -, -,
    raisedOk, lastOk, done⟩ := slashValidator_ok computed
  have cancelled : w.eth1DepositIndex = last.eth1DepositIndex := by
    subst done
    split <;> rfl
  exact cancelled.trans <| (depositIndex_increaseBalance lastOk).trans <|
    (depositIndex_increaseBalance raisedOk).trans <|
    (depositIndex_decreaseBalance loweredOk).trans <|
    (depositIndex_setValidator markedOk).trans (depositIndex_initiateValidatorExit exitedOk)

private theorem index_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t)
    (before : fork < .hegota) :
    t.eth1DepositIndex before = s.eth1DepositIndex before := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact congrFun (depositIndex_slashValidator slashed) before

/-- A conditional slashing keeps the next deposit index. -/
private theorem depositIndex_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    next.1.eth1DepositIndex = step.1.eth1DepositIndex := by
  obtain ⟨u, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact depositIndex_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    rw [← computed]

private theorem index_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t)
    (before : fork < .hegota) : t.eth1DepositIndex before = s.eth1DepositIndex before := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact congrFun (foldlM_ok_invariant
    (fun step : BeaconState preset fork × Bool => step.1.eth1DepositIndex = s.eth1DepositIndex)
    (fun _ _ _ before ok => (depositIndex_slashIfSlashable ok).trans before) rfl folded) before

private theorem index_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (computed : processAttestation config checks s parent attestation = .ok t)
    (before : fork < .hegota) : t.eth1DepositIndex before = s.eth1DepositIndex before := by
  suffices same : t.eth1DepositIndex = s.eth1DepositIndex from congrFun same before
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : t.eth1DepositIndex = raised.eth1DepositIndex := by
      split at final
      · rw [recordPaymentWeight_eq final]
      · cases final
        rfl
    refine last.trans ((depositIndex_increaseBalance raisedOk).trans ?_)
    unfold setEpochParticipation
    split <;> rfl
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
    have kept := recordPendingAttestation_ok recorded
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      rw [← rest]

private theorem index_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) (before : fork < .hegota) :
    t.eth1DepositIndex before = s.eth1DepositIndex before := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact congrFun (depositIndex_initiateValidatorExit exited) before

private theorem index_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t)
    (before : fork < .hegota) : t.eth1DepositIndex before = s.eth1DepositIndex before := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    refine congrFun (depositIndex_foldlM (fun _ _ _ ok => ?_) computed) before
    obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
    exact depositIndex_setValidator set
  · cases computed
    rfl

/-- A partial withdrawal request keeps the next deposit index. -/
private theorem depositIndex_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {u w : BeaconState preset fork} {index : ValidatorIndex} {validator : Validator}
    {amount owed : Gwei}
    (computed : requestPartialWithdrawal config u electra index validator amount owed = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  · cases computed
    rfl

/-- A switch to compounding credentials keeps the next deposit index. -/
private theorem depositIndex_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {u w : BeaconState preset fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator u electra index = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  refine Eq.trans ?_ (depositIndex_setValidator set)
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    have lowered := depositIndex_setBalance set
    exact lowered
  · cases queued
    rfl

/-- A queued consolidation keeps the next deposit index. -/
private theorem depositIndex_queueConsolidation {electra : .pectra ≤ fork}
    {u w : BeaconState preset fork} {sourceIndex : ValidatorIndex} {source : Validator}
    {targetIndex : ValidatorIndex}
    (computed : queueConsolidation config u electra sourceIndex source targetIndex = .ok w) :
    w.eth1DepositIndex = u.eth1DepositIndex := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  have marked := depositIndex_setValidator set
  exact marked

private theorem index_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t)
    (before : fork < .hegota) : t.eth1DepositIndex before = s.eth1DepositIndex before := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  have deposits := depositIndex_foldlM (fun u request w ok => by
    obtain ⟨start, recorded⟩ :=
      recordDepositRequestsStart_eq (state := u) (index := request.index)
    simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    rfl) depositsOk
  have withdrawals := depositIndex_foldlM (fun _ _ _ ok => by
    unfold processWithdrawalRequest at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; rfl)
      | exact depositIndex_initiateValidatorExit (liftAccessor_ok.mp ok)
      | exact depositIndex_requestPartialWithdrawal ok) withdrawalsOk
  have consolidations := depositIndex_foldlM (fun _ _ _ ok => by
    unfold processConsolidationRequest at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; rfl)
      | exact depositIndex_switchToCompoundingValidator (liftAccessor_ok.mp ok)
      | exact depositIndex_queueConsolidation ok) consolidationsOk
  exact congrFun (consolidations.trans (withdrawals.trans deposits)) before

private theorem index_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t)
    (before : fork < .hegota) : t.eth1DepositIndex before = s.eth1DepositIndex before := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine congrFun (depositIndex_foldlM (fun _ _ _ ok => ?_) folded) before
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (depositIndex_increaseBalance paid).trans (depositIndex_increaseBalance raised)
  · exact depositIndex_decreaseBalance (liftAccessor_ok.mp ok)

end Index

section KeptSteps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
    (computed : items.foldlM step s = .ok t) : Kept s t :=
  foldlM_ok_invariant (Kept s) (fun _ _ _ before ok => before.trans (each _ _ _ ok))
    (Kept.refl s) computed

private theorem kept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : Kept s t :=
  ⟨(frame_processProposerSlashing computed).toFrame, payloadInputs_processProposerSlashing computed,
    stepKeeps_processProposerSlashing computed, effectiveKept_proposerSlashing computed⟩

private theorem kept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : Kept s t :=
  ⟨(frame_processAttesterSlashing computed).toFrame,
    payloadInputs_processAttesterSlashing computed, stepKeeps_processAttesterSlashing computed,
    effectiveKept_attesterSlashing computed⟩

private theorem kept_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (computed : processAttestation config checks s parent attestation = .ok t) : Kept s t :=
  ⟨frame_processAttestation computed, payloadInputs_processAttestation computed,
    stepKeeps_processAttestation computed,
    effectiveKept_data (by rw [(processAttestation_registry computed).1])⟩

/-- A new validator keeps the inputs of a payload. -/
private theorem payloadInputs_addValidatorToRegistry' {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry s pubkey withdrawalCredentials amount = .ok t) :
    PayloadInputs s t := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  split at computed
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases computed

private theorem payloadInputs_processDeposit' {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before s deposit = .ok t) : PayloadInputs s t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine PayloadInputs.trans (second := { s with eth1DepositIndex := fun _ => next })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  unfold applyDeposit at applied
  split at applied
  · unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨_, added, pushed⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (payloadInputs_addValidatorToRegistry' added).trans
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases applied
        exact PayloadInputs.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rcases applyPendingDeposit_cases applied with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact PayloadInputs.refl _
    · exact payloadInputs_increaseBalance raised
    · exact payloadInputs_addValidatorToRegistry' added

private theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before s deposit = .ok t) : Kept s t :=
  ⟨(frame_processDeposit computed).toFrame, payloadInputs_processDeposit' computed,
    stepKeeps_processDeposit computed, effectiveKept_processDeposit computed⟩

private theorem kept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Kept s t :=
  ⟨(frame_processVoluntaryExit computed).toFrame, payloadInputs_processVoluntaryExit computed,
    stepKeeps_processVoluntaryExit computed, effectiveKept_voluntaryExit computed⟩

private theorem kept_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) : Kept s t := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    exact Kept.foldlM (fun _ _ _ ok => ⟨(frame_processBlsToExecutionChange ok).toFrame,
      payloadInputs_processBlsToExecutionChange ok, stepKeeps_processBlsToExecutionChange ok,
      effectiveKept_blsChange ok⟩) computed
  · cases computed; exact Kept.refl _

private theorem kept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : Kept s t := by
  have inputs : PayloadInputs s t := by
    have ok := computed
    simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
    exact (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processDepositRequest ok)
      deposits).trans <| (PayloadInputs.foldlM
        (fun _ _ _ ok => payloadInputs_processWithdrawalRequest ok) withdrawals).trans <|
      PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processConsolidationRequest ok)
        consolidations
  exact ⟨(frame_processExecutionRequests computed).toFrame, inputs,
    stepKeeps_processExecutionRequests computed, effectiveKept_requests computed⟩

end KeptSteps

/-! ### The operations of a block -/

/-- The divisor of the proposer reward of an attestation, `(64 - 8) * 64 / 8 = 448`. -/
private abbrev proposerDenominator : ℕ :=
  (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
    PROPOSER_WEIGHT.toNat

/-- What some operations of a block do to the balances.

The credits other than sync go to the proposer of the slot, from attestations and slashings.

Before Electra, they also go to the recipients of deposits.

The slashed validators were not slashed before, and pay their initial penalty.

The proposer reward of the attestations is bounded by the flags they set. -/
private structure Credited {fork : Fork} (o t : BeaconState preset fork)
    (proposer : ValidatorIndex) (credit : ℕ) (slashed deposited conv : Finset ValidatorIndex)
    (other slash : ValidatorIndex → ℕ) : Prop where
  ledger : Ledger o t ∅ conv 0 other slash
  kept : Kept o t
  grow : FlagsGrowBelow o t
  read : 0 < credit ∨ slashed.Nonempty → getBeaconProposerIndex o = .ok proposer
  credited : ∀ v, v ∉ deposited → other v ≤ if v = proposer then
    credit + ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0
  penalized : ∀ v, slash v ≤ if v ∈ slashed then effectiveAt ⟨fork, t⟩ v.toNat /
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
  newly : ∀ v ∈ slashed, (∀ validator, o.validators.data[v.toNat]? = some validator →
      validator.slashed = false) ∧
    ∃ later, t.validators.data[v.toNat]? = some later ∧ later.slashed = true
  potential : ∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count →
    Reads o base → (∀ i, o.validators.data.size ≤ i → base i = 0) →
    credit * proposerDenominator + flagPotential o altair base count ≤
      flagPotential t altair base count
  phase0 : fork < .altair → credit = 0
  electra : .pectra ≤ fork → deposited = ∅
  deposits : ∀ before : fork < .hegota,
    (o.eth1DepositIndex before).toNat + deposited.card ≤ (t.eth1DepositIndex before).toNat

section Credited

variable {fork : Fork} {o u t : BeaconState preset fork}

/-- A kept step that moves no balance and keeps the deposit index credits nothing. -/
private theorem Credited.of_ledger (ledger : Ledger o t ∅ ∅ 0 0 0) (kept : Kept o t)
    (grow : FlagsGrowBelow o t)
    (index : ∀ before : fork < .hegota, t.eth1DepositIndex before = o.eth1DepositIndex before) :
    Credited o t 0 0 ∅ ∅ ∅ 0 0 where
  ledger := ledger
  kept := kept
  grow := grow
  read hyp := by simp at hyp
  credited v _ := by simp
  penalized v := by simp
  newly v member := absurd member (Finset.notMem_empty v)
  potential altair base count _ _ support := by
    simpa using flagPotential_mono_below grow altair base count support
  phase0 _ := rfl
  electra _ := rfl
  deposits before := by simp [index before]

/-- An effective balance at a later kept state is the one before, for an existing validator. -/
private theorem effectiveAt_of_kept (kept : Kept u t) {v : ValidatorIndex} {validator : Validator}
    (found : u.validators.data[v.toNat]? = some validator) :
    effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, u⟩ v.toNat :=
  kept.effective v.toNat (Array.getElem?_eq_some_iff.mp found).1

private theorem Credited.trans {proposer proposer' : ValidatorIndex} {credit credit' : ℕ}
    {slashed slashed' deposited deposited' conv conv' : Finset ValidatorIndex}
    {other other' slash slash' : ValidatorIndex → ℕ}
    (one : Credited o u proposer credit slashed deposited conv other slash)
    (two : Credited u t proposer' credit' slashed' deposited' conv' other' slash') :
    Credited o t (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer)
      (credit + credit') (slashed ∪ slashed') (deposited ∪ deposited') (conv ∪ conv')
      (other + other') (slash + slash') := by
  -- No validator is slashed in both parts.
  have apart : ∀ v ∈ slashed, v ∉ slashed' := by
    intro v first second
    obtain ⟨later, found, marked⟩ := (one.newly v first).2
    rw [(two.newly v second).1 later found] at marked
    cases marked
  have disjoint : Disjoint slashed slashed' := Finset.disjoint_left.mpr apart
  -- The effective balance of a validator slashed in the first part stays to the end.
  have kept : ∀ v ∈ slashed, effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, u⟩ v.toNat := by
    intro v member
    obtain ⟨later, found, _⟩ := (one.newly v member).2
    exact effectiveAt_of_kept two.kept found
  have sumKept : ∑ x ∈ slashed, effectiveAt ⟨fork, u⟩ x.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
      ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun x member => by rw [kept x member]
  have proposerSame : getBeaconProposerIndex u = getBeaconProposerIndex o := one.kept.proposer
  refine ⟨by simpa using one.ledger.trans two.ledger, one.kept.trans two.kept,
    one.grow.trans two.grow one.kept.frame.registryGrows, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro positive
    split
    · rename_i later
      exact proposerSame ▸ two.read later
    · rename_i none
      have zero : credit' = 0 ∧ slashed' = ∅ := by
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at none
        exact none
      apply one.read
      rcases positive with positive | nonempty
      · left; omega
      · right; rw [zero.2, Finset.union_empty] at nonempty; exact nonempty
  · -- Each part credits the proposer of the whole, or nothing.
    have moved {x c : ℕ} {q : ValidatorIndex} (v : ValidatorIndex)
        (bound : x ≤ if v = q then c else 0)
        (same : c = 0 ∨ q = (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer)) :
        x ≤ if v = (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer) then c
          else 0 := by
      rcases same with zero | same
      · subst zero; split at bound <;> simp_all
      · rw [← same]; exact bound
    intro v absent
    simp only [Finset.mem_union, not_or] at absent
    have first := one.credited v absent.1
    have second := two.credited v absent.2
    rw [sumKept] at first
    have first' := moved v first (by
      by_cases earlier : 0 < credit ∨ slashed.Nonempty
      · right
        split
        · rename_i later
          have := one.read earlier
          rw [← proposerSame, two.read later] at this
          exact (Except.ok.inj this).symm
        · rfl
      · left
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at earlier
        simp [earlier.1, earlier.2])
    have second' := moved v second (by
      by_cases later : 0 < credit' ∨ slashed'.Nonempty
      · right; simp only [later, ↓reduceIte]
      · left
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at later
        simp [later.1, later.2])
    simp only [Pi.add_apply]
    rw [Finset.sum_union disjoint]
    have total := Nat.add_le_add first' second'
    generalize (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer) = chosen at total ⊢
    by_cases same : v = chosen
    · simp only [same, ↓reduceIte] at total ⊢; omega
    · simp only [same, ↓reduceIte] at total ⊢; omega
  · intro v
    simp only [Pi.add_apply]
    have first := one.penalized v
    have second := two.penalized v
    by_cases member : v ∈ slashed
    · have notSecond := apart v member
      simp only [member, notSecond, ↓reduceIte, Finset.mem_union, true_or] at first second ⊢
      rw [kept v member]
      omega
    · by_cases member' : v ∈ slashed'
      · simp only [member, member', ↓reduceIte, Finset.mem_union, or_true] at first second ⊢
        omega
      · simp only [member, member', ↓reduceIte, Finset.mem_union, or_self] at first second ⊢
        omega
  · intro v member
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨unslashed, later, found, marked⟩ := one.newly v first
      obtain ⟨final, finalFound, -⟩ :=
        (two.kept.frame.registryGrows) |> fun _ => (⟨later, found, marked⟩ :
          ∃ later, u.validators.data[v.toNat]? = some later ∧ later.slashed = true)
      have inside : v.toNat < t.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 two.kept.frame.registryGrows
      refine ⟨unslashed, t.validators.data[v.toNat], Array.getElem?_eq_getElem inside, ?_⟩
      exact two.kept.frame.slashed v.toNat later _ found (Array.getElem?_eq_getElem inside) marked
    · refine ⟨fun validator found => ?_, (two.newly v second).2⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have middle : v.toNat < u.validators.data.size :=
        Nat.lt_of_lt_of_le inside one.kept.frame.registryGrows
      have unslashed := (two.newly v second).1 _ (Array.getElem?_eq_getElem middle)
      cases flag : validator.slashed
      · rfl
      · have := one.kept.frame.slashed v.toNat validator _ found
          (Array.getElem?_eq_getElem middle) flag
        rw [unslashed] at this
        cases this
  · intro altair base count big reads support
    have first := one.potential altair base count big reads support
    have second := two.potential altair base count big (one.kept.reads reads) fun i outside =>
      support i (Nat.le_trans one.kept.frame.registryGrows outside)
    rw [Nat.add_mul]
    omega
  · intro early
    rw [one.phase0 early, two.phase0 early]
  · intro electra
    rw [one.electra electra, two.electra electra, Finset.union_empty]
  · intro before
    have first := one.deposits before
    have second := two.deposits before
    have := Finset.card_union_le deposited deposited'
    omega

/-- A fold of steps that each credit like operations, and convert nothing, does so too. -/
private theorem Credited.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, BalancesMatch a → step a x = .ok b →
      ∃ p c sl d o sh, Credited a b p c sl d ∅ o sh)
    {items : List α} (matched : BalancesMatch o) (computed : items.foldlM step o = .ok t) :
    ∃ p c sl d o' sh, Credited o t p c sl d ∅ o' sh := by
  refine foldlM_ok_invariant (fun b => ∃ p c sl d o' sh, Credited o b p c sl d ∅ o' sh)
    (fun a x b ⟨_, _, _, _, _, _, before⟩ ok => ?_)
    ⟨0, 0, ∅, ∅, 0, 0, Credited.of_ledger (Ledger.refl o) (Kept.refl o) (FlagsGrow.refl o).below
      fun _ => rfl⟩ computed
  obtain ⟨_, _, _, _, _, _, next⟩ := each a x b (before.kept.frame.balancesMatch matched) ok
  have joined := before.trans next
  rw [Finset.empty_union] at joined
  exact ⟨_, _, _, _, _, _, joined⟩

end Credited

section CreditedSteps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem effectiveAt_eq_of_found {validator : Validator}
    (found : s.validators.data[i]? = some validator) :
    effectiveAt ⟨fork, s⟩ i = validator.effectiveBalance.toNat := by
  simp [effectiveAt, found]

private theorem credited_processProposerSlashing {slashing : ProposerSlashing}
    (early : fork < .glamsterdam)
    (computed : processProposerSlashing config checks s slashing = .ok t) :
    ∃ p c sl d o sh, Credited s t p c sl d ∅ o sh := by
  obtain ⟨proposer, slashed, validator, read, found, unslashed, ⟨later, laterFound, marked⟩,
    ledger⟩ := ledger_processProposerSlashing early computed
  have kept := kept_processProposerSlashing computed
  have grow := (grow_processProposerSlashing computed).below
  have effective : effectiveAt ⟨fork, t⟩ slashed.toNat = validator.effectiveBalance.toNat :=
    (effectiveAt_of_kept kept found).trans (effectiveAt_eq_of_found found)
  refine ⟨proposer, 0, {slashed}, ∅, _, _, ledger, kept, grow, fun _ => read,
    fun v _ => ?_, fun v => ?_, fun v member => ?_, fun altair base count _ _ support => ?_,
    fun _ => rfl, fun _ => rfl, fun before => ?_⟩
  · simp only [Finset.sum_singleton, effective, zero_add]; exact le_rfl
  · by_cases same : v = slashed
    · subst same; simp [effective]
    · simp [same]
  · rw [Finset.mem_singleton.mp member]
    exact ⟨fun other found' => by rw [found] at found'; cases found'; exact unslashed,
      later, laterFound, marked⟩
  · simpa using flagPotential_mono_below grow altair base count support
  · simp [index_processProposerSlashing computed before]

private theorem credited_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (early : fork < .glamsterdam)
    (computed : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ p c sl d o sh, Credited s t p c sl d ∅ o sh := by
  obtain ⟨proposer, slashed, read, newly, ledger⟩ := ledger_processAttesterSlashing early computed
  have kept := kept_processAttesterSlashing computed
  have grow := (grow_processAttesterSlashing computed).below
  have effective : ∀ v ∈ slashed, effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, s⟩ v.toNat :=
    fun v member => by
      obtain ⟨validator, _, found, _⟩ := newly v member
      exact effectiveAt_of_kept kept found
  refine ⟨proposer, 0, slashed, ∅, _, _, ledger, kept, grow,
    fun hyp => read (by simpa using hyp), fun v _ => ?_, fun v => ?_, fun v member => ?_,
    fun altair base count _ _ support => ?_, fun _ => rfl, fun _ => rfl, fun before => ?_⟩
  · have same : ∑ x ∈ slashed, effectiveAt ⟨fork, s⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun x member => by rw [effective x member]
    simp only [same, zero_add]; exact le_rfl
  · split
    · rename_i member; rw [effective v member]
    · exact le_rfl
  · obtain ⟨validator, later, found, unslashed, laterFound, marked⟩ := newly v member
    exact ⟨fun other found' => by rw [found] at found'; cases found'; exact unslashed,
      later, laterFound, marked⟩
  · simpa using flagPotential_mono_below grow altair base count support
  · simp [index_processAttesterSlashing computed before]

private theorem credited_processAttestation {attestation : Attestation preset fork}
    {parent : Slot} (early : fork < .glamsterdam)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    ∃ p c sl d o sh, Credited s t p c sl d ∅ o sh := by
  obtain ⟨proposer, credit, credited, read, ledger⟩ := ledger_processAttestation early computed
  have kept := kept_processAttestation computed
  have grow := (grow_processAttestation early computed).below
  refine ⟨proposer, credit, ∅, ∅, _, _, ledger, kept, grow,
    fun hyp => read (by simpa using hyp), fun v _ => by simp, fun v => by simp,
    fun v member => absurd member (Finset.notMem_empty v), fun altair base count big reads _ => ?_,
    fun before => ?_, fun _ => rfl, fun before => ?_⟩
  · exact attestationCredit_potential altair early computed credited base big reads
  · have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
    simp [attestationCredit, notAltair, pure, Except.pure] at credited
    exact credited.symm
  · simp [index_processAttestation computed before]

private theorem credited_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (matched : BalancesMatch s)
    (computed : processDeposit config checks before s deposit = .ok t) :
    ∃ p c sl d o sh, Credited s t p c sl d ∅ o sh := by
  obtain ⟨recipient, index, ledger⟩ := ledger_processDeposit matched computed
  have kept := kept_processDeposit computed
  have grow := grow_processDeposit computed
  refine ⟨recipient, 0, ∅, if fork < .pectra then {recipient} else ∅, _, _, ledger, kept,
    grow, fun hyp => by simp at hyp, fun v absent => ?_, fun v => by simp,
    fun v member => absurd member (Finset.notMem_empty v),
    fun altair base count _ _ support => by
      simpa using flagPotential_mono_below grow altair base count support,
    fun _ => rfl, fun electra => by
      have notBefore : ¬ fork < .pectra := Nat.not_lt_of_le electra
      simp [notBefore], fun before' => ?_⟩
  · by_cases credited : v = recipient ∧ fork < .pectra
    · simp [credited.1, credited.2] at absent
    · simp [credited]
  · split <;> simp <;> omega

private theorem credited_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) :
    ∃ p c sl d o sh, Credited s t p c sl d ∅ o sh :=
  ⟨_, _, _, _, _, _, Credited.of_ledger (ledger_processVoluntaryExit computed)
    (kept_processVoluntaryExit computed) (grow_processVoluntaryExit computed).below
    (index_processVoluntaryExit computed)⟩

private theorem credited_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) :
    ∃ p c sl d o sh, Credited s t p c sl d ∅ o sh :=
  ⟨_, _, _, _, _, _, Credited.of_ledger (ledger_processBlsToExecutionChanges computed)
    (kept_processBlsToExecutionChanges computed)
    (grow_processBlsToExecutionChanges computed).below
    (index_processBlsToExecutionChanges computed)⟩

private theorem credited_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) :
    ∃ conv, Credited s t 0 0 ∅ ∅ conv 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  obtain ⟨conv, ledger, count⟩ := ledger_processExecutionRequests computed
  have grow := (grow_processExecutionRequests computed).below
  exact ⟨conv, ⟨ledger, kept_processExecutionRequests computed, grow, fun hyp => by simp at hyp,
    fun v _ => by simp, fun v => by simp, fun v member => absurd member (Finset.notMem_empty v),
    fun altair base count _ _ support => by
      simpa using flagPotential_mono_below grow altair base count support,
    fun _ => rfl, fun _ => rfl,
    fun before => by simp [index_processExecutionRequests computed before]⟩, count⟩

/-- Before Gloas, the operations of a block credit like operations.

They convert at most one validator for each consolidation request. -/
private theorem credited_processOperations {body : BeaconBlockBody preset fork} {parent : Slot}
    (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (computed : processOperations config checks s body parent = .ok t) :
    ∃ p c sl d cv o sh, Credited s t p c sl d cv o sh ∧
      cv.card ≤ if .pectra ≤ fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat
        else 0 := by
  unfold processOperations at computed
  split at computed
  · rename_i later
    exact False.elim (Nat.not_le_of_lt early later)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, a, proposersOk, b, attestersOk, c, attestationsOk, d, depositsOk, e,
    exitsOk, f, changesOk, requestsOk⟩ := computed
  have step {x y : BeaconState preset fork} {p c sl d o sh p' c' sl' d' cv' o' sh'}
      (one : Credited s x p c sl d ∅ o sh) (two : Credited x y p' c' sl' d' cv' o' sh') :
      ∃ p c sl d o sh, Credited s y p c sl d cv' o sh := by
    have joined := one.trans two
    rw [Finset.empty_union] at joined
    exact ⟨_, _, _, _, _, _, joined⟩
  have matchedAt {x : BeaconState preset fork} {p c sl d o sh}
      (held : Credited s x p c sl d ∅ o sh) : BalancesMatch x :=
    held.kept.frame.balancesMatch matched
  obtain ⟨_, _, _, _, _, _, one⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processProposerSlashing early ok) matched proposersOk
  obtain ⟨_, _, _, _, _, _, two⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processAttesterSlashing early ok) (matchedAt one) attestersOk
  obtain ⟨_, _, _, _, _, _, upTwo⟩ := step one two
  obtain ⟨_, _, _, _, _, _, three⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processAttestation early ok) (matchedAt upTwo) attestationsOk
  obtain ⟨_, _, _, _, _, _, upThree⟩ := step upTwo three
  obtain ⟨_, _, _, _, _, _, four⟩ := Credited.foldlM
    (fun _ _ _ held ok => credited_processDeposit held ok) (matchedAt upThree) depositsOk
  obtain ⟨_, _, _, _, _, _, upFour⟩ := step upThree four
  obtain ⟨_, _, _, _, _, _, five⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processVoluntaryExit ok) (matchedAt upFour) exitsOk
  obtain ⟨_, _, _, _, _, _, upFive⟩ := step upFour five
  obtain ⟨_, _, _, _, _, _, six⟩ := credited_processBlsToExecutionChanges changesOk
  obtain ⟨_, _, _, _, _, _, upSix⟩ := step upFive six
  split at requestsOk
  · rename_i electra
    obtain ⟨conv, seven, count⟩ := credited_processExecutionRequests requestsOk
    obtain ⟨_, _, _, _, _, _, upSeven⟩ := step upSix seven
    exact ⟨_, _, _, _, _, _, _, upSeven, by simpa [electra] using count⟩
  · cases requestsOk
    exact ⟨_, _, _, _, _, _, _, upSix, by simp⟩

/-- Take a fold of steps that each move the deposit index by the same amount.

The fold moves the deposit index by that amount for each step. -/
private theorem index_foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    {before : fork < .hegota} {width : ℕ}
    (each : ∀ a x b, step a x = .ok b →
      (b.eth1DepositIndex before).toNat = (a.eth1DepositIndex before).toNat + width) :
    ∀ {items : List α} {s t : BeaconState preset fork}, items.foldlM step s = .ok t →
      (t.eth1DepositIndex before).toNat = (s.eth1DepositIndex before).toNat + width * items.length
  | [], s, t, computed => by cases computed; simp
  | x :: rest, s, t, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, folded⟩ := computed
    rw [index_foldlM each folded, each s x middle first, List.length_cons, Nat.mul_succ]
    omega

/-- Before Electra, the operations of a block move the deposit index by their deposits.

There are at most `MAX_DEPOSITS` of these deposits. -/
private theorem index_processOperations {body : BeaconBlockBody preset fork} {parent : Slot}
    (early : fork < .glamsterdam) (before : fork < .hegota)
    (computed : processOperations config checks s body parent = .ok t) :
    (t.eth1DepositIndex before).toNat ≤
      (s.eth1DepositIndex before).toNat + preset.MAX_DEPOSITS.toNat := by
  unfold processOperations at computed
  split at computed
  · rename_i later
    exact False.elim (Nat.not_le_of_lt early later)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨expected, expectedOk, sized, _, a, proposersOk, b, attestersOk, c, attestationsOk, d,
    depositsOk, e, exitsOk, f, changesOk, requestsOk⟩ := computed
  have one := index_foldlM (width := 0) (before := before)
    (fun _ _ _ ok => by rw [index_processProposerSlashing ok before]; rfl) proposersOk
  have two := index_foldlM (width := 0) (before := before)
    (fun _ _ _ ok => by rw [index_processAttesterSlashing ok before]; rfl) attestersOk
  have three := index_foldlM (width := 0) (before := before)
    (fun _ _ _ ok => by rw [index_processAttestation ok before]; rfl) attestationsOk
  have four := index_foldlM (width := 1) (before := before)
    (fun _ _ _ ok => by rw [(processDeposit_ok ok).2.1]) depositsOk
  have five := index_foldlM (width := 0) (before := before)
    (fun _ _ _ ok => by rw [index_processVoluntaryExit ok before]; rfl) exitsOk
  have six := index_processBlsToExecutionChanges changesOk before
  have seven : t.eth1DepositIndex before = f.eth1DepositIndex before := by
    split at requestsOk
    · exact index_processExecutionRequests requestsOk before
    · cases requestsOk; rfl
  -- The block carries the expected number of deposits, at most `MAX_DEPOSITS`.
  have least (a b : UInt64) : (min a b).toNat ≤ a.toNat := by
    rw [UInt64.min_def]
    split
    · exact le_rfl
    · rename_i greater
      exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp greater))
  have bound : expected ≤ preset.MAX_DEPOSITS.toNat := by
    unfold expectedDepositCount at expectedOk
    split at expectedOk
    · cases expectedOk; exact Nat.zero_le _
    split at expectedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at expectedOk
      subst expectedOk
      split
      · exact least _ _
      · exact Nat.zero_le _
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at expectedOk
      obtain ⟨_, _, rfl⟩ := expectedOk
      exact least _ _
  simp only [Array.length_toList] at four
  rw [seven, six] at *
  omega

end CreditedSteps

/-! ### One block -/

section Block

variable {fork : Fork} {s t : BeaconState preset fork}

/-- The participant reward of the sync committee reads only the total active balance. -/
private theorem syncParticipantReward_congr
    (total : getTotalActiveBalance t = getTotalActiveBalance s) :
    syncParticipantReward t = syncParticipantReward s := by
  unfold syncParticipantReward
  rw [total]

private theorem steady_of_validators (validators : t.validators.data = s.validators.data)
    (slot : t.slot = s.slot) : Steady s t :=
  ⟨StepKeeps.of_validators validators slot, effectiveKept_data validators⟩

private theorem steady_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : Steady s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact steady_of_validators rfl rfl

private theorem steady_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : Steady s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact steady_of_validators rfl rfl

private theorem steady_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : Steady s t :=
  ⟨stepKeeps_processEth1Data computed, effectiveKept_data (by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
    rw [← rest])⟩

private theorem steady_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    Steady s t := by
  refine ⟨stepKeeps_processBlockExecution computed, ?_⟩
  have payload {a b : BeaconState preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine a body bellatrix = .ok b) :
      b.validators = a.validators := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    rfl
  unfold processBlockExecution at computed
  split at computed
  · exact False.elim (Nat.not_le_of_lt early (by assumption))
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawn, paid⟩ := computed
    intro i inside
    simpa only [effectiveAt, payload paid] using effectiveKept_withdrawals withdrawn i inside
  · dsimp only at computed
    split at computed
    · exact effectiveKept_data (congrArg (·.data) (payload computed))
    · cases computed; exact effectiveKept_refl _

private theorem kept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) : Kept s t :=
  ⟨(frame_processSyncAggregate computed).toFrame, payloadInputs_processSyncAggregate computed,
    stepKeeps_processSyncAggregate computed, effectiveKept_sync computed⟩

/-- The proposer of a slot reads the seed of its epoch, the slot, the lookahead and the registry. -/
private theorem getBeaconProposerIndex_congr_seed {s w : BeaconState preset fork}
    (slot : w.slot = s.slot)
    (seed : getSeed w (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER =
      getSeed s (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER)
    (lookahead : ∀ fulu : .fusaka ≤ fork, w.proposerLookahead fulu = s.proposerLookahead fulu)
    (validators : w.validators.data = s.validators.data) :
    getBeaconProposerIndex w = getBeaconProposerIndex s := by
  have epoch : getCurrentEpoch w = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  have active : getActiveValidatorIndicesChecked w (getCurrentEpoch s) =
      getActiveValidatorIndicesChecked s (getCurrentEpoch s) := by
    unfold getActiveValidatorIndicesChecked; rw [validators]
  have effective : ∀ j < s.validators.data.size, (s.validators.data[j]?).map
      (·.effectiveBalance) = (w.validators.data[j]?).map (·.effectiveBalance) := by
    intro j _; rw [validators]
  unfold getBeaconProposerIndex
  split
  · rename_i fulu
    simp only [slot, lookahead fulu]
  · dsimp only
    rw [epoch, seed, active, slot]
    cases checked : getActiveValidatorIndicesChecked s (getCurrentEpoch s) with
    | error => simp only [bind, Except.bind]
    | ok indices =>
      simp only [bind, Except.bind]
      cases getSeed s (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER with
      | error => simp only
      | ok mix =>
        simp only
        unfold computeProposerIndex
        by_cases empty : indices.toArray.size = 0
        · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
            MonadExceptOf.throw]
        have inside : ∀ index ∈ indices.toArray, index.toNat < s.validators.data.size := by
          intro index member
          obtain ⟨v, found, _⟩ :=
            (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp (by simpa using member)
          exact (Array.getElem?_eq_some_iff.mp found).1
        have positive : 0 < s.validators.data.size := by
          obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil indices
            (fun nil => empty (by simp [nil]))
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) (inside index (by simpa using member))
        simp only [empty, ↓reduceIte]
        rw [proposerSearch_congr_validators positive inside effective]

/-- A write to the RANDAO mix of the current epoch keeps the seed of that epoch.

The ring of mixes must be longer than `MIN_SEED_LOOKAHEAD + 2`. -/
private theorem getSeed_eq_of_mixesKeptBut_current {s w : BeaconState preset fork}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (mixes : MixesKeptBut (getCurrentEpoch s) s w) (domainType : DomainType) :
    getSeed w (getCurrentEpoch s) domainType = getSeed s (getCurrentEpoch s) domainType := by
  refine getSeed_eq_of_mix domainType fun shifted shiftedEq => mixes shifted fun same => ?_
  have same := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
  exact Nat.mod_ne_of_sub_lt (low := (getCurrentEpoch s).toNat) (high := shifted.toNat)
    (length := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (by omega) (by omega) same

/-- Before Altair, the header, RANDAO and eth1 steps of a block keep the proposer of the header. -/
private theorem proposer_of_prefix {before : fork < .hegota} {block : BeaconBlock preset fork}
    {headed revealed voted : BeaconState preset fork} (phase0 : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (headedOk : processBlockHeader s block = .ok headed)
    (revealedOk : processRandao config checks headed block.body = .ok revealed)
    (votedOk : processEth1Data before revealed block.body = .ok voted) :
    getBeaconProposerIndex voted = .ok block.proposerIndex := by
  have proposer := (processBlockHeader_checks headedOk).2.2.1
  have mixesR := mixesKeptBut_processRandao revealedOk
  have slotR := (frame_processRandao revealedOk).slot
  have validatorsR : revealed.validators.data = headed.validators.data := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    rfl
  have inputsV := payloadInputs_processEth1Data votedOk
  have validatorsV : voted.validators.data = revealed.validators.data := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
    rw [← rest]
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
  have mixes : MixesKeptBut (getCurrentEpoch s) s voted := by
    intro epoch other
    rw [inputsV.randaoMixes]
    exact mixesR epoch other
  rw [getBeaconProposerIndex_congr_seed (inputsV.slot.trans slotR)
    (getSeed_eq_of_mixesKeptBut_current apart mixes _)
    (fun fulu => absurd (Nat.lt_of_lt_of_le phase0 (Nat.le_trans (by decide) fulu))
      (Nat.lt_irrefl _)) (validatorsV.trans validatorsR)]
  exact proposer

/-- The balances of a block before Gloas, read at each validator.

Withdrawals pay at most as many validators as a payload has withdrawals.

Consolidation requests convert at most as many validators as a payload has requests.

The sync committee pays and charges each member at most its seats times the participant reward.

The other credits go to the proposer of the slot.

They are the proposer rewards of attestations and the whistleblower rewards of slashings.

They also include the proposer share of the sync aggregate, which no participant amount counts.

Before Electra, deposits credit at most as many recipients as the block has deposits.

The slashed validators were not slashed before, and pay their initial penalty. -/
private theorem block_balances {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (computed : processBlock config checks engine s block = .ok t) :
    ∃ (paid conv slashed deposited : Finset ValidatorIndex) (sync other slash : ValidatorIndex → ℕ)
      (proposer : ValidatorIndex) (credit share : ℕ),
      Ledger s t paid conv sync other slash ∧
      paid.card ≤ (if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) ∧
      conv.card ≤ (if .pectra ≤ fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat
        else 0) ∧
      (∀ v, v ∉ deposited → other v ≤ if v = proposer then credit + share +
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) ∧
      (∀ v, slash v ≤ if v ∈ slashed then effectiveAt ⟨fork, t⟩ v.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) ∧
      (∀ v ∈ slashed, (∀ validator, s.validators.data[v.toNat]? = some validator →
          validator.slashed = false) ∧
        ∃ later, t.validators.data[v.toNat]? = some later ∧ later.slashed = true) ∧
      (∀ altair : .altair ≤ fork, ∃ reward : Gwei, syncParticipantReward s = .ok reward ∧
        (∀ v, sync v ≤ seatsOf t altair v * reward.toNat) ∧
        share ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))) ∧
      (fork < .altair → sync = 0 ∧ share = 0 ∧ credit = 0) ∧
      (∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count → Reads s base →
        (∀ i, s.validators.data.size ≤ i → base i = 0) →
        credit * proposerDenominator + flagPotential s altair base count ≤
          flagPotential t altair base count) ∧
      (.pectra ≤ fork → deposited = ∅) ∧
      (∀ before : fork < .hegota, (s.eth1DepositIndex before).toNat + deposited.card ≤
        (t.eth1DepositIndex before).toNat ∧ deposited.card ≤ preset.MAX_DEPOSITS.toNat) ∧
      (fork < .altair →
        preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
        0 < credit + share ∨ slashed.Nonempty → proposer = block.proposerIndex) := by
  -- The steps before the operations move no balance except the withdrawals, and keep the reads.
  have before {o : BeaconState preset fork}
      (steps : ∃ paid : Finset ValidatorIndex, Ledger s o paid ∅ 0 0 0 ∧
        paid.card ≤ (if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) ∧
        Steady s o ∧ FlagsGrow s o ∧ BalancesMatch o ∧
        ∀ before : fork < .hegota, o.eth1DepositIndex before = s.eth1DepositIndex before) :
      True := trivial
  clear before
  unfold processBlock at computed
  split at computed
  · rename_i altair
    unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid0, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    have paidSame : paid0 = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid0
    -- The header, the payload, the reveal and the vote.
    obtain ⟨paid, executedLedger, paidCount, executedSteady, executedGrow, executedFrame,
        executedIndex⟩ :
        ∃ paid : Finset ValidatorIndex, Ledger headed executed paid ∅ 0 0 0 ∧
          paid.card ≤ (if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) ∧
          Steady headed executed ∧ FlagsGrow headed executed ∧ Frame headed executed ∧
          ∀ before : fork < .hegota,
            executed.eth1DepositIndex before = headed.eth1DepositIndex before := by
      split at executedOk
      · obtain ⟨paid, ledger, count⟩ := ledger_processBlockExecution early executedOk
        exact ⟨paid, ledger, count, steady_processBlockExecution early executedOk,
          grow_processBlockExecution early executedOk,
          (frame_processBlockExecution executedOk).toFrame,
          index_processBlockExecution early executedOk⟩
      · cases executedOk
        exact ⟨∅, Ledger.refl _, by simp, ⟨StepKeeps.refl _, effectiveKept_refl _⟩,
          FlagsGrow.refl _, Frame.refl _, fun _ => rfl⟩
    obtain ⟨votedLedger, votedSteady, votedGrow, votedFrame, votedIndex⟩ :
        Ledger revealed voted ∅ ∅ 0 0 0 ∧ Steady revealed voted ∧ FlagsGrow revealed voted ∧
          Frame revealed voted ∧
          ∀ before : fork < .hegota,
            voted.eth1DepositIndex before = revealed.eth1DepositIndex before := by
      split at votedOk
      · exact ⟨ledger_processEth1Data votedOk, steady_processEth1Data votedOk,
          grow_processEth1Data votedOk, (frame_processEth1Data votedOk).toFrame,
          fun _ => index_processEth1Data votedOk⟩
      · cases votedOk
        exact ⟨Ledger.refl _, ⟨StepKeeps.refl _, effectiveKept_refl _⟩, FlagsGrow.refl _,
          Frame.refl _, fun _ => rfl⟩
    have toVoted : Ledger s voted paid ∅ 0 0 0 :=
      (ledger_processBlockHeader headedOk).zero_left
        ((executedLedger.zero_right (ledger_processRandao revealedOk)).zero_right votedLedger)
    have steadyVoted : Steady s voted :=
      (steady_processBlockHeader headedOk).trans <| executedSteady.trans <|
        (steady_processRandao revealedOk).trans votedSteady
    have growVoted : FlagsGrow s voted :=
      (grow_processBlockHeader headedOk).trans <| executedGrow.trans <|
        (grow_processRandao revealedOk).trans votedGrow
    have frameVoted : Frame s voted :=
      (frame_processBlockHeader headedOk).toFrame.trans <| executedFrame.trans <|
        (frame_processRandao revealedOk).toFrame.trans votedFrame
    have indexVoted : ∀ before : fork < .hegota,
        voted.eth1DepositIndex before = s.eth1DepositIndex before := fun before => by
      rw [votedIndex before, index_processRandao revealedOk before, executedIndex before,
        index_processBlockHeader headedOk before]
    -- The operations and the sync aggregate.
    obtain ⟨proposer, credit, slashed, deposited, conv, other, slash, ops, convCount⟩ :=
      credited_processOperations early (frameVoted.balancesMatch matched) operatedOk
    obtain ⟨proposer', reward, share, sync, rewardOk, read', shareBound, seats, syncLedger⟩ :=
      ledger_processSyncAggregate synced
    have syncKept := kept_processSyncAggregate synced
    have syncGrow := grow_processSyncAggregate synced
    have total : getTotalActiveBalance operated = getTotalActiveBalance s :=
      (steadyVoted.trans ops.kept.steady).total
    -- One proposer earns all the other credits.
    have same : 0 < credit ∨ slashed.Nonempty → 0 < share → proposer' = proposer := by
      intro first second
      have := read' second
      rw [ops.kept.proposer, ops.read first] at this
      exact (Except.ok.inj this).symm
    have effectiveSame : ∀ x ∈ slashed,
        effectiveAt ⟨fork, t⟩ x.toNat = effectiveAt ⟨fork, operated⟩ x.toNat := by
      intro x member
      obtain ⟨later, found, _⟩ := (ops.newly x member).2
      exact effectiveAt_of_kept syncKept found
    refine ⟨paid ∪ ∅ ∪ ∅, ∅ ∪ conv ∪ ∅, slashed, deposited, 0 + 0 + sync,
      0 + other + fun v => if v = proposer' then share else 0, 0 + slash + 0,
      if 0 < share then proposer' else proposer, credit, share,
      (toVoted.trans ops.ledger).trans syncLedger, by simpa using paidCount,
      by simpa [altair] using convCount, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v absent
      have first := ops.credited v absent
      have sumSame : ∑ x ∈ slashed, effectiveAt ⟨fork, operated⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
          ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
        Finset.sum_congr rfl fun x member => by rw [effectiveSame x member]
      rw [sumSame] at first
      simp only [Pi.add_apply, zero_add]
      by_cases positive : 0 < share
      · simp only [positive, ↓reduceIte]
        by_cases earlier : 0 < credit ∨ slashed.Nonempty
        · rw [same earlier positive] at *
          split at first <;> split <;> omega
        · simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at earlier
          simp only [earlier.1, earlier.2, Finset.sum_empty, add_zero] at first ⊢
          split at first <;> split <;> omega
      · have zero : share = 0 := by omega
        simp only [zero, ite_self, add_zero]
        split at first <;> split <;> omega
    · intro v
      have := ops.penalized v
      simp only [Pi.add_apply, Pi.zero_apply, zero_add, add_zero]
      split at this
      · rename_i member; rw [ite_eq_left member, effectiveSame v member]; exact this
      · rw [ite_eq_right (by assumption)]; exact this
    · intro v member
      obtain ⟨unslashed, later, found, marked⟩ := ops.newly v member
      refine ⟨fun validator found' => ?_, ?_⟩
      · have inside := (Array.getElem?_eq_some_iff.mp found').1
        have middle : v.toNat < voted.validators.data.size :=
          Nat.lt_of_lt_of_le inside frameVoted.registryGrows
        have clear := unslashed _ (Array.getElem?_eq_getElem middle)
        cases flag : validator.slashed
        · rfl
        · have := frameVoted.slashed v.toNat validator _ found' (Array.getElem?_eq_getElem middle)
            flag
          rw [clear] at this
          cases this
      · have inside : v.toNat < t.validators.data.size :=
          Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 syncKept.frame.registryGrows
        exact ⟨_, Array.getElem?_eq_getElem inside,
          syncKept.frame.slashed v.toNat later _ found (Array.getElem?_eq_getElem inside) marked⟩
    · intro altair'
      refine ⟨reward, ?_, fun v => by simpa using seats v, shareBound⟩
      rw [← syncParticipantReward_congr total]
      exact rewardOk
    · intro earlier
      exact absurd altair (Nat.not_le_of_lt earlier)
    · intro altair' base count big reads support
      have votedReads : Reads voted base := steadyVoted.reads reads
      have first := flagPotential_mono growVoted altair' base count
      have second := ops.potential altair' base count big votedReads fun i outside =>
        support i (Nat.le_trans frameVoted.registryGrows outside)
      have third := flagPotential_mono syncGrow altair' base count
      omega
    · exact ops.electra
    · intro before
      have := ops.deposits before
      rw [indexVoted before] at this
      rw [index_processSyncAggregate synced before]
      refine ⟨this, ?_⟩
      have bound := index_processOperations early before operatedOk
      rw [indexVoted before] at bound
      omega
    · intro earlier
      exact absurd altair (Nat.not_le_of_lt earlier)
  · rename_i altair
    have notAltair : fork < .altair := Nat.lt_of_not_le altair
    simp only [bind_ok_iff] at computed
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := computed
    have toVoted : Ledger s voted ∅ ∅ 0 0 0 :=
      (ledger_processBlockHeader headedOk).zero_left
        ((ledger_processRandao revealedOk).zero_right (ledger_processEth1Data votedOk))
    have frameVoted : Frame s voted :=
      (frame_processBlockHeader headedOk).toFrame.trans <|
        (frame_processRandao revealedOk).toFrame.trans (frame_processEth1Data votedOk).toFrame
    have indexVoted : ∀ before : fork < .hegota,
        voted.eth1DepositIndex before = s.eth1DepositIndex before := fun before => by
      rw [index_processEth1Data votedOk, index_processRandao revealedOk before,
        index_processBlockHeader headedOk before]
    obtain ⟨proposer, credit, slashed, deposited, conv, other, slash, ops, convCount⟩ :=
      credited_processOperations early (frameVoted.balancesMatch matched) operatedOk
    have zero := ops.phase0 notAltair
    refine ⟨∅, conv, slashed, deposited, 0, other, slash, proposer, credit, 0,
      toVoted.zero_left ops.ledger, by simp, convCount, ?_, ops.penalized, ?_, ?_, ?_, ?_,
      ops.electra, ?_, ?_⟩
    · intro v absent
      simpa using ops.credited v absent
    · intro v member
      obtain ⟨unslashed, later⟩ := ops.newly v member
      refine ⟨fun validator found' => ?_, later⟩
      have inside := (Array.getElem?_eq_some_iff.mp found').1
      have middle : v.toNat < voted.validators.data.size :=
        Nat.lt_of_lt_of_le inside frameVoted.registryGrows
      have clear := unslashed _ (Array.getElem?_eq_getElem middle)
      cases flag : validator.slashed
      · rfl
      · have := frameVoted.slashed v.toNat validator _ found' (Array.getElem?_eq_getElem middle)
          flag
        rw [clear] at this
        cases this
    · intro altair'
      exact absurd altair' altair
    · intro _
      exact ⟨rfl, rfl, zero⟩
    · intro altair'
      exact absurd altair' altair
    · intro before
      have := ops.deposits before
      rw [indexVoted before] at this
      refine ⟨this, ?_⟩
      have bound := index_processOperations early before operatedOk
      rw [indexVoted before] at bound
      omega
    · intro _ apart positive
      have read := ops.read (by simpa using positive)
      rw [proposer_of_prefix notAltair apart headedOk revealedOk votedOk] at read
      exact (Except.ok.inj read).symm


end Block

/-! ### The blocks of one epoch -/

section Epoch

variable {fork : Fork}

/-- The induction of `Run.induction_of_same_epoch`, which also counts the blocks so far. -/
private theorem Run.induction_counted {x : ForkedBeaconState preset}
    (motive : (z : ForkedBeaconState preset) → Run config checks x z → Prop)
    (start : motive x .nil)
    (blockStep : ∀ {f : Fork} {s t : BeaconState preset f} (engine : ExecutionEngine preset f)
      (signed : SignedBeaconBlock preset f) (due : upgradeDue config ⟨f, s⟩ = false)
      (ok : applySignedBlock config checks engine s signed true = .ok t)
      (pre : Run config checks x ⟨f, s⟩), f < .glamsterdam → motive ⟨f, s⟩ pre →
        motive ⟨f, t⟩ (pre.snoc (.block engine signed due ok)))
    (slotStep : ∀ {middle last : ForkedBeaconState preset} {cached : BeaconState preset middle.fork}
      {next : Slot} (pre : Run config checks x middle)
      (ok : advanceSlotAcross config checks middle = .ok last),
      last = ⟨middle.fork, { cached with slot := next }⟩ →
      processSlot middle.state = .ok cached →
      getCurrentEpoch ({ cached with slot := next } : BeaconState preset middle.fork) =
        getCurrentEpoch middle.state → motive middle pre →
      motive last (pre.snoc (.slot ok)))
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    motive y tail := by
  induction tail with
  | nil => exact start
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have midEpoch : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      UInt64.le_antisymm (same ▸ step.chainStep.currentEpoch_le)
        (currentEpoch_le_of_chainSteps pre.chainSteps)
    have prior := ih middleEarly midEpoch
    cases step with
    | block engine signed due ok => exact blockStep engine signed due ok pre early prior
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have epoch : getCurrentEpoch next = getCurrentEpoch middle.state := by
        have slot : last.state.slot = next.slot := processUpgrades_induction
          (property := fun t => t.state.slot = next.slot)
          (fun prior ok => (upgradeFrame_upgradeNext ok).slot.trans prior) rfl upgraded
        have eq : getCurrentEpoch last.state = getCurrentEpoch next := by
          simp only [getCurrentEpoch, slot]
        exact eq.symm.trans (same.trans midEpoch.symm)
      obtain ⟨slot, cached, epoched, sum, cachedOk, epochOk, rfl⟩ := advanceSlot_ok advanced
      have notFirst : slot % preset.SLOTS_PER_EPOCH ≠ 0 := by
        intro firstSlot
        have rem : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
          simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat firstSlot
        have eq := congrArg UInt64.toNat epoch
        simp only [getCurrentEpoch_toNat] at eq
        have divide := Nat.mod_add_div slot.toNat preset.SLOTS_PER_EPOCH.toNat
        have before := Nat.mod_add_div middle.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
        rw [eq] at divide
        omega
      rw [processUpgrades_of_not_due (upgradeDue_of_not_first notFirst)] at upgraded
      have lastEq := (Except.ok.inj upgraded).symm
      simp only [epochIfLast, ite_eq_right notFirst, pure, Except.pure, Except.ok.injEq] at epochOk
      subst epoched
      exact slotStep pre ok lastEq cachedOk epoch prior

/-- A later state of the same epoch.

Its registry grows and keeps activity and effective balances. -/
private structure Within (a s : BeaconState preset fork) : Prop where
  size : a.validators.data.size ≤ s.validators.data.size
  epoch : getCurrentEpoch s = getCurrentEpoch a
  active : ActiveKept (activityFixedEpoch a) a s
  effective : EffectiveKept a s

/-- Every state is within its own epoch. -/
private theorem Within.refl (a : BeaconState preset fork) : Within a a :=
  ⟨Nat.le_refl _, rfl, ActiveKept.refl _ _, effectiveKept_refl _⟩

/-- A steady step stays within the epoch. -/
private theorem Within.steady {a s t : BeaconState preset fork} (w : Within a s)
    (kept : Steady s t) : Within a t where
  size := Nat.le_trans w.size kept.keeps.1
  epoch := kept.epoch.trans w.epoch
  active := by
    have fixed : activityFixedEpoch s = activityFixedEpoch a := by
      simp only [activityFixedEpoch, w.epoch]
    have step := kept.keeps.2.2
    rw [fixed] at step
    exact w.active.trans step
  effective := effectiveKept_trans w.effective kept.effective w.size

/-- The effective balances below the registry size of the start, read as options. -/
private theorem Within.effective_map {a s : BeaconState preset fork} (w : Within a s) (j : ℕ)
    (inside : j < a.validators.data.size) :
    (a.validators.data[j]?).map (·.effectiveBalance) =
      (s.validators.data[j]?).map (·.effectiveBalance) := by
  have same := w.effective j inside
  have later : j < s.validators.data.size := Nat.lt_of_lt_of_le inside w.size
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem later,
    Option.map_some, Option.getD_some] at same ⊢
  exact congrArg some (UInt64.toNat_inj.mp same.symm)

/-- A state within the epoch has the total active balance of the start. -/
private theorem Within.total {a s : BeaconState preset fork} (w : Within a s) :
    getTotalActiveBalance s = getTotalActiveBalance a :=
  ExitChurn.totalActiveBalance_eq w.epoch
    (fun epoch le => w.active epoch (UInt64.le_trans le
      (getCurrentEpoch_le_activityFixedEpoch a))) w.size
    fun i v found => by
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have same := w.effective_map i inside
      rw [found] at same
      cases later : s.validators.data[i]? with
      | none => simp [later] at same
      | some u =>
        simp only [later, Option.map_some, Option.some.injEq] at same
        exact ⟨u, rfl, same.symm⟩

/-- A state within the epoch has the recent validators of the start. -/
private theorem Within.recent {a s : BeaconState preset fork} (w : Within a s) (i : ℕ) :
    (isActiveAt s (getPreviousEpoch s) i = true ∨ isActiveAt s (getCurrentEpoch s) i = true) ↔
      (isActiveAt a (getPreviousEpoch a) i = true ∨ isActiveAt a (getCurrentEpoch a) i = true) := by
  have previous : getPreviousEpoch s = getPreviousEpoch a := by
    unfold getPreviousEpoch; rw [w.epoch]
  have fixed := getCurrentEpoch_le_activityFixedEpoch a
  have previousLe : getPreviousEpoch a ≤ activityFixedEpoch a :=
    UInt64.le_trans (getPreviousEpoch_le a) fixed
  rw [previous, w.epoch, w.active _ previousLe, w.active _ fixed]

/-- A recent validator is in the registry. -/
private theorem inside_of_recent {a : BeaconState preset fork} {i : ℕ}
    (recent : isActiveAt a (getPreviousEpoch a) i = true ∨
      isActiveAt a (getCurrentEpoch a) i = true) : i < a.validators.data.size := by
  rcases recent with active | active <;>
  · unfold isActiveAt at active
    cases found : a.validators.data[i]? with
    | none => simp [found] at active
    | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

/-- The base rewards read at the start are read at every state within the epoch. -/
private theorem Within.reads {a s : BeaconState preset fork} (w : Within a s) {base : ℕ → ℕ}
    (reads : Reads a base) : Reads s base := by
  intro index total reward recent totalOk rewardOk
  rw [w.recent] at recent
  have inside := inside_of_recent recent
  rw [w.total] at totalOk
  rw [getBaseReward_congr (w.effective_map _ inside).symm] at rewardOk
  exact reads index total reward recent totalOk rewardOk

/-- The base rewards read at a state within the epoch are read at the start. -/
private theorem Within.reads_back {a s : BeaconState preset fork} (w : Within a s)
    {base : ℕ → ℕ} (reads : Reads s base) : Reads a base := by
  intro index total reward recent totalOk rewardOk
  have inside := inside_of_recent recent
  refine reads index total reward ((w.recent _).mpr recent) (by rw [w.total]; exact totalOk) ?_
  rw [getBaseReward_congr (w.effective_map _ inside).symm]
  exact rewardOk

/-- Whether the validator at an index is slashed, and false outside the registry. -/
private def slashedAt (s : BeaconState preset fork) (v : ValidatorIndex) : Bool :=
  ((s.validators.data[v.toNat]?).map (·.slashed)).getD false

/-- The initial slashing penalty of a slashed validator, read at its effective balance. -/
private def slashBackAt (s : BeaconState preset fork) (v : ValidatorIndex) : ℕ :=
  if slashedAt s v then effectiveAt ⟨fork, s⟩ v.toNat /
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0

/-- The sync amount of a validator for one block, its seats times a participant reward. -/
private def syncAt (s : BeaconState preset fork) (reward : ℕ) (v : ValidatorIndex) : ℕ :=
  if altair : .altair ≤ fork then seatsOf s altair v * reward else 0

/-- The participant reward of the sync committee read at a state, and zero when the read fails. -/
private def rewardRead (a : BeaconState preset fork) : ℕ :=
  match syncParticipantReward a with
  | .ok reward => reward.toNat
  | .error _ => 0

/-- A slashed validator stays slashed along a frame. -/
private theorem slashedAt_of_frame {s t : BeaconState preset fork} (frame : Frame s t)
    {v : ValidatorIndex} (marked : slashedAt s v = true) : slashedAt t v = true := by
  unfold slashedAt at marked ⊢
  cases found : s.validators.data[v.toNat]? with
  | none => simp [found] at marked
  | some old =>
    simp only [found, Option.map_some, Option.getD_some] at marked
    have later : v.toNat < t.validators.data.size :=
      Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 frame.registryGrows
    rw [Array.getElem?_eq_getElem later]
    simpa using frame.slashed v.toNat old _ found (Array.getElem?_eq_getElem later) marked

/-- A slashed validator is in the registry. -/
private theorem inside_of_slashedAt {s : BeaconState preset fork} {v : ValidatorIndex}
    (marked : slashedAt s v = true) : v.toNat < s.validators.data.size := by
  unfold slashedAt at marked
  cases found : s.validators.data[v.toNat]? with
  | none => simp [found] at marked
  | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

/-- The slashing penalty read at a state only grows along a frame that keeps effective balances. -/
private theorem slashBackAt_le {s t : BeaconState preset fork} (frame : Frame s t)
    (kept : EffectiveKept s t) (v : ValidatorIndex) : slashBackAt s v ≤ slashBackAt t v := by
  unfold slashBackAt
  by_cases marked : slashedAt s v = true
  · rw [ite_eq_left marked, ite_eq_left (slashedAt_of_frame frame marked),
      kept v.toNat (inside_of_slashedAt marked)]
  · rw [ite_eq_right marked]
    exact Nat.zero_le _

/-- A block before Gloas keeps the current sync committee. -/
private theorem committee_processBlock {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .glamsterdam) (altair : .altair ≤ fork)
    (computed : processBlock config checks engine s block = .ok t) :
    t.currentSyncCommittee altair = s.currentSyncCommittee altair := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid0, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    have paidSame : paid0 = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid0
    have header : headed.currentSyncCommittee altair = s.currentSyncCommittee altair := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      rfl
    have execution : executed.currentSyncCommittee altair =
        headed.currentSyncCommittee altair := by
      split at executedOk
      · exact processBlockExecution_currentSyncCommittee altair executedOk
      · cases executedOk; rfl
    have randao : revealed.currentSyncCommittee altair = executed.currentSyncCommittee altair := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      rfl
    have vote : voted.currentSyncCommittee altair = revealed.currentSyncCommittee altair := by
      split at votedOk
      · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
        rw [← rest]
      · cases votedOk; rfl
    rw [congrFun (processSyncAggregate_kept synced).2 altair,
      processOperations_currentSyncCommittee altair operatedOk, vote, randao, execution, header]
  · exact absurd altair (by assumption)

/-- A frame that keeps the committee keeps the seats of every old validator. -/
private theorem seatsOf_le {s t : BeaconState preset fork} (frame : Frame s t)
    (altair : .altair ≤ fork)
    (committee : t.currentSyncCommittee altair = s.currentSyncCommittee altair)
    (v : ValidatorIndex) : seatsOf s altair v ≤ seatsOf t altair v := by
  unfold seatsOf
  rw [committee]
  cases found : s.validators.data[v.toNat]? with
  | none => simp
  | some w =>
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have keyS : (validatorKeys s)[v.toNat]? = some w.pubkey := by
      simp [validatorKeys, found]
    have keyT : (validatorKeys t)[v.toNat]? = some w.pubkey := by
      obtain ⟨rest, joined⟩ := frame.pubkeysPrefix
      rw [← joined, List.getElem?_append_left (by simpa [validatorKeys] using inside)]
      exact keyS
    cases later : t.validators.data[v.toNat]? with
    | none => simp [validatorKeys, later] at keyT
    | some w' =>
      simp only [validatorKeys, List.getElem?_map, Array.getElem?_toList, later, Option.map_some,
        Option.some.injEq] at keyT
      simp [keyT]

/-- A frame that keeps the committee keeps the sync amount of every old validator. -/
private theorem syncAt_le {s t : BeaconState preset fork} (frame : Frame s t)
    (committee : ∀ altair : .altair ≤ fork,
      t.currentSyncCommittee altair = s.currentSyncCommittee altair)
    (reward : ℕ) (v : ValidatorIndex) : syncAt s reward v ≤ syncAt t reward v := by
  unfold syncAt
  by_cases altair : .altair ≤ fork
  · rw [dite_eq_left altair, dite_eq_left altair]
    exact Nat.mul_le_mul_right _ (seatsOf_le frame altair (committee altair) v)
  · rw [dite_eq_right altair, dite_eq_right altair]

/-- What the blocks of one epoch so far did to the balances.

It is read from the start `a` of the epoch at a later state `s` after `n` blocks. -/
private structure Tally (a s : BeaconState preset fork) (n : ℕ)
    (deb conv props dep sl : Finset ValidatorIndex) (pc deposit : ValidatorIndex → ℕ)
    (credits shares : ℕ) : Prop where
  within : Within a s
  matched : BalancesMatch s
  persist : ∀ (v : ValidatorIndex) validator, a.validators.data[v.toNat]? = some validator →
    validator.slashed = true → slashedAt s v = true
  debCard : deb.card ≤
    ((if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
      (if .pectra ≤ fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) * n
  convSub : conv ⊆ deb
  down : ∀ v, v ∉ deb → actualBalanceAt ⟨fork, a⟩ v.toNat ≤
    actualBalanceAt ⟨fork, s⟩ v.toNat + slashBackAt s v + n * syncAt s (rewardRead a) v
  up : ∀ v, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
    actualBalanceAt ⟨fork, a⟩ v.toNat + n * syncAt s (rewardRead a) v + pc v + deposit v
  converted : ∀ v ∈ conv, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
    preset.MIN_ACTIVATION_BALANCE.toNat + n * syncAt s (rewardRead a) v + pc v + deposit v
  kept : ∀ (v : ValidatorIndex) validator, v ∉ conv →
    a.validators.data[v.toNat]? = some validator →
    ∃ later, s.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator
  pcZero : ∀ v, v ∉ props → pc v = 0
  depositZero : ∀ v, v ∉ dep → deposit v = 0
  budget : ∑ v ∈ props, pc v ≤ credits + shares + ∑ v ∈ sl, effectiveAt ⟨fork, s⟩ v.toNat /
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  potential : ∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count →
    Reads a base → (∀ i, a.validators.data.size ≤ i → base i = 0) →
    credits * proposerDenominator + flagPotential a altair base count ≤
      flagPotential s altair base count
  phase0 : fork < .altair → credits = 0 ∧ shares = 0
  share : .altair ≤ fork → shares ≤ n * (preset.SYNC_COMMITTEE_SIZE.toNat *
    (rewardRead a * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)))
  newly : ∀ v ∈ sl, (∀ validator, a.validators.data[v.toNat]? = some validator →
    validator.slashed = false) ∧ slashedAt s v = true
  propsCard : props.card ≤ n
  propsPos : props.Nonempty → 0 < credits ∨ 0 < shares ∨ sl.Nonempty
  depCard : dep.card ≤ preset.MAX_DEPOSITS.toNat * n
  depIndex : ∀ before : fork < .hegota,
    (a.eth1DepositIndex before).toNat + dep.card ≤ (s.eth1DepositIndex before).toNat
  electra : .pectra ≤ fork → dep = ∅
  reward : 0 < n → .altair ≤ fork → ∃ r, syncParticipantReward a = .ok r

/-- Before any block, the tally is empty. -/
private theorem Tally.start (a : BeaconState preset fork) (matched : BalancesMatch a) :
    Tally a a 0 ∅ ∅ ∅ ∅ ∅ 0 0 0 0 where
  within := Within.refl a
  matched := matched
  persist v validator found flag := by simp [slashedAt, found, flag]
  debCard := by simp
  convSub := Finset.empty_subset _
  down v _ := by simp
  up v := by simp
  converted v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := ⟨validator, found, rfl⟩
  pcZero _ _ := rfl
  depositZero _ _ := rfl
  budget := by simp
  potential _ _ _ _ _ _ := by simp
  phase0 _ := ⟨rfl, rfl⟩
  share _ := by simp
  newly v member := absurd member (Finset.notMem_empty v)
  propsCard := by simp
  propsPos h := absurd h (by simp)
  depCard := by simp
  depIndex _ := by simp
  electra _ := rfl
  reward h := absurd h (Nat.lt_irrefl 0)

/-- A slot step inside the epoch keeps the tally. -/
private theorem Tally.slot {a s cached : BeaconState preset fork} {next : Slot} {n : ℕ}
    {deb conv props dep sl : Finset ValidatorIndex} {pc deposit : ValidatorIndex → ℕ}
    {credits shares : ℕ} (tally : Tally a s n deb conv props dep sl pc deposit credits shares)
    (computed : processSlot s = .ok cached)
    (epoch : getCurrentEpoch ({ cached with slot := next } : BeaconState preset fork) =
      getCurrentEpoch s) :
    Tally a { cached with slot := next } n deb conv props dep sl pc deposit credits shares := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact { tally with
    within := { tally.within with epoch := epoch.trans tally.within.epoch
                                  active := tally.within.active } }

/-- A block before Gloas extends the tally by one block. -/
private theorem Tally.block {a s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {n : ℕ} {deb conv props dep sl : Finset ValidatorIndex}
    {pc deposit : ValidatorIndex → ℕ} {credits shares : ℕ}
    (tally : Tally a s n deb conv props dep sl pc deposit credits shares)
    (early : fork < .glamsterdam) (computed : processBlock config checks engine s block = .ok t) :
    ∃ (deb' conv' props' dep' sl' : Finset ValidatorIndex) (pc' deposit' : ValidatorIndex → ℕ)
      (credits' shares' : ℕ),
      Tally a t (n + 1) deb' conv' props' dep' sl' pc' deposit' credits' shares' ∧
      (fork < .altair →
        preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
        ∀ v ∈ props', v ∉ props → v = block.proposerIndex) := by
  obtain ⟨paid, cv, slashed, deposited, sync, other, slash, proposer, credit, share, ledger,
    paidCard, convCard, credited, penalized, newly, rewards, phase0, potential, electra,
    deposits, header⟩ := block_balances early tally.matched computed
  have frame := frame_processBlock computed
  have steady : Steady s t := ⟨stepKeeps_processBlock computed, effectiveKept_block early computed⟩
  have within := tally.within.steady steady
  have committee : ∀ altair : .altair ≤ fork,
      t.currentSyncCommittee altair = s.currentSyncCommittee altair :=
    fun altair => committee_processBlock early altair computed
  have syncMono : ∀ v, syncAt s (rewardRead a) v ≤ syncAt t (rewardRead a) v :=
    syncAt_le frame committee _
  have backMono : ∀ v, slashBackAt s v ≤ slashBackAt t v := slashBackAt_le frame steady.effective
  have hegota : fork < .hegota := Nat.lt_trans early (by decide)
  -- The participant reward of the block is the one read at the start.
  have rewardSame : ∀ altair : .altair ≤ fork, ∃ reward : Gwei,
      syncParticipantReward a = .ok reward ∧ reward.toNat = rewardRead a ∧
      (∀ v, sync v ≤ seatsOf t altair v * reward.toNat) ∧
      share ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat * PROPOSER_WEIGHT.toNat /
        (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := by
    intro altair
    obtain ⟨reward, ok, seats, bound⟩ := rewards altair
    rw [syncParticipantReward_congr tally.within.total] at ok
    refine ⟨reward, ok, ?_, seats, bound⟩
    unfold rewardRead
    rw [ok]
  have syncLe : ∀ v, sync v ≤ syncAt t (rewardRead a) v := by
    intro v
    by_cases altair : .altair ≤ fork
    · obtain ⟨reward, _, same, seats, _⟩ := rewardSame altair
      unfold syncAt
      rw [dite_eq_left altair, ← same]
      exact seats v
    · rw [(phase0 (Nat.lt_of_not_le altair)).1]
      exact Nat.zero_le _
  -- The unslashed validators that the block slashes.
  have unslashedS : ∀ v ∈ slashed, slashedAt s v = false := by
    intro v member
    unfold slashedAt
    cases found : s.validators.data[v.toNat]? with
    | none => rfl
    | some w => simp [(newly v member).1 w found]
  have slashedT : ∀ v ∈ slashed, slashedAt t v = true := by
    intro v member
    obtain ⟨later, found, marked⟩ := (newly v member).2
    simp [slashedAt, found, marked]
  have slashLe : ∀ v, slash v + slashBackAt s v ≤ slashBackAt t v := by
    intro v
    have pen := penalized v
    by_cases member : v ∈ slashed
    · rw [ite_eq_left member] at pen
      simp only [slashBackAt, unslashedS v member, slashedT v member, Bool.false_eq_true,
        ↓reduceIte]
      omega
    · rw [ite_eq_right member] at pen
      have := backMono v
      omega
  have parts : ∀ v, (if v ∈ deposited then 0 else other v) +
      (if v ∈ deposited then other v else 0) = other v := by
    intro v; split <;> simp
  set whistle := ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with whistleEq
  refine ⟨deb ∪ (paid ∪ cv), conv ∪ cv,
    if 0 < credit + share + whistle then insert proposer props else props,
    dep ∪ deposited, sl ∪ slashed, fun v => pc v + if v ∈ deposited then 0 else other v,
    fun v => deposit v + if v ∈ deposited then other v else 0, credits + credit, shares + share,
    { within := within
      matched := frame.balancesMatch tally.matched
      persist := fun v validator found flag =>
        slashedAt_of_frame frame (tally.persist v validator found flag)
      debCard := ?_
      convSub := Finset.union_subset_union tally.convSub Finset.subset_union_right
      down := ?_
      up := ?_
      converted := ?_
      kept := ?_
      pcZero := ?_
      depositZero := ?_
      budget := ?_
      potential := ?_
      phase0 := ?_
      share := ?_
      newly := ?_
      propsCard := ?_
      propsPos := ?_
      depCard := ?_
      depIndex := ?_
      electra := ?_
      reward := ?_ }, ?_⟩
  · have one := Finset.card_union_le deb (paid ∪ cv)
    have two := Finset.card_union_le paid cv
    have three := tally.debCard
    rw [Nat.mul_succ]
    omega
  · intro v notIn
    simp only [Finset.mem_union, not_or] at notIn
    have h1 := tally.down v notIn.1
    have h2 := ledger.down v notIn.2.1 notIn.2.2
    have h3 := slashLe v
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    omega
  · intro v
    have h1 := tally.up v
    have h2 := ledger.up v
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    have h6 := parts v
    rw [Nat.succ_mul]
    omega
  · intro v member
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    have h6 := parts v
    rw [Nat.succ_mul]
    by_cases fresh : v ∈ cv
    · have := ledger.converted v fresh
      omega
    · have old : v ∈ conv := by
        rcases Finset.mem_union.mp member with h | h
        · exact h
        · exact absurd h fresh
      have h1 := tally.converted v old
      have h2 := ledger.up v
      omega
  · intro v validator notIn found
    simp only [Finset.mem_union, not_or] at notIn
    obtain ⟨middle, middleFound, same⟩ := tally.kept v validator notIn.1 found
    obtain ⟨later, laterFound, same'⟩ := ledger.kept v middle notIn.2 middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  · intro v notIn
    have notProps : v ∉ props := fun h => notIn (by split <;> simp [h])
    rw [tally.pcZero v notProps, Nat.zero_add]
    split
    · rfl
    · rename_i notDep
      have bound := credited v notDep
      split at bound
      · rename_i eq
        subst eq
        have zero : ¬ 0 < credit + share + whistle := fun pos => notIn (by simp [pos])
        omega
      · omega
  · intro v notIn
    simp only [Finset.mem_union, not_or] at notIn
    rw [tally.depositZero v notIn.1, ite_eq_right notIn.2]
  · -- The budget: the old credits, and the amount of this block, which goes to its proposer.
    rw [Finset.sum_add_distrib]
    have sub : props ⊆ if 0 < credit + share + whistle then insert proposer props else props := by
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
    rw [← Finset.sum_subset sub fun v _ notIn => tally.pcZero v notIn]
    have blockPart : ∑ v ∈ (if 0 < credit + share + whistle then insert proposer props else props),
        (if v ∈ deposited then 0 else other v) ≤ credit + share + whistle := by
      calc _ ≤ ∑ v ∈ (if 0 < credit + share + whistle then insert proposer props else props),
            (if v = proposer then credit + share + whistle else 0) := by
            apply Finset.sum_le_sum
            intro v _
            split
            · exact Nat.zero_le _
            · rename_i notDep
              exact credited v notDep
        _ ≤ credit + share + whistle := by
            rw [Finset.sum_ite_eq']
            split_ifs <;> omega
    have disjoint : Disjoint sl slashed := by
      rw [Finset.disjoint_left]
      intro v inOld inNew
      have := (tally.newly v inOld).2
      rw [unslashedS v inNew] at this
      cases this
    rw [Finset.sum_union disjoint]
    have oldSame : ∑ v ∈ sl, effectiveAt ⟨fork, t⟩ v.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ v ∈ sl, effectiveAt ⟨fork, s⟩ v.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun v member => by
        rw [steady.effective v.toNat (inside_of_slashedAt (tally.newly v member).2)]
    rw [oldSame, ← whistleEq]
    have := tally.budget
    omega
  · intro altair base count big reads support
    have readsS : Reads s base := tally.within.reads reads
    have first := tally.potential altair base count big reads support
    have second := potential altair base count big readsS fun i outside =>
      support i (Nat.le_trans tally.within.size outside)
    rw [Nat.add_mul]
    omega
  · intro before
    have := tally.phase0 before
    have := phase0 before
    omega
  · intro altair
    obtain ⟨reward, _, same, _, bound⟩ := rewardSame altair
    rw [same] at bound
    have := tally.share altair
    rw [Nat.succ_mul]
    omega
  · intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact ⟨(tally.newly v old).1, slashedAt_of_frame frame (tally.newly v old).2⟩
    · refine ⟨fun validator found => ?_, slashedT v fresh⟩
      cases flag : validator.slashed
      · rfl
      · have := tally.persist v validator found flag
        rw [unslashedS v fresh] at this
        cases this
  · split
    · have := Finset.card_insert_le proposer props
      have := tally.propsCard
      omega
    · have := tally.propsCard
      omega
  · intro nonempty
    split at nonempty
    · rename_i positive
      by_cases c : 0 < credit
      · left; omega
      by_cases d : 0 < share
      · right; left; omega
      right; right
      have : 0 < whistle := by omega
      obtain ⟨v, member⟩ : slashed.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro empty
        rw [whistleEq, empty, Finset.sum_empty] at this
        exact Nat.lt_irrefl 0 this
      exact ⟨v, Finset.mem_union_right _ member⟩
    · rcases tally.propsPos nonempty with h | h | ⟨v, member⟩
      · left; omega
      · right; left; omega
      · right; right; exact ⟨v, Finset.mem_union_left _ member⟩
  · have := Finset.card_union_le dep deposited
    have := tally.depCard
    have := (deposits hegota).2
    rw [Nat.mul_succ]
    omega
  · intro before
    have := Finset.card_union_le dep deposited
    have := tally.depIndex before
    have := (deposits before).1
    omega
  · intro pectra
    rw [tally.electra pectra, electra pectra, Finset.union_empty]
  · intro _ altair
    obtain ⟨reward, ok, _⟩ := rewardSame altair
    exact ⟨reward, ok⟩
  · intro pre apart v member notOld
    split at member
    · rename_i positive
      rcases Finset.mem_insert.mp member with h | h
      · rw [h]
        refine header pre apart ?_
        by_cases c : 0 < credit + share
        · exact Or.inl c
        · right
          rw [Finset.nonempty_iff_ne_empty]
          intro empty
          have : whistle = 0 := by rw [whistleEq, empty, Finset.sum_empty]
          omega
      · exact absurd h notOld
    · exact absurd member notOld

/-- The flags of one byte weigh at most the sum of all flag weights, `54`. -/
private theorem flagWeight_le (flags : ParticipationFlags) : flagWeight flags ≤ 54 := by
  unfold flagWeight
  calc _ ≤ ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat).sum := by
        apply List.sum_le_sum
        intro flag _
        split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
    _ = 54 := by decide

/-- The flag potential is at most `108` times the sum of the weights it reads. -/
private theorem flagPotential_le (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (base : ℕ → ℕ) (count : ℕ) :
    flagPotential s altair base count ≤ 108 * ∑ i ∈ Finset.range count, base i := by
  unfold flagPotential
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have one := flagWeight_le (((s.previousEpochParticipation altair).data[i]?).getD 0)
  have two := flagWeight_le (((s.currentEpochParticipation altair).data[i]?).getD 0)
  rw [Nat.mul_comm 108]
  exact Nat.mul_le_mul_left _ (by omega)

/-- A sum of quotients is at most the quotient of the sum. -/
private theorem sum_div_le_div_sum {α : Type} (S : Finset α) (f : α → ℕ) (q : ℕ) :
    ∑ v ∈ S, f v / q ≤ (∑ v ∈ S, f v) / q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S notIn ih =>
    rw [Finset.sum_insert notIn, Finset.sum_insert notIn]
    refine Nat.le_trans (Nat.add_le_add_left ih _) ?_
    rcases Nat.eq_zero_or_pos q with zero | positive
    · simp [zero]
    · rw [Nat.le_div_iff_mul_le positive, Nat.add_mul]
      exact Nat.add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)

end Epoch

/-! ## Piece 12: the branch corrections -/

/-- The balances along a branch inside one epoch, before Gloas, read from its last state.

This is the branch correction of the fast confirmation rule.

It is read by `quorumDrift_le_quorumReserve`.

The run moves through the blocks of one epoch.

Read at its last state:

- (BC-g) Off a set of debited validators, a balance falls by at most the sum of its penalties.
  These are the initial slashing penalty and the sync penalties of the blocks.
  The debited validators are those that a withdrawal pays or a consolidation request converts.
  Their number is at most the payload limits per block.
  Off them the largest effective balance stays.
- (BC-l) A balance rises by at most the sync rewards of the blocks and its other credits.
  The other credits are zero off a set of credited validators.
  That set holds the proposers of the blocks that can credit anything.
  Before Electra, it also holds the recipients of deposits, at most the deposits read.
- Apart from deposits, the other credits come from three sources.
  The first is the proposer rewards of attestations.
  The second is the proposer share of the sync aggregates.
  The third is the whistleblower rewards.
  Together they are at most the sum of the proposer credit and some whistleblower rewards.
  These are the whistleblower rewards of the validators slashed at the last state.
  The proposer credit counts the proposer share apart from the participant sync rewards.
  The bound also holds with only the validators slashed along the run.
  Before Altair, blocks pay no proposer rewards, so only those whistleblower rewards remain.
- The credited set splits into the credited proposers and the recipients of deposits.
  Before Altair, each credited proposer is the proposer of a block of the run.
- (L4a) A validator whose largest effective balance changed was converted.
  Its balance then ends at most the activation balance above its later credits.
- Effective balances stay. -/
theorem branchCorrections {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    (matched : BalancesMatch x.state) :
    let state := y.state
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let slots := preset.SLOTS_PER_EPOCH.toNat
    let p := parameters preset y.fork
    let positions := Finset.range state.validators.data.size
    let validator (i : ℕ) := state.validators.data[i]?
    let effective (i : ℕ) := balanceAt state i
    let current (i : ℕ) := isActiveAt state (getCurrentEpoch state) i
    let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
    let recent (i : ℕ) := before i || current i
    let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
    let total := max inc (∑ i ∈ positions with current i, effective i)
    let root := (integerSquareroot (UInt64.ofNat total)).toNat
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
    let base (i : ℕ) := if .altair ≤ y.fork then effective i / inc * perIncrement
      else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
    let seatReward := if .altair ≤ y.fork then
        total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
          slots / preset.SYNC_COMMITTEE_SIZE.toNat
      else 0
    let seats (i : ℕ) := if altair : .altair ≤ y.fork then
        ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
          (validator i).any (·.pubkey == key)).length
      else 0
    let sync (i : ℕ) := seats i * seatReward
    let syncProposer := if .altair ≤ y.fork then
        slots * preset.SYNC_COMMITTEE_SIZE.toNat *
          (seatReward * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
      else 0
    let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
    let whistleblowerP :=
      (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
    let slashBack (i : ℕ) :=
      if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
    let blocks := tail.blockCount
    let debited := ((if .shapella ≤ y.fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
      (if .pectra ≤ y.fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) *
        blocks
    let blockDeposits := if h : y.fork < .hegota then
        (if .pectra ≤ y.fork then 0
         else min (preset.MAX_DEPOSITS.toNat * blocks) (state.eth1DepositIndex h).toNat)
      else 0
    let creditedP :=
      (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0
        else blocks) + blockDeposits
    ∃ (debitedKeys creditedKeys : Finset ValidatorIndex) (pc deposit : ValidatorIndex → ℕ),
      debitedKeys.card ≤ debited ∧ creditedKeys.card ≤ creditedP ∧
      (∀ v, v ∉ debitedKeys → actualBalanceAt x v.toNat ≤
        actualBalanceAt y v.toNat + slashBack v.toNat + blocks * sync v.toNat) ∧
      (∀ v, actualBalanceAt y v.toNat ≤
        actualBalanceAt x v.toNat + blocks * sync v.toNat + pc v + deposit v) ∧
      (∀ v, v ∉ creditedKeys → pc v = 0 ∧ deposit v = 0) ∧
      (.pectra ≤ y.fork → ∀ v, deposit v = 0) ∧
      ∑ v ∈ creditedKeys, pc v ≤ proposerCredit + whistleblowerP ∧
      (∃ slashedNow : Finset ValidatorIndex,
        (∀ v ∈ slashedNow, (∀ validator, x.state.validators.data[v.toNat]? = some validator →
            validator.slashed = false) ∧ slashed v.toNat = true) ∧
        ∑ v ∈ creditedKeys, pc v ≤ (∑ i ∈ positions with recent i, base i) + syncProposer +
          (∑ v ∈ slashedNow, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ∧
      (∀ v validator later, x.state.validators.data[v.toNat]? = some validator →
        y.state.validators.data[v.toNat]? = some later →
        withdrawalMaxEffectiveBalance preset y.fork later ≠
          withdrawalMaxEffectiveBalance preset x.fork validator →
        actualBalanceAt y v.toNat ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
          blocks * sync v.toNat + pc v + deposit v) ∧
      (y.fork < .altair → ∃ slashedNow : Finset ValidatorIndex,
        (∀ v ∈ slashedNow, slashed v.toNat = true) ∧
        ∑ v ∈ creditedKeys, pc v ≤
          (∑ v ∈ slashedNow, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ∧
      (∃ proposerKeys depositKeys : Finset ValidatorIndex,
        creditedKeys = proposerKeys ∪ depositKeys ∧
        proposerKeys.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
          positions.filter (slashed ·) = ∅ then 0 else blocks) ∧
        depositKeys.card ≤ blockDeposits ∧
        (∀ v, v ∉ proposerKeys → pc v = 0) ∧ (∀ v, v ∉ depositKeys → deposit v = 0) ∧
        (y.fork < .altair →
          preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
          ∀ v ∈ proposerKeys, ∃ (f : Fork) (b a : BeaconState preset f)
            (engine : ExecutionEngine preset f) (signed : SignedBeaconBlock preset f)
            (due : upgradeDue config ⟨f, b⟩ = false)
            (ok : applySignedBlock config checks engine b signed true = .ok a),
            tail.Contains (.block engine signed due ok) ∧ signed.message.proposerIndex = v)) ∧
      (∀ v validator, v ∉ debitedKeys → x.state.validators.data[v.toNat]? = some validator →
        ∃ later, y.state.validators.data[v.toNat]? = some later ∧
          withdrawalMaxEffectiveBalance preset y.fork later =
            withdrawalMaxEffectiveBalance preset x.fork validator) ∧
      x.fork = y.fork ∧ EffectiveKept x.state y.state := by
  obtain ⟨F, a⟩ := x
  obtain ⟨b, rfl, deb, conv, props, dep, sl, pc, deposit, credits, shares, tally, owned⟩ :=
    Run.induction_counted (fun z pre => ∃ s : BeaconState preset F, z = ⟨F, s⟩ ∧
      ∃ (deb conv props dep sl : Finset ValidatorIndex) (pc deposit : ValidatorIndex → ℕ)
        (credits shares : ℕ), Tally a s pre.blockCount deb conv props dep sl pc deposit credits
          shares ∧
        (F < .altair →
          preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
          ∀ v ∈ props, ∃ (f : Fork) (b a : BeaconState preset f)
            (engine : ExecutionEngine preset f) (signed : SignedBeaconBlock preset f)
            (due : upgradeDue config ⟨f, b⟩ = false)
            (ok : applySignedBlock config checks engine b signed true = .ok a),
            pre.Contains (.block engine signed due ok) ∧ signed.message.proposerIndex = v))
      ⟨a, rfl, _, _, _, _, _, _, _, _, _, Tally.start a matched,
        fun _ _ v member => absurd member (Finset.notMem_empty v)⟩
      (fun engine signed due ok pre early prior => by
        obtain ⟨_, eq, _, _, props, _, _, _, _, _, _, tally, owned⟩ := prior
        cases eq
        obtain ⟨_, _, _, _, _, _, _, _, _, next, fresh⟩ :=
          tally.block early (applySignedBlock_ok ok).2.1
        refine ⟨_, rfl, _, _, _, _, _, _, _, _, _, next, fun phase0 apart v member => ?_⟩
        by_cases old : v ∈ props
        · obtain ⟨f, b, a, engine', signed', due', ok', contains, eq⟩ := owned phase0 apart v old
          exact ⟨f, b, a, engine', signed', due', ok', .earlier contains _, eq⟩
        · exact ⟨_, _, _, engine, signed, due, ok, .last pre _,
            (fresh phase0 apart v member old).symm⟩)
      (fun pre ok last computed epoch prior => by
        have count : (pre.snoc (.slot ok)).blockCount = pre.blockCount := rfl
        have lift : ∀ {b' a' : ForkedBeaconState preset} (st : Step config checks b' a'),
            pre.Contains st → (pre.snoc (.slot ok)).Contains st := fun _ c => .earlier c _
        generalize pre.snoc (.slot ok) = run at count lift ⊢
        clear ok
        obtain ⟨_, rfl, _, _, _, _, _, _, _, _, _, tally, owned⟩ := prior
        subst last
        rw [count]
        refine ⟨_, rfl, _, _, _, _, _, _, _, _, _, tally.slot computed epoch,
          fun phase0 apart v member => ?_⟩
        obtain ⟨f, b, a, engine, signed, due, ok', contains, eq⟩ := owned phase0 apart v member
        exact ⟨f, b, a, engine, signed, due, ok', lift _ contains, eq⟩)
      tail early same
  intro state inc slots p positions validator effective current before recent slashed total root
    perIncrement base seatReward seats sync syncProposer proposerCredit whistleblowerP slashBack
    blocks debited blockDeposits creditedP
  have hegota : F < .hegota := Nat.lt_trans early (by decide)
  -- The participant reward read at the start is the formula at the end.
  have rewardEq : 0 < blocks → .altair ≤ F → rewardRead a = seatReward := by
    intro positive altair
    obtain ⟨r, ok⟩ := tally.reward positive altair
    have okB : syncParticipantReward b = .ok r := by
      rw [syncParticipantReward_congr tally.within.total]; exact ok
    obtain ⟨read, _, readOk, _⟩ := syncParticipantReward_ok okB
    have value := syncParticipantReward_toNat readOk okB
    have read' := getTotalActiveBalance_toNat readOk
    have first : rewardRead a = r.toNat := by unfold rewardRead; rw [ok]
    rw [first, value, read']
    simp only [seatReward, total, perIncrement, root, inc, slots, ite_eq_left altair]
    rfl
  have syncEq : ∀ v, blocks * syncAt b (rewardRead a) v = blocks * sync v.toNat := by
    intro v
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · rw [zero, Nat.zero_mul, Nat.zero_mul]
    · by_cases altair : .altair ≤ F
      · rw [rewardEq positive altair]
        simp only [syncAt, dite_eq_left altair, sync, seats]
        rfl
      · simp only [syncAt, dite_eq_right altair, sync, seats]
        simp
  -- The proposer credits of attestations are at most the base rewards of the recent validators.
  have creditsLe : credits ≤ ∑ i ∈ positions with recent i, base i := by
    by_cases altair : .altair ≤ F
    swap
    · rw [(tally.phase0 (Nat.lt_of_not_le altair)).1]; exact Nat.zero_le _
    let weight (i : ℕ) := if recent i then base i else 0
    have readsB : Reads b weight := by
      intro index tot reward recentB totOk rewardOk
      have isRecent : recent index.toNat = true := by
        simp only [recent, before, current, Bool.or_eq_true]; exact recentB
      rw [show weight index.toNat = base index.toNat from ite_eq_left isRecent,
        getBaseReward_toNat rewardOk, getTotalActiveBalance_toNat totOk]
      rfl
    have support : ∀ i, a.validators.data.size ≤ i → weight i = 0 := by
      intro i outside
      by_cases isRecent : recent i = true
      · have recentB : isActiveAt b (getPreviousEpoch b) i = true ∨
            isActiveAt b (getCurrentEpoch b) i = true := by
          simpa [recent, before, current] using isRecent
        have := inside_of_recent ((tally.within.recent i).mp recentB)
        omega
      · exact ite_eq_right isRecent
    have bound := tally.potential altair weight (2 ^ 64) (Nat.le_refl _)
      (tally.within.reads_back readsB) support
    have upper := flagPotential_le b altair weight (2 ^ 64)
    have sumEq : ∑ i ∈ Finset.range (2 ^ 64), weight i =
        ∑ i ∈ positions with recent i, base i := by
      rw [show ∑ i ∈ Finset.range (2 ^ 64), weight i =
        ∑ i ∈ Finset.range (2 ^ 64), (if recent i = true then base i else 0) from rfl,
        ← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro i member
        simp only [Finset.mem_filter, Finset.mem_range, positions] at member ⊢
        exact ⟨Nat.lt_trans member.1 (BeaconState.validators_size_lt_of_lt_glamsterdam early b),
          member.2⟩
      · intro i member notIn
        exfalso
        simp only [Finset.mem_filter, Finset.mem_range, positions, not_and] at member notIn
        have recentB : isActiveAt b (getPreviousEpoch b) i = true ∨
            isActiveAt b (getCurrentEpoch b) i = true := by
          simpa [recent, before, current] using member.2
        exact notIn (inside_of_recent recentB) member.2
    have denominator : proposerDenominator = 448 := by decide
    rw [denominator] at bound
    rw [sumEq] at upper
    omega
  -- A run inside one epoch has at most one block for each slot of the epoch.
  have blocksLe : 0 < slots → blocks ≤ slots := by
    intro positive
    have epochs := congrArg UInt64.toNat same
    simp only [getCurrentEpoch_toNat] at epochs
    have low := Nat.div_mul_le_self a.slot.toNat slots
    have high := Nat.lt_div_mul_add (a := b.slot.toNat) positive
    have count := tail.blocks_le_slots (a := a.slot.toNat / slots * slots)
      (b := a.slot.toNat / slots * slots + slots - 1) low (by
        change b.slot.toNat ≤ _
        change b.slot.toNat / slots = a.slot.toNat / slots at epochs
        rw [epochs] at high
        omega)
    change tail.blockCount ≤ slots
    omega
  -- The proposer shares of the sync aggregates.
  have sharesLe : shares ≤ syncProposer := by
    by_cases altair : .altair ≤ F
    swap
    · rw [(tally.phase0 (Nat.lt_of_not_le altair)).2]; exact Nat.zero_le _
    have bound := tally.share altair
    have proposerEq : syncProposer = slots * preset.SYNC_COMMITTEE_SIZE.toNat *
        (seatReward * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := ite_eq_left altair
    rw [proposerEq]
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · change shares ≤ blocks * _ at bound
      rw [zero, Nat.zero_mul] at bound
      omega
    · rw [rewardEq positive altair] at bound
      change shares ≤ blocks * _ at bound
      rcases Nat.eq_zero_or_pos slots with none | some
      · have : seatReward = 0 := by
          simp only [seatReward, ite_eq_left altair, none, Nat.div_zero, Nat.zero_div]
        rw [this, Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.mul_zero] at bound
        omega
      · calc shares ≤ blocks * _ := bound
          _ ≤ slots * _ := Nat.mul_le_mul_right _ (blocksLe some)
          _ = _ := by rw [Nat.mul_assoc]
  have whistleLe : ∑ v ∈ sl, effectiveAt ⟨F, b⟩ v.toNat /
      (parameters preset F).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (∑ v ∈ sl, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    sum_div_le_div_sum sl (fun v => effectiveAt ⟨F, b⟩ v.toNat) _
  have pcSum : ∑ v ∈ props ∪ dep, pc v = ∑ v ∈ props, pc v :=
    (Finset.sum_subset Finset.subset_union_left fun v _ notIn => tally.pcZero v notIn).symm
  have slashedSub : ∑ v ∈ sl, effective v.toNat ≤ ∑ i ∈ positions with slashed i, effective i := by
    rw [← Finset.sum_image (f := effective) (s := sl) (g := UInt64.toNat)
      (fun x _ y _ eq => UInt64.toNat_inj.mp eq)]
    apply Finset.sum_le_sum_of_subset
    intro i member
    obtain ⟨v, inSl, rfl⟩ := Finset.mem_image.mp member
    have marked := (tally.newly v inSl).2
    simp only [Finset.mem_filter, Finset.mem_range, positions]
    exact ⟨inside_of_slashedAt marked, marked⟩
  have budget : ∑ v ∈ props ∪ dep, pc v ≤ (∑ i ∈ positions with recent i, base i) +
      syncProposer + (∑ v ∈ sl, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    rw [pcSum]
    have := tally.budget
    omega
  -- The credited validators.
  have propsCard : props.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
      positions.filter (slashed ·) = ∅ then 0 else blocks) := by
    split
    · rename_i zero
      obtain ⟨credit0, -, slash0⟩ := zero
      have credit0' : (∑ i ∈ positions with recent i, base i) + syncProposer = 0 := credit0
      suffices empty : props = ∅ by rw [empty]; rfl
      by_contra nonempty
      rcases tally.propsPos (Finset.nonempty_iff_ne_empty.mpr nonempty) with
        positive | positive | ⟨v, member⟩
      · omega
      · omega
      · have marked := (tally.newly v member).2
        have : v.toNat ∈ positions.filter (slashed ·) := by
          simp only [Finset.mem_filter, Finset.mem_range, positions]
          exact ⟨inside_of_slashedAt marked, marked⟩
        rw [slash0] at this
        exact Finset.notMem_empty _ this
    · exact tally.propsCard
  have depCard : dep.card ≤ blockDeposits := by
    have unfolded : blockDeposits = if .pectra ≤ F then 0
        else min (preset.MAX_DEPOSITS.toNat * blocks) (b.eth1DepositIndex hegota).toNat :=
      dite_eq_left hegota
    rw [unfolded]
    split
    · rename_i pectra
      rw [tally.electra pectra]
      rfl
    · have one := tally.depCard
      have two := tally.depIndex hegota
      exact le_min one (by omega)
  have creditedCard : (props ∪ dep).card ≤ creditedP :=
    Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add propsCard depCard)
  refine ⟨deb, props ∪ dep, pc, deposit, tally.debCard, creditedCard, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ⟨props, dep, rfl, propsCard, depCard, tally.pcZero, tally.depositZero, owned⟩, ?_, rfl,
    tally.within.effective⟩
  · intro v notIn
    have := tally.down v notIn
    rw [syncEq v] at this
    exact this
  · intro v
    have := tally.up v
    rw [syncEq v] at this
    exact this
  · intro v notIn
    simp only [Finset.mem_union, not_or] at notIn
    exact ⟨tally.pcZero v notIn.1, tally.depositZero v notIn.2⟩
  · intro pectra v
    exact tally.depositZero v (by rw [tally.electra pectra]; exact Finset.notMem_empty v)
  · calc _ ≤ _ := budget
      _ ≤ _ := Nat.add_le_add_left (Nat.div_le_div_right slashedSub) _
  · exact ⟨sl, fun v member => ⟨(tally.newly v member).1, (tally.newly v member).2⟩, budget⟩
  · intro v validator later found foundB differ
    have member : v ∈ conv := by
      by_contra notConv
      obtain ⟨later', found', same⟩ := tally.kept v validator notConv found
      have : some later' = some later := found'.symm.trans foundB
      cases this
      apply differ
      simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, same]
    have := tally.converted v member
    rw [syncEq v] at this
    exact this
  · intro pre
    have ph := tally.phase0 pre
    refine ⟨sl, fun v member => (tally.newly v member).2, ?_⟩
    rw [pcSum]
    have := tally.budget
    omega
  · intro v validator notIn found
    obtain ⟨later, foundB, same⟩ := tally.kept v validator (fun h => notIn (tally.convSub h)) found
    exact ⟨later, foundB,
      by simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, same]⟩


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

/-- The largest effective balance of a validator reads only its credentials. -/
private theorem withdrawalMax_congr {f : Fork} {a b : Validator}
    (same : a.withdrawalCredentials = b.withdrawalCredentials) :
    withdrawalMaxEffectiveBalance preset f a = withdrawalMaxEffectiveBalance preset f b := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance hasCompoundingWithdrawalCredential
  rw [same]

/-- The update of one effective balance changes only the validator at its position.

It keeps the credentials of that validator and every balance. -/
private theorem updateEffectiveBalance_read {f : Fork} {s t : BeaconState preset f} {j : ℕ}
    (ok : updateEffectiveBalance s j = .ok t) :
    t.balances = s.balances ∧ ∃ validator balance next,
      s.validators.data[j]? = some validator ∧ s.balances.data[j]? = some balance ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f validator) balance
        validator.effectiveBalance = .ok next ∧
      ∀ i, t.validators.data[i]? =
        if i = j then some { validator with effectiveBalance := next }
        else s.validators.data[i]? := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, balance, read, next, updated, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  refine ⟨rfl, validator, balance, next, getValidatorAt_eq_ok_iff.mp found,
    getBalanceAt_eq_ok_iff.mp read, updated, fun i => ?_⟩
  by_cases same : i = j
  · subst i
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
  · simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm same, same]

/-- The update of the effective balances keeps every credential and every balance. -/
private theorem effectiveUpdates_keep {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : ℕ) :
    t.balances = s.balances ∧ (i < s.validators.data.size → i < t.validators.data.size) ∧
      ∀ old w, s.validators.data[i]? = some old → t.validators.data[i]? = some w →
        w.withdrawalCredentials = old.withdrawalCredentials := by
  unfold processEffectiveBalanceUpdates at ok
  have kept := foldlM_ok_invariant
    (fun w : BeaconState preset f => w.balances = s.balances ∧
      (i < s.validators.data.size → i < w.validators.data.size) ∧
      ∀ old val, s.validators.data[i]? = some old → w.validators.data[i]? = some val →
        val.withdrawalCredentials = old.withdrawalCredentials)
    (fun w j w' previous step => by
      obtain ⟨balances, validator, balance, next, found, -, -, reads⟩ :=
        updateEffectiveBalance_read step
      refine ⟨balances.trans previous.1, fun inside => ?_, fun old val start read => ?_⟩
      · have before := previous.2.1 inside
        have := reads i
        by_cases same : i = j
        · subst same
          simp only [↓reduceIte] at this
          exact (Array.getElem?_eq_some_iff.mp this).1
        · simp only [same, ↓reduceIte, Array.getElem?_eq_getElem before] at this
          exact (Array.getElem?_eq_some_iff.mp this).1
      · rw [reads i] at read
        by_cases same : i = j
        · subst same
          simp only [↓reduceIte, Option.some.injEq] at read
          subst val
          exact previous.2.2 old validator start found
        · simp only [same, ↓reduceIte] at read
          exact previous.2.2 old val start read)
    ⟨rfl, id, fun old val start read => by rw [start, Option.some.injEq] at read; rw [read]⟩ ok
  exact kept

/-- Take an effective balance bounded by its largest value after the update.

The update of the effective balances lowers it by at most the fall allowed below its balance. -/
private theorem effectiveUpdates_fall {f : Fork} {s t : BeaconState preset f}
    (bands : preset.IncrementWithinUpwardBand)
    (ok : processEffectiveBalanceUpdates s = .ok t) {i : ℕ} {old : Validator}
    (found : s.validators.data[i]? = some old)
    (capped : ∀ w, t.validators.data[i]? = some w →
      old.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w) :
    old.effectiveBalance.toNat ≤ effectiveAt ⟨f, t⟩ i +
      fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
        old.effectiveBalance.toNat (actualBalanceAt ⟨f, s⟩ i) := by
  obtain ⟨-, grows, credentials⟩ := effectiveUpdates_keep ok i
  have inside := grows (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨w, read⟩ : ∃ w, t.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have capOld :
      old.effectiveBalance.toNat ≤ (withdrawalMaxEffectiveBalance preset f old).toNat := by
    have := capped w read
    rw [withdrawalMax_congr (credentials old w found read)] at this
    exact UInt64.le_iff_toNat_le.mp this
  generalize hb : actualBalanceAt ⟨f, s⟩ i = b
  generalize hg : fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
    old.effectiveBalance.toNat b = gap
  have increment := bands.1
  have band := bands.2
  unfold processEffectiveBalanceUpdates at ok
  have result := foldlM_ok_invariant
    (fun u : BeaconState preset f => u.balances = s.balances ∧
      ∀ val, u.validators.data[i]? = some val →
        val.withdrawalCredentials = old.withdrawalCredentials ∧
        (val.effectiveBalance = old.effectiveBalance ∨ val.effectiveBalance.toNat ≤ b) ∧
        old.effectiveBalance.toNat ≤ val.effectiveBalance.toNat + gap)
    (fun u j u' previous step => by
      obtain ⟨balances, validator, balance, next, located, balanceRead, updated, reads⟩ :=
        updateEffectiveBalance_read step
      refine ⟨balances.trans previous.1, fun val read' => ?_⟩
      rw [reads i] at read'
      by_cases same : i = j
      · subst same
        simp only [↓reduceIte, Option.some.injEq] at read'
        subst val
        obtain ⟨keys, current, held⟩ := previous.2 validator located
        have balanceValue : balance.toNat = b := by
          rw [← hb]
          simp [actualBalanceAt, ← previous.1, balanceRead]
        have capValue := capOld
        rw [withdrawalMax_congr (f := f) (keys.symm)] at capValue
        refine ⟨keys, ?_⟩
        rcases updatedEffectiveBalance_split updated with ⟨rfl, -, -⟩ | ⟨rfl, crossed⟩
        · exact ⟨current, held⟩
        · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
            UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
          have value : (min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
              (withdrawalMaxEffectiveBalance preset f validator)).toNat =
              min (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
                (withdrawalMaxEffectiveBalance preset f validator).toNat := by
            rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
          simp only [value]
          have remainder := Nat.mod_lt balance.toNat increment
          have remainderLe := Nat.mod_le balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          subst balanceValue
          rw [← hg] at held ⊢
          by_cases low : old.effectiveBalance.toNat ≤ balance.toNat + preset.downwardBand
          · simp only [fallGap, low, ↓reduceIte] at held ⊢
            generalize balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = r at *
            rcases current with current | current
            · rw [current] at crossed
              exact ⟨.inr (by omega), by omega⟩
            · exact ⟨.inr (by omega), by omega⟩
          · simp only [fallGap, low, ↓reduceIte] at held ⊢
            generalize balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = r at *
            exact ⟨.inr (by omega), by omega⟩
      · simp only [same, ↓reduceIte] at read'
        exact previous.2 val read')
    ⟨rfl, fun val read' => by
      rw [found, Option.some.injEq] at read'
      subst val
      exact ⟨rfl, .inl rfl, Nat.le_add_right _ _⟩⟩ ok
  have final := (result.2 w read).2.2
  simpa [effectiveAt, read] using final


/-! ## The steps of an epoch that do not lower the balance of a voter -/

/-- Writing a validator keeps every balance. -/
private theorem setValidatorAt_balances {f : Fork} {s t : BeaconState preset f}
    {i : ℕ} {v : Validator} (ok : s.setValidatorAt i v = .ok t) : t.balances = s.balances := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

/-- Starting an exit keeps every balance. -/
private theorem initiateValidatorExit_balances {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    t.balances = s.balances := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · obtain ⟨_, rfl⟩ := setValidator_ok set
    exact (exitQueue_validators queue).2

/-- A fold of steps that keep every balance keeps every balance. -/
private theorem foldlM_balances {f : Fork} {α ε : Type}
    {action : BeaconState preset f → α → Except ε (BeaconState preset f)}
    (keeps : ∀ s a t, action s a = .ok t → t.balances = s.balances)
    {s t : BeaconState preset f} {xs : List α} (ok : xs.foldlM action s = .ok t) :
    t.balances = s.balances :=
  foldlM_ok_invariant (fun t => t.balances = s.balances)
    (fun a b c previous step => (keeps a b c step).trans previous) rfl ok

/-- The registry updates keep every balance. -/
private theorem registryUpdates_balances {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : t.balances = s.balances := by
  have electra (epoch : Epoch) (s t : BeaconState preset f) (i : Nat)
      (ok : updateRegistryEntryElectra config epoch s i = .ok t) :
      t.balances = s.balances := by
    simp only [updateRegistryEntryElectra, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · obtain ⟨_, _, set⟩ := bind_ok_iff.mp ok
      exact setValidatorAt_balances (liftAccessor_ok.mp set)
    · split at ok
      · obtain ⟨_, _, exited⟩ := bind_ok_iff.mp ok
        exact initiateValidatorExit_balances (liftAccessor_ok.mp exited)
      · split at ok
        · exact setValidatorAt_balances (liftAccessor_ok.mp ok)
        · cases ok; rfl
  have ordinary (s t : BeaconState preset f) (i : Nat)
      (ok : updateRegistryEntry config s i = .ok t) : t.balances = s.balances := by
    simp only [updateRegistryEntry, bind_ok_iff] at ok
    obtain ⟨_, _, _, _, u, set, rest⟩ := ok
    have same := setValidatorAt_balances (liftAccessor_ok.mp set)
    split at rest
    · obtain ⟨_, _, exited⟩ := bind_ok_iff.mp rest
      exact (initiateValidatorExit_balances (liftAccessor_ok.mp exited)).trans same
    · cases rest; exact same
  have activate (s t : BeaconState preset f) (i : ValidatorIndex)
      (ok : activateValidator s i = .ok t) : t.balances = s.balances := by
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setValidator_ok set
    rfl
  unfold processRegistryUpdates at ok
  split at ok
  · obtain ⟨epoch, _, folded⟩ := bind_ok_iff.mp ok
    exact foldlM_balances (fun s i t => electra epoch s t i) folded
  · obtain ⟨u, first, last⟩ := bind_ok_iff.mp ok
    exact (foldlM_balances (fun s i t => activate s t i) last).trans
      (foldlM_balances (fun s i t => ordinary s t i) first)

/-- The slashings keep the balance of a validator that is not slashed. -/
private theorem slashings_unslashed {f : Fork} {s t : BeaconState preset f}
    (early : f < .glamsterdam) (ok : processSlashings s = .ok t) {i : ℕ} {w : Validator}
    (found : s.validators.data[i]? = some w) (clear : w.slashed = false) :
    actualBalanceAt ⟨f, t⟩ i = actualBalanceAt ⟨f, s⟩ i := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have notDue : ¬ SlashingPenaltyDue preset (getCurrentEpoch s) w := by
    simp [SlashingPenaltyDue, clear]
  by_cases electra : .pectra ≤ f
  · obtain ⟨_, _, _, _, _, rest⟩ := processSlashings_balances_toNat_of_electra electra
      (s.validators.bound early) ok
    obtain ⟨validator, read, balances⟩ := (rest i).1 inside
    rw [found, Option.some.injEq] at read
    subst validator
    simp only [notDue, ↓reduceIte, Nat.sub_zero] at balances
    simp only [actualBalanceAt]
    cases h : s.balances.data[i]? <;> cases h' : t.balances.data[i]? <;> simp_all
  · obtain ⟨_, _, _, _, _, rest⟩ := processSlashings_balances_toNat_of_lt_electra
      (Nat.lt_of_not_le electra) ok
    obtain ⟨validator, read, balances⟩ := (rest i).1 inside
    rw [found, Option.some.injEq] at read
    subst validator
    simp only [notDue, ↓reduceIte, Nat.sub_zero] at balances
    simp only [actualBalanceAt]
    cases h : s.balances.data[i]? <;> cases h' : t.balances.data[i]? <;> simp_all

/-- From Electra, the pending deposits of an epoch never lower a balance. -/
private theorem pendingDeposits_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t)
    (matched : BalancesMatch s) (i : ℕ) :
    actualBalanceAt ⟨f, s⟩ i ≤ actualBalanceAt ⟨f, t⟩ i := by
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, appliedOk, rfl⟩ :=
    processPendingDeposits_applied ok
  have result := foldlM_ok_invariant
    (fun u : BeaconState preset f => BalancesMatch u ∧
      actualBalanceAt ⟨f, s⟩ i ≤ actualBalanceAt ⟨f, u⟩ i)
    (fun u deposit u' previous step => by
      rcases applyPendingDeposit_cases step with rfl | ⟨index, raised⟩ | ⟨_, added⟩
      · exact previous
      · refine ⟨?_, ?_⟩
        · unfold BalancesMatch at previous ⊢
          rw [increaseBalance_validators raised]
          obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
          simpa [BeaconState.putBalance] using previous.1
        · rw [actualBalanceAt_increaseBalance raised]
          exact Nat.le_add_right_of_le previous.2
      · obtain ⟨validators, balances⟩ := addValidatorToRegistry_push added previous.1
        refine ⟨?_, ?_⟩
        · have := previous.1
          unfold BalancesMatch at this ⊢
          rw [validators, balances]
          simp [this]
        · refine previous.2.trans ?_
          simp only [actualBalanceAt, balances, Array.getElem?_push]
          split
          · rename_i at_end
            simp [at_end]
          · exact Nat.le_refl _)
    ⟨matched, Nat.le_refl _⟩ appliedOk
  simpa [actualBalanceAt] using result.2

/-- Take a validator that no consolidation read by a pass of the pending consolidations takes from.

The pass never lowers the balance of that validator. -/
private theorem passConsolidations_mono {f : Fork} {nextEpoch : Epoch} {i : ℕ} :
    ∀ {list : List PendingConsolidation} {s : BeaconState preset f} {result},
      passPendingConsolidations nextEpoch s list = .ok result →
      (∀ c ∈ list, c.sourceIndex.toNat = i → ∀ w, s.validators.data[i]? = some w →
        w.slashed = false → nextEpoch < w.withdrawableEpoch) →
      actualBalanceAt ⟨f, s⟩ i ≤ actualBalanceAt ⟨f, result.1⟩ i
  | [], _, _, computed, _ => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Nat.le_refl _
  | consolidation :: rest, s, result, computed, apart => by
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i source sourceOk
    have sourceRead := getValidator_eq_ok_iff.mp (liftAccessor_ok.mp sourceOk)
    have restApart : ∀ c ∈ rest, c.sourceIndex.toNat = i → ∀ w, s.validators.data[i]? = some w →
        w.slashed = false → nextEpoch < w.withdrawableEpoch :=
      fun c member => apart c (List.mem_cons_of_mem _ member)
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      exact (passConsolidations_mono recur restApart :)
    split at computed
    · cases computed
      exact Nat.le_refl _
    rename_i slashedFlag notWithdrawable
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i loweredState loweredOk
    split at computed
    · cases computed
    rename_i raisedState raisedOk
    split at computed
    · cases computed
    rename_i recur
    cases computed
    have lowered := liftAccessor_ok.mp loweredOk
    have raised := liftAccessor_ok.mp raisedOk
    have other : consolidation.sourceIndex.toNat ≠ i := by
      intro same
      subst same
      have := apart consolidation List.mem_cons_self rfl source sourceRead
        (by simpa using slashedFlag)
      exact notWithdrawable this
    have validators : raisedState.validators = s.validators :=
      (increaseBalance_validators raised).trans (decreaseBalance_validators lowered)
    have later := passConsolidations_mono recur (fun c member same w read clear =>
      restApart c member same w (by rw [← validators]; exact read) clear)
    have down := actualBalanceAt_decreaseBalance lowered i
    have up := actualBalanceAt_increaseBalance raised i
    simp only [other, ↓reduceIte, Nat.sub_zero] at down
    dsimp only
    split at up <;> omega

/-- A validator active in an epoch exits after it.

When its withdrawal waits at least one epoch after its exit, it withdraws after the next epoch. -/
private theorem withdrawable_after_next {w : Validator} {epoch next : Epoch}
    (active : isActiveValidator w epoch = true) (bound : next.toNat ≤ epoch.toNat + 1)
    (ordered : w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
      w.withdrawableEpoch.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    next < w.withdrawableEpoch := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  have exit := UInt64.lt_iff_toNat_lt.mp active.2
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-- Suppose that the sources of the pending consolidations exit with the withdrawal delay.

Take a validator active in the current epoch.

From Electra, the pending deposits and consolidations of an epoch never lower its balance. -/
private theorem pendingBalances_mono {f : Fork} {s t : BeaconState preset f}
    (ok : processPendingBalances config checks s = .ok t) (matched : BalancesMatch s)
    (holds : PendingConsolidationInvariant config s)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} (active : isActiveAt s (getCurrentEpoch s) i = true) :
    actualBalanceAt ⟨f, s⟩ i ≤ actualBalanceAt ⟨f, t⟩ i := by
  unfold processPendingBalances at ok
  split at ok
  · rename_i electra
    obtain ⟨deposited, depositedOk, consolidatedOk⟩ := bind_ok_iff.mp ok
    have first := pendingDeposits_mono depositedOk matched i
    have invariant := PendingConsolidationInvariant.pendingDeposits holds depositedOk
    have keeps : StepKeeps s deposited := by
      have copy := depositedOk
      unfold processPendingDeposits at copy
      simp only [bind, Except.bind, pure, Except.pure] at copy
      repeat' (split at copy <;> try cases copy)
      all_goals exact (stepKeeps_passPendingDeposits ‹_›).trans StepKeeps.of_validators
    have epoch : getCurrentEpoch deposited = getCurrentEpoch s := by
      simp only [getCurrentEpoch, keeps.2.1]
    have activeThere : isActiveAt deposited (getCurrentEpoch s) i = true := by
      rw [keeps.2.2 _ (getCurrentEpoch_le_activityFixedEpoch s)]
      exact active
    obtain ⟨result, passed, balances, -⟩ := processPendingConsolidations_pass consolidatedOk
    have second := passConsolidations_mono passed fun c member same w read _ => by
      obtain ⟨-, sources⟩ := invariant electra
      obtain ⟨w', read', -, ordered, -⟩ := sources c member
      rw [same, read] at read'
      cases read'
      obtain ⟨w'', read'', isActive⟩ := isActiveAt_eq_true_iff.mp activeThere
      rw [read, Option.some.injEq] at read''
      subst w''
      refine withdrawable_after_next isActive ?_ ordered delay
      rw [epoch, UInt64.toNat_add]
      have := Nat.mod_le ((getCurrentEpoch s).toNat + (1 : UInt64).toNat) (2 ^ 64)
      simp only [UInt64.toNat_one] at this ⊢
      omega
    have last : actualBalanceAt ⟨f, t⟩ i = actualBalanceAt ⟨f, result.1⟩ i := by
      simp only [actualBalanceAt, balances]
    omega
  · cases ok
    exact Nat.le_refl _

/-- Justification and finalization keep the registry, the balances, the slot and the scores. -/
private theorem justification_same {f : Fork} {s t : BeaconState preset f}
    (ok : processJustificationAndFinalization s = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances ∧ t.slot = s.slot ∧
      t.inactivityScores = s.inactivityScores := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest]⟩

/-- Take a validator active in the epoch of an epoch transition and not slashed after it.

Before Gloas, the transition never lowers its balance between the rewards and the update.

That update of the effective balances starts from the effective balances before the transition.

The update gives the registry of the transition. -/
private theorem epoch_parts {f : Fork} {c t : BeaconState preset f} (early : f < .glamsterdam)
    (ok : processEpoch config checks c = .ok t)
    (holds : PendingConsolidationInvariant config c) (matched : BalancesMatch c)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} (active : isActiveAt c (getCurrentEpoch c) i = true)
    (unslashed : ∀ w, t.validators.data[i]? = some w → w.slashed = false) :
    ∃ justified rewarded before after : BeaconState preset f,
      processJustificationAndFinalization c = .ok justified ∧
      (∀ altair : .altair ≤ f, ∃ scored,
        processInactivityUpdates config justified altair = .ok scored ∧
        processRewardsAndPenalties config scored = .ok rewarded) ∧
      (f < .altair → processRewardsAndPenalties config justified = .ok rewarded) ∧
      actualBalanceAt ⟨f, rewarded⟩ i ≤ actualBalanceAt ⟨f, before⟩ i ∧
      EffectiveKept c before ∧ processEffectiveBalanceUpdates before = .ok after ∧
      t.validators = after.validators ∧
      c.validators.data.size ≤ before.validators.data.size := by
  have tail {a b c d : BeaconState preset f}
      (clear : processSlashingsReset a = .ok b) (mix : processRandaoMixesReset b = .ok c)
      (same : d.validators = c.validators) : d.validators = a.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clear
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mix
    exact same
  -- The registry updates keep the flag of a validator that is slashed at the end.
  have clearAt {registered balanced : BeaconState preset f}
      (frame : Frame registered balanced) (same : t.validators = balanced.validators) :
      ∀ w, registered.validators.data[i]? = some w → w.slashed = false := by
    intro w found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have grown := Nat.lt_of_lt_of_le inside frame.registryGrows
    have later := unslashed _ (by rw [same]; exact Array.getElem?_eq_getElem grown)
    cases flag : w.slashed
    · rfl
    · have := frame.slashed i w _ found (Array.getElem?_eq_getElem grown) flag
      rw [later] at this
      cases this
  unfold processEpoch at ok
  split at ok
  · rename_i altair
    unfold processEpochAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
      registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
      balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, ok⟩ := ok
    have paidEq : paid = pending := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid
    have justifiedSame := justification_same justifiedOk
    have scoredSame := balanceDrift_inactivity scoredOk
    -- The registry after the transition is the one after the update.
    have last : t.validators = mixed.validators := by
      split at ok <;> simp only [bind_ok_iff] at ok <;>
        obtain ⟨_, rooted, _, synced, _, looked, windowed⟩ := ok
      · exact (balanceDrift_epochEnd synced looked windowed).1.trans
          (balanceDrift_summaries rooted).1
      · exact (balanceDrift_epochEnd synced looked windowed).1.trans
          (balanceDrift_historical rooted).1
    have final : t.validators = balanced.validators := tail clearedOk mixedOk last
    -- The reset of the deposit votes.
    have resetFrame : Frame slashed reset ∧ reset.balances = slashed.balances ∧
        StepKeeps slashed reset ∧ reset.validators = slashed.validators := by
      split at resetOk
      · exact ⟨(frame_processEth1DataReset resetOk).toFrame, (balanceDrift_reset resetOk).2,
          StepKeeps.of_step (frame_processEth1DataReset resetOk).registryGrows
            (activeStep_processEth1DataReset resetOk), (balanceDrift_reset resetOk).1⟩
      · cases resetOk
        exact ⟨Frame.refl _, rfl, StepKeeps.refl _, rfl⟩
    have frame : Frame registered balanced :=
      (frame_processSlashings slashedOk).toFrame.trans <| resetFrame.1.trans <|
        (frame_processPendingBalances pendingOk).toFrame.trans
          (frame_processEffectiveBalanceUpdates balancedOk).toFrame
    have clear := clearAt frame final
    -- What holds just before the pending balances.
    have rewardedMatch : BalancesMatch rewarded := by
      refine (frame_processRewardsAndPenalties rewardedOk).balancesMatch ?_
      unfold BalancesMatch at matched ⊢
      rw [scoredSame.1, scoredSame.2, justifiedSame.1, justifiedSame.2.1]
      exact matched
    have resetMatch : BalancesMatch reset :=
      resetFrame.1.balancesMatch <| (frame_processSlashings slashedOk).balancesMatch <|
        (frame_processRegistryUpdates registeredOk).balancesMatch rewardedMatch
    have resetHolds : PendingConsolidationInvariant config reset := by
      have one := ((holds.justification justifiedOk).inactivity scoredOk).rewards rewardedOk
      have two := (one.registry registeredOk).slashings slashedOk
      split at resetOk
      · exact two.eth1Reset resetOk
      · cases resetOk; exact two
    have keeps : StepKeeps c reset :=
      (stepKeeps_processJustificationAndFinalization justifiedOk).trans <|
      (stepKeeps_processInactivityUpdates scoredOk).trans <|
      (StepKeeps.of_step (frame_processRewardsAndPenalties rewardedOk).registryGrows
        (activeStep_processRewardsAndPenalties rewardedOk)).trans <|
      (stepKeeps_processRegistryUpdates registeredOk).trans <|
      (StepKeeps.of_step (frame_processSlashings slashedOk).registryGrows
        (activeStep_processSlashings slashedOk)).trans resetFrame.2.2.1
    have resetActive : isActiveAt reset (getCurrentEpoch reset) i = true := by
      have epoch : getCurrentEpoch reset = getCurrentEpoch c := by
        simp only [getCurrentEpoch, keeps.2.1]
      rw [epoch, keeps.2.2 _ (getCurrentEpoch_le_activityFixedEpoch c)]
      exact active
    have pendingUp := pendingBalances_mono pendingOk resetMatch resetHolds delay resetActive
    -- The balance after the rewards reaches the update.
    have registeredSame : actualBalanceAt ⟨f, registered⟩ i = actualBalanceAt ⟨f, rewarded⟩ i := by
      simp only [actualBalanceAt, registryUpdates_balances registeredOk]
    have slashedSame : actualBalanceAt ⟨f, slashed⟩ i = actualBalanceAt ⟨f, registered⟩ i := by
      cases found : registered.validators.data[i]? with
      | none =>
        have matchedRegistered := (frame_processRegistryUpdates registeredOk).balancesMatch
          rewardedMatch
        have outside : registered.validators.data.size ≤ i := by
          simpa using (Array.getElem?_eq_none_iff.mp found)
        have registeredNone : registered.balances.data[i]? = none := by
          rw [Array.getElem?_eq_none_iff]
          unfold BalancesMatch at matchedRegistered
          omega
        have slashedMatch := (frame_processSlashings slashedOk).balancesMatch matchedRegistered
        have grows := (frame_processSlashings slashedOk).registryGrows
        have slashedNone : slashed.balances.data[i]? = none := by
          rw [Array.getElem?_eq_none_iff]
          unfold BalancesMatch at slashedMatch
          have sameSize : slashed.validators.data.size = registered.validators.data.size := by
            rw [balanceDrift_slashings slashedOk]
          omega
        simp [actualBalanceAt, registeredNone, slashedNone]
      | some w => exact slashings_unslashed early slashedOk found (clear w found)
    have resetSame : actualBalanceAt ⟨f, reset⟩ i = actualBalanceAt ⟨f, slashed⟩ i := by
      simp only [actualBalanceAt, resetFrame.2.1]
    -- The update starts from the effective balances before the transition.
    have kept : EffectiveKept c pending := by
      have one := effectiveKept_trans (effectiveKept_registry registeredOk)
        (effectiveKept_trans (effectiveKept_data
          (by rw [resetFrame.2.2.2, balanceDrift_slashings slashedOk]))
          (effectiveKept_pending pendingOk)
          (by rw [resetFrame.2.2.2, balanceDrift_slashings slashedOk]))
        (registryLifecycle_processRegistryUpdates registeredOk).size_le
      intro j inside
      have same : rewarded.validators = c.validators := by
        rw [processRewardsAndPenalties_frame rewardedOk]
        exact scoredSame.1.trans justifiedSame.1
      simpa only [effectiveAt, same] using one j (by simpa [same] using inside)
    exact ⟨justified, rewarded, pending, balanced, justifiedOk,
      fun _ => ⟨scored, scoredOk, rewardedOk⟩,
      fun before => absurd altair (Nat.not_le_of_lt before),
      by omega, kept, balancedOk, final,
      Nat.le_trans keeps.1 (frame_processPendingBalances pendingOk).registryGrows⟩
  · rename_i altair
    simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk,
      slashed, slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk,
      mixed, mixedOk, rooted, rootedOk, rotated⟩ := ok
    have justifiedSame := justification_same justifiedOk
    have rotatedSame : t.validators = rooted.validators := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; rfl
    have final : t.validators = balanced.validators :=
      tail clearedOk mixedOk (rotatedSame.trans (balanceDrift_historical rootedOk).1)
    have frame : Frame registered balanced :=
      (frame_processSlashings slashedOk).toFrame.trans <|
        (frame_processEth1DataReset resetOk).toFrame.trans
          (frame_processEffectiveBalanceUpdates balancedOk).toFrame
    have clear := clearAt frame final
    have rewardedMatch : BalancesMatch rewarded := by
      refine (frame_processRewardsAndPenalties rewardedOk).balancesMatch ?_
      unfold BalancesMatch at matched ⊢
      rw [justifiedSame.1, justifiedSame.2.1]
      exact matched
    have registeredSame : actualBalanceAt ⟨f, registered⟩ i = actualBalanceAt ⟨f, rewarded⟩ i := by
      simp only [actualBalanceAt, registryUpdates_balances registeredOk]
    have slashedSame : actualBalanceAt ⟨f, slashed⟩ i = actualBalanceAt ⟨f, registered⟩ i := by
      cases found : registered.validators.data[i]? with
      | none =>
        have matchedRegistered := (frame_processRegistryUpdates registeredOk).balancesMatch
          rewardedMatch
        have outside : registered.validators.data.size ≤ i := by
          simpa using (Array.getElem?_eq_none_iff.mp found)
        have registeredNone : registered.balances.data[i]? = none := by
          rw [Array.getElem?_eq_none_iff]
          unfold BalancesMatch at matchedRegistered
          omega
        have slashedMatch := (frame_processSlashings slashedOk).balancesMatch matchedRegistered
        have slashedNone : slashed.balances.data[i]? = none := by
          rw [Array.getElem?_eq_none_iff]
          unfold BalancesMatch at slashedMatch
          have sameSize : slashed.validators.data.size = registered.validators.data.size := by
            rw [balanceDrift_slashings slashedOk]
          omega
        simp [actualBalanceAt, registeredNone, slashedNone]
      | some w => exact slashings_unslashed early slashedOk found (clear w found)
    have resetSame : actualBalanceAt ⟨f, reset⟩ i = actualBalanceAt ⟨f, slashed⟩ i := by
      simp only [actualBalanceAt, (balanceDrift_reset resetOk).2]
    have same : rewarded.validators = c.validators := by
      rw [processRewardsAndPenalties_frame rewardedOk]
      exact justifiedSame.1
    have kept : EffectiveKept c reset := by
      intro j inside
      simpa only [effectiveAt, (balanceDrift_reset resetOk).1,
        balanceDrift_slashings slashedOk, same] using
        effectiveKept_registry registeredOk j (by simpa [same] using inside)
    refine ⟨justified, rewarded, reset, balanced, justifiedOk,
      fun altair' => absurd altair' altair, fun _ => rewardedOk, by omega, kept, balancedOk,
      final, ?_⟩
    have grows := Nat.le_trans (frame_processRewardsAndPenalties rewardedOk).registryGrows <|
      Nat.le_trans (frame_processRegistryUpdates registeredOk).registryGrows <|
      Nat.le_trans (frame_processSlashings slashedOk).registryGrows
        (frame_processEth1DataReset resetOk).registryGrows
    rw [justifiedSame.1] at grows
    exact grows

/-- Take a validator active in an epoch and not slashed after it.

A slot that ends that epoch lowers its effective balance by at most an allowed fall.

This fall is the one allowed below its balance after the rewards. -/
private theorem crossing_fall {z z' : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks z = .ok z') (early : z'.fork < .glamsterdam)
    (next : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch z.state).toNat + 1)
    (bands : preset.IncrementWithinUpwardBand)
    (holds : PendingConsolidationInvariant config z.state) (matched : BalancesMatch z.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} {old : Validator} (found : z.state.validators.data[i]? = some old)
    (active : isActiveAt z.state (getCurrentEpoch z.state) i = true)
    (capped : old.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset z.fork old)
    (unslashed : ∀ w, z'.state.validators.data[i]? = some w → w.slashed = false) :
    ∃ cached justified rewarded : BeaconState preset z.fork,
      processSlot z.state = .ok cached ∧
      processJustificationAndFinalization cached = .ok justified ∧
      (∀ altair : .altair ≤ z.fork, ∃ scored,
        processInactivityUpdates config justified altair = .ok scored ∧
        processRewardsAndPenalties config scored = .ok rewarded) ∧
      (z.fork < .altair → processRewardsAndPenalties config justified = .ok rewarded) ∧
      old.effectiveBalance.toNat ≤ effectiveAt z' i +
        fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
          old.effectiveBalance.toNat (actualBalanceAt ⟨z.fork, rewarded⟩ i) := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have forkEarly : z.fork < .glamsterdam := by
    have := processUpgrades_fork_le upgraded
    exact Nat.lt_of_le_of_lt this early
  have advancedCopy := advancedOk
  obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advancedOk
  have slotAfter : z'.state.slot = nextSlot := processUpgrades_slot upgraded
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  swap
  · rename_i inside
    have same := nextSlot_epoch_of_inside sum inside
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotAfter] at next
    omega
  -- The slot runs the epoch transition.
  have cachedHolds : PendingConsolidationInvariant config cached := by
    subst cachedEq; exact holds
  have cachedMatch : BalancesMatch cached := by
    subst cachedEq; exact matched
  have cachedFound : cached.validators.data[i]? = some old := by
    subst cachedEq; exact found
  have cachedActive : isActiveAt cached (getCurrentEpoch cached) i = true := by
    subst cachedEq; exact active
  have cachedBalance : ∀ j, actualBalanceAt ⟨z.fork, cached⟩ j = actualBalanceAt z j := by
    subst cachedEq; intro j; rfl
  -- The validator is not slashed right after the transition, since the upgrades keep the flag.
  have persists : SlashedPersistence ({ epoched with slot := nextSlot } : BeaconState preset _)
      z'.state :=
    processUpgrades_induction
      (property := fun w => SlashedPersistence ({ epoched with slot := nextSlot } :
        BeaconState preset z.fork) w.state)
      (fun held stepOk => held.trans (.of_upgradeFrame (upgradeFrame_upgradeNext stepOk)))
      (.refl _) upgraded
  have epochClear : ∀ w, epoched.validators.data[i]? = some w → w.slashed = false := by
    intro w read
    cases flag : w.slashed
    · rfl
    · obtain ⟨w', read', marked⟩ := persists i w read flag
      rw [unslashed w' read'] at marked
      cases marked
  obtain ⟨justified, rewarded, before, after, justifiedOk, altairRewards, phase0Rewards, rises,
    kept, updated, validators, grows⟩ :=
    epoch_parts forkEarly epochedOk cachedHolds cachedMatch delay cachedActive epochClear
  refine ⟨cached, justified, rewarded, cachedOk, justifiedOk, altairRewards, phase0Rewards, ?_⟩
  -- The validator before the update has the old effective balance.
  have inside := (Array.getElem?_eq_some_iff.mp cachedFound).1
  have keptEffective := kept i inside
  obtain ⟨beforeValidator, beforeFound⟩ : ∃ w, before.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside grows)⟩
  have sameEffective : beforeValidator.effectiveBalance = old.effectiveBalance := by
    simp only [effectiveAt, beforeFound, cachedFound, Option.map_some, Option.getD_some]
      at keptEffective
    exact UInt64.toNat_inj.mp keptEffective
  -- The largest effective balance after the transition bounds the old effective balance.
  obtain ⟨w, wFound, monotone⟩ := processEpoch_validatorCap_mono forkEarly epochedOk i old
    cachedFound
  have capAfter : ∀ u, after.validators.data[i]? = some u →
      beforeValidator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset z.fork u := by
    intro u read
    rw [← validators, wFound, Option.some.injEq] at read
    subst u
    rw [sameEffective]
    exact UInt64.le_trans capped monotone
  have fall := effectiveUpdates_fall bands updated beforeFound capAfter
  rw [sameEffective] at fall
  have anti := fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand
    old.effectiveBalance.toNat rises
  -- The upgrades keep the effective balance of a validator that was activated.
  obtain ⟨a, aRead, life⟩ := (registryLifecycle_advanceSlot advancedCopy).validators i old found
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
  have endSame : effectiveAt ⟨z.fork, after⟩ i =
      effectiveAt ⟨z.fork, ({ epoched with slot := nextSlot } : BeaconState preset z.fork)⟩ i := by
    simp only [effectiveAt, validators]
  rw [upgradedSame, ← endSame]
  omega

/-- Take a run that ends one epoch after it starts.

It stays in its first epoch up to one slot, and in the next epoch after that slot. -/
private theorem run_split_next {x y : ForkedBeaconState preset} (run : Run config checks x y)
    (next : (getCurrentEpoch y.state).toNat = (getCurrentEpoch x.state).toNat + 1) :
    ∃ (z z' : ForkedBeaconState preset) (_ : Run config checks x z)
      (_ : advanceSlotAcross config checks z = .ok z') (_ : Run config checks z' y),
      getCurrentEpoch z.state = getCurrentEpoch x.state ∧
      getCurrentEpoch z'.state = getCurrentEpoch y.state := by
  induction run with
  | nil => omega
  | @snoc middle last pre step ih =>
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have high := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    by_cases crossed : (getCurrentEpoch middle.state).toNat = (getCurrentEpoch x.state).toNat + 1
    · obtain ⟨z, z', head, edge, tail, first, second⟩ := ih crossed
      refine ⟨z, z', head, edge, tail.snoc step, first, ?_⟩
      exact UInt64.toNat_inj.mp (by rw [second]; omega)
    · have same : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
        UInt64.toNat_inj.mp (by omega)
      cases step with
      | block engine signed due ok =>
        have slot := processBlock_slot (applySignedBlock_ok ok).2.1
        have epoch := congrArg (computeEpochAtSlot preset) slot
        change getCurrentEpoch _ = getCurrentEpoch _ at epoch
        simp only at next same
        rw [epoch] at next
        rw [same] at next
        omega
      | slot ok => exact ⟨middle, last, pre, ok, .nil, same, rfl⟩

/-! ## Before Altair, the pending attestations lie in their epochs -/

/-- Before Altair, each pending attestation of the two epochs targets the epoch of its list.

Its slot lies in that epoch. -/
private def PendingSlots {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ (before : f < .altair) (current : Bool), ∀ pending ∈ recentPending s before current,
    pending.data.target.epoch = (if current then getCurrentEpoch s else getPreviousEpoch s) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch

/-- A step that keeps the pending attestations and the slot keeps them in their epochs. -/
private theorem PendingSlots.of_pendingFrame {f : Fork} {s t : BeaconState preset f}
    (frame : PendingFrame s t) (holds : PendingSlots s) : PendingSlots t := by
  intro before current pending member
  have lists : recentPending t before current = recentPending s before current := by
    cases current <;> simp [recentPending, frame.previousPending, frame.currentPending]
  rw [lists] at member
  obtain ⟨epoch, slot⟩ := holds before current pending member
  have currentEq : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch t = getPreviousEpoch s := by
    unfold getPreviousEpoch
    rw [currentEq]
  exact ⟨by rw [currentEq, previousEq]; exact epoch, slot⟩

/-- Before Altair, an attestation records a pending attestation of its own epoch. -/
private theorem PendingSlots.of_processAttestation {f : Fork} {s t : BeaconState preset f}
    {parentSlot : Slot} {attestation : Attestation preset f} (before : f < .altair)
    (holds : PendingSlots s)
    (computed : processAttestation config checks s parentSlot attestation = .ok t) :
    PendingSlots t := by
  have frame := frame_processAttestation computed
  have currentEq : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch t = getPreviousEpoch s := by
    unfold getPreviousEpoch
    rw [currentEq]
  have kept : ∀ (current : Bool), ∀ pending ∈ recentPending s before current,
      pending.data.target.epoch = (if current then getCurrentEpoch t else getPreviousEpoch t) ∧
        computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch := by
    intro current pending member
    obtain ⟨epoch, slot⟩ := holds before current pending member
    exact ⟨by rw [currentEq, previousEq]; exact epoch, slot⟩
  obtain ⟨recent, slotEpoch, -⟩ := processAttestation_checks before computed
  obtain ⟨pending, -, dataEq, -, -, recorded, -⟩ := processAttestation_records before computed
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  intro before' current other member
  generalize chosen : (attestation.data.target.epoch == getCurrentEpoch s) = target
    at added same
  by_cases here : current = target
  · subst here
    rw [added] at member
    rcases Array.mem_push.mp member with old | rfl
    · exact kept _ other old
    rw [dataEq]
    refine ⟨?_, slotEpoch.symm⟩
    cases current
    · have differ : attestation.data.target.epoch ≠ getCurrentEpoch s :=
        ne_of_beq_false chosen
      simpa [previousEq] using recent.resolve_right differ
    · simpa [currentEq] using beq_iff_eq.mp chosen
  · have flipped : current = !target := by cases current <;> cases target <;> simp_all
    subst flipped
    rw [same] at member
    exact kept _ other member

/-- A block keeps the pending attestations in their epochs. -/
private theorem PendingSlots.of_processBlock {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f} (holds : PendingSlots s)
    (computed : processBlock config checks engine s block = .ok t) : PendingSlots t := by
  by_cases altair : .altair ≤ f
  · intro before
    exact absurd altair (Nat.not_le_of_lt before)
  have before := Nat.lt_of_not_le altair
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  have middle := foldlM_ok_invariant PendingSlots
    (fun _ _ _ prior ok => prior.of_processAttestation before ok) (holds.of_pendingFrame head)
    attested
  exact middle.of_pendingFrame tail

/-- One slot keeps the pending attestations in their epochs.

This also holds when the current ones become the previous ones at the end of an epoch. -/
private theorem PendingSlots.of_advanceSlot {f : Fork} {s t : BeaconState preset f}
    (holds : PendingSlots s) (computed : advanceSlot config checks s = .ok t) :
    PendingSlots t := by
  by_cases altair : .altair ≤ f
  · intro before
    exact absurd altair (Nat.not_le_of_lt before)
  have before := Nat.lt_of_not_le altair
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedLists : ∀ current, recentPending cached before current =
      recentPending s before current := by
    intro current
    cases current <;> simp [recentPending, cachedEq]
  have stateEpoch := getCurrentEpoch_toNat s
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro before' current pending member
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch s := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation before epochedOk
    cases current
    · have moved : recentPending { epoched with slot := next } before false =
          recentPending s before true := by
        rw [← cachedLists true]
        simp [recentPending, rotated]
      rw [moved] at member
      obtain ⟨epoch, slot⟩ := holds before true pending member
      simp only [↓reduceIte] at epoch
      exact ⟨by simp only [Bool.false_eq_true, ↓reduceIte, previousEq]; exact epoch, slot⟩
    · simp [recentPending, emptied] at member
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch s := by
      apply UInt64.toNat_inj.mp
      rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch s := by
      unfold getPreviousEpoch
      rw [currentEq]
    have lists : recentPending { cached with slot := next } before current =
        recentPending s before current := cachedLists current
    rw [lists] at member
    obtain ⟨epoch, slot⟩ := holds before current pending member
    exact ⟨by rw [currentEq, previousEq]; exact epoch, slot⟩

/-- Every state of a run from genesis keeps its pending attestations in their epochs. -/
private theorem run_pendingSlots {g x : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (run : Run config checks g x) :
    PendingSlots x.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, computed⟩ := genesis
    intro before current pending member
    rw [initializeBeaconStateFromEth1_pending computed before current] at member
    simp at member
  | snoc pre step ih =>
    cases step with
    | slot computed =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
      have advancedHolds : PendingSlots (⟨_, advanced⟩ : ForkedBeaconState preset).state :=
        ih.of_advanceSlot advancedOk
      exact processUpgrades_induction (property := fun w => PendingSlots w.state)
        (fun _ stepOk before => absurd (upgradeNext_altair stepOk).1 (Nat.not_le_of_lt before))
        advancedHolds upgraded
    | block engine signed due applied =>
      exact ih.of_processBlock (applySignedBlock_ok applied).2.1

/-- Before Altair, the attestations that match the source of the previous epoch lie in it. -/
private theorem PendingSlots.matchingSource_slot {f : Fork} {s : BeaconState preset f}
    (holds : PendingSlots s) (before : f < .altair)
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingSourceAttestations s before (getPreviousEpoch s) = .ok attestations) :
    ∀ pending ∈ attestations,
      computeEpochAtSlot preset pending.data.slot = getPreviousEpoch s := by
  intro pending member
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at matching
  obtain ⟨_, _, rfl⟩ := matching
  by_cases here : getPreviousEpoch s = getCurrentEpoch s
  · simp only [here, ↓reduceIte] at member
    obtain ⟨epoch, slot⟩ := holds before true pending member
    simp only [↓reduceIte] at epoch
    rw [slot, epoch, here]
  · simp only [here, ↓reduceIte] at member
    obtain ⟨epoch, slot⟩ := holds before false pending member
    simp only [Bool.false_eq_true, ↓reduceIte] at epoch
    rw [slot, epoch]

/-- Justification keeps the pending attestations in their epochs. -/
private theorem PendingSlots.of_justification {f : Fork} {s t : BeaconState preset f}
    (holds : PendingSlots s) (ok : processJustificationAndFinalization s = .ok t) :
    PendingSlots t := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact holds
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    have lists : ∀ before current, recentPending t before current =
        recentPending s before current := by
      intro before current
      cases current <;> simp only [recentPending] <;> rw [← rest]
    have slot : t.slot = s.slot := by rw [← rest]
    intro before current pending member
    rw [lists] at member
    have currentEq : getCurrentEpoch t = getCurrentEpoch s := by
      simp only [getCurrentEpoch, slot]
    have previousEq : getPreviousEpoch t = getPreviousEpoch s := by
      unfold getPreviousEpoch
      rw [currentEq]
    obtain ⟨epoch, slotIn⟩ := holds before current pending member
    exact ⟨by rw [currentEq, previousEq]; exact epoch, slotIn⟩

/-! ## The floor of a balance under the withdrawals of a payload -/

/-- From Electra, take the queued partial withdrawals that pay a validator.

They leave it at least the activation balance.

They pay only from an effective balance of at least that balance. -/
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
        have above := UInt64.lt_iff_toNat_lt.mp eligible.2
        have amountLe :
            partials[j].amount.toNat ≤ left.toNat - preset.MIN_ACTIVATION_BALANCE.toNat := by
          rw [amount, Base.Uint64.toNat_min,
            UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt eligible.2)]
          exact Nat.min_le_left _ _
        right
        exact ⟨by omega, eligible.1.2⟩
      · simpa using prior
  rcases prefixes partials.size (Nat.le_refl _) with zero | holds
  · rw [Array.extract_eq_self_of_le (Nat.le_refl _)] at zero
    omega
  · rw [Array.extract_eq_self_of_le (Nat.le_refl _)] at holds
    exact holds

/-- Take a validator that cannot withdraw in full.

Before Gloas, the withdrawals of a payload leave it at least a floor.

The floor is the smaller of its balance and its effective balance, less a queued amount.

That amount is what the queued partial withdrawals pay it, up to a cap.

The cap is its effective balance above the activation balance. -/
private theorem withdrawals_floor {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (early : f < .glamsterdam) (computed : processWithdrawals s capella payload = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch) :
    ∃ q : ℕ, min (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat ≤
        actualBalanceAt ⟨f, t⟩ v.toNat +
          min q (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) ∧
      (∀ electra : .pectra ≤ f, ∃ (partials : Array Withdrawal) (next : WithdrawalIndex)
        (count : ℕ), getPendingPartialWithdrawals s electra
          (s.nextWithdrawalIndex capella) #[] = .ok (partials, next, count) ∧
          q = withdrawnFrom partials v) ∧
      (f < .pectra → q = 0) := by
  obtain ⟨expected, expectedOk, -, -⟩ := processWithdrawals_expected early computed
  obtain ⟨builders, partials, buildersSweep, sweep, index1, index2, index3, index4, count1,
    count2, count3, count4, split, -, -, buildersEmpty, partialsOk, partialsEmpty, -,
    buildersSweepEmpty, sweepOk⟩ := getExpectedWithdrawals_parts expectedOk
  obtain ⟨rfl, rfl⟩ := buildersEmpty early
  obtain ⟨rfl, rfl⟩ := buildersSweepEmpty early
  refine ⟨withdrawnFrom partials v, ?_, fun electra => ⟨_, _, _, partialsOk electra, rfl⟩,
    fun before => by obtain ⟨rfl, -⟩ := partialsEmpty before; simp [withdrawnFrom]⟩
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
      obtain ⟨pays, distinct⟩ := getValidatorsSweepWithdrawals_sweepPays
        (s.validators.bound early) sweepOk
      obtain ⟨validator, balance', left, validatorOk, read', -, kind⟩ :=
        withdrawnFrom_of_sweepPays pays distinct inside
      rw [named] at validatorOk read' kind
      rw [getValidator_eq_ok_iff, found, Option.some.injEq] at validatorOk
      subst validator
      rw [read, Option.some.injEq] at read'
      subst balance'
      simp only [Array.empty_append, Array.append_empty, withdrawnFrom_append] at kind
      rcases kind with ⟨full, -⟩ | ⟨-, excess, total, below⟩
      · simp only [isFullyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq] at full
        exact absurd full.1.2 (UInt64.not_le.mpr later)
      · simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at excess
        rw [total, ← excess.1.2]
        omega
    · -- Otherwise only the queued partial withdrawals pay it.
      have zero : withdrawnFrom sweep v = 0 := withdrawnFrom_eq_zero fun w member same => by
        obtain ⟨k, inside, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
        exact swept ⟨k, inside, same⟩
      rw [zero] at bounded ⊢
      by_cases positive : 0 < withdrawnFrom partials v
      · by_cases electra : .pectra ≤ f
        · have partialsRead := partialsOk electra
          obtain ⟨floor, effective⟩ := partials_floor partialsRead found read positive
          have := UInt64.le_iff_toNat_le.mp effective
          omega
        · obtain ⟨rfl, -⟩ := partialsEmpty (Nat.lt_of_not_le electra)
          simp [withdrawnFrom] at positive
      · omega

/-- Before Gloas, the execution part of a block keeps the floor of the withdrawals.

Its queued partial withdrawals are those that the state computes from Electra. -/
private theorem execution_floor {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {body : BeaconBlockBody preset f}
    {bellatrix : .bellatrix ≤ f} (early : f < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch) :
    ∃ q : ℕ, min (actualBalanceAt ⟨f, s⟩ v.toNat) val.effectiveBalance.toNat ≤
        actualBalanceAt ⟨f, t⟩ v.toNat +
          min q (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) ∧
      (∀ electra : .pectra ≤ f, ∃ (partials : Array Withdrawal) (next : WithdrawalIndex)
        (count : ℕ), getPendingPartialWithdrawals s electra
          (s.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
            .ok (partials, next, count) ∧ q = withdrawnFrom partials v) ∧
      (f < .pectra → q = 0) := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at computed
  split at computed
  · rename_i capella
    simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    obtain ⟨q, floor, partials, zero⟩ := withdrawals_floor early withdrawnOk found later
    exact ⟨q, by simpa [actualBalanceAt] using floor, partials, zero⟩
  · rename_i capella
    have notElectra : f < .pectra :=
      Nat.lt_of_lt_of_le (Nat.lt_of_not_le capella) (by decide)
    refine ⟨0, ?_, fun electra => absurd electra (Nat.not_le_of_lt notElectra), fun _ => rfl⟩
    have same : t.balances = s.balances := by
      split at computed
      · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
        rfl
      · cases computed; rfl
    simp only [actualBalanceAt, same]
    omega

/-! ## The floor of a balance under a block -/

/-- What the queued partial withdrawals of a block pay a validator.

They are read as `Step.queuePaid` reads them. -/
private def blockQueuePaid {fork : Fork} (before : BeaconState preset fork)
    (block : BeaconBlock preset fork) (v : ValidatorIndex) : ℕ :=
  if electra : .pectra ≤ fork ∧ fork < .glamsterdam then
    ((do
      let headed ← processBlockHeader before block
      let (partials, _) ← getPendingPartialWithdrawals headed electra.1
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra.1)) #[]
      pure ((partials.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum :
      Except TransitionError ℕ).toOption).getD 0
  else 0

/-- The queued payments of a block step are those of its block. -/
private theorem queuePaid_block {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, before⟩ = false}
    {ok : applySignedBlock config checks engine before signed true = .ok after}
    (v : ValidatorIndex) :
    (Step.block engine signed due ok).queuePaid v = blockQueuePaid before signed.message v := rfl

/-- The queued payments of a block are the withdrawals that the header leaves to compute. -/
private theorem blockQueuePaid_eq {fork : Fork} {s headed : BeaconState preset fork}
    {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    (headedOk : processBlockHeader s block = .ok headed) {v : ValidatorIndex} {q : ℕ}
    (partials : ∀ electra : .pectra ≤ fork, ∃ (partials : Array Withdrawal)
      (next : WithdrawalIndex) (count : ℕ), getPendingPartialWithdrawals headed electra
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
          .ok (partials, next, count) ∧ q = withdrawnFrom partials v)
    (zero : fork < .pectra → q = 0) : blockQueuePaid s block v = q := by
  unfold blockQueuePaid
  by_cases electra : .pectra ≤ fork
  · obtain ⟨found, next, count, foundOk, rfl⟩ := partials electra
    simp only [electra, early, and_self, dite_true, headedOk, foundOk, bind, Except.bind, pure,
      Except.pure, Except.toOption, Option.getD_some, withdrawnFrom]
  · simp only [electra, false_and, dite_false]
    exact (zero (Nat.lt_of_not_le electra)).symm

/-- Take a validator that cannot withdraw in full and stays unslashed.

Its effective balance is within its largest.

Before Gloas, a block leaves it at least a floor.

The floor is the smaller of its balance and its effective balance, less two amounts.

The first is its sync amount.

The second is what the queued partial withdrawals pay it, up to a cap.

The cap is its effective balance above the activation balance. -/
private theorem block_floor {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (computed : processBlock config checks engine s block = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch)
    (capped : val.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork val)
    (unslashed : ∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) :
    ∃ sync : ℕ, min (actualBalanceAt ⟨fork, s⟩ v.toNat) val.effectiveBalance.toNat ≤
        actualBalanceAt ⟨fork, t⟩ v.toNat + sync + min (blockQueuePaid s block v)
          (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) ∧
      (∀ altair : .altair ≤ fork, ∃ reward : Gwei, syncParticipantReward s = .ok reward ∧
        sync ≤ seatsOf t altair v * reward.toNat) ∧
      (fork < .altair → sync = 0) := by
  -- The operations keep the floor, given the converted validators and the slashed ones.
  have operationsFloor {voted operated : BeaconState preset fork}
      {proposer : ValidatorIndex} {credit : ℕ}
      {slashed deposited conv : Finset ValidatorIndex} {other slash : ValidatorIndex → ℕ}
      (ops : Credited voted operated proposer credit slashed deposited conv other slash)
      (convCount : conv.card ≤ if .pectra ≤ fork then
        preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)
      (toVoted : ∀ validator, s.validators.data[v.toNat]? = some validator →
        ∃ later, voted.validators.data[v.toNat]? = some later ∧
          hasCompoundingWithdrawalCredential later =
            hasCompoundingWithdrawalCredential validator)
      (clear : ∀ w, operated.validators.data[v.toNat]? = some w → w.slashed = false) :
      min (actualBalanceAt ⟨fork, voted⟩ v.toNat) val.effectiveBalance.toNat ≤
        actualBalanceAt ⟨fork, operated⟩ v.toNat := by
    have noSlash : slash v = 0 := by
      have bound := ops.penalized v
      split at bound
      · rename_i member
        obtain ⟨w, wFound, marked⟩ := (ops.newly v member).2
        rw [clear w wFound] at marked
        cases marked
      · omega
    by_cases converted : v ∈ conv
    · have lowered := ops.ledger.lowered v converted (Finset.notMem_empty v)
      obtain ⟨laterValidator, laterFound, same⟩ := toVoted val found
      have fresh := ops.ledger.fresh v converted laterValidator laterFound
      rw [same] at fresh
      have electra : .pectra ≤ fork := by
        by_contra notElectra
        simp only [notElectra, ↓reduceIte, Nat.le_zero, Finset.card_eq_zero] at convCount
        rw [convCount] at converted
        exact Finset.notMem_empty v converted
      have cap := UInt64.le_iff_toNat_le.mp capped
      simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance,
        fresh, Bool.false_eq_true] at cap
      simp only [Pi.zero_apply, noSlash] at lowered
      omega
    · have down := ops.ledger.down v (Finset.notMem_empty v) converted
      simp only [Pi.zero_apply, noSlash] at down
      omega
  unfold processBlock at computed
  split at computed
  · rename_i altair
    unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid0, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    have paidSame : paid0 = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid0
    have headedSame : headed.validators = s.validators ∧ headed.balances = s.balances ∧
        headed.slot = s.slot := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact ⟨rfl, rfl, rfl⟩
    have headedFound : headed.validators.data[v.toNat]? = some val := by
      rw [headedSame.1]; exact found
    have headedLater : getCurrentEpoch headed < val.withdrawableEpoch := by
      simpa only [getCurrentEpoch, headedSame.2.2] using later
    -- The execution part, with its withdrawals.
    obtain ⟨q, executedFloor, partials, zero, paid, executedLedger, executedSteady,
        executedFrame⟩ :
        ∃ q : ℕ, min (actualBalanceAt ⟨fork, headed⟩ v.toNat) val.effectiveBalance.toNat ≤
          actualBalanceAt ⟨fork, executed⟩ v.toNat +
            min q (val.effectiveBalance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) ∧
          (∀ electra : .pectra ≤ fork, ∃ (partials : Array Withdrawal) (next : WithdrawalIndex)
            (count : ℕ), getPendingPartialWithdrawals headed electra
              (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
                .ok (partials, next, count) ∧ q = withdrawnFrom partials v) ∧
          (fork < .pectra → q = 0) ∧ ∃ paid : Finset ValidatorIndex,
          Ledger headed executed paid ∅ 0 0 0 ∧ Steady headed executed ∧
            Frame headed executed := by
      split at executedOk
      · obtain ⟨q, floor, partials, zero⟩ := execution_floor early executedOk headedFound
          headedLater
        obtain ⟨paid, ledger, -⟩ := ledger_processBlockExecution early executedOk
        exact ⟨q, floor, partials, zero, paid, ledger,
          steady_processBlockExecution early executedOk,
          (frame_processBlockExecution executedOk).toFrame⟩
      · rename_i bellatrix
        cases executedOk
        have notElectra : fork < .pectra :=
          Nat.lt_of_lt_of_le (Nat.lt_of_not_le bellatrix) (by decide)
        refine ⟨0, by omega, fun electra => absurd electra (Nat.not_le_of_lt notElectra),
          fun _ => rfl, ∅, Ledger.refl _, ⟨StepKeeps.refl _, effectiveKept_refl _⟩, Frame.refl _⟩
    have queue : blockQueuePaid s block v = q := blockQueuePaid_eq early headedOk partials zero
    obtain ⟨votedLedger, votedSteady, votedFrame⟩ :
        Ledger revealed voted ∅ ∅ 0 0 0 ∧ Steady revealed voted ∧ Frame revealed voted := by
      split at votedOk
      · exact ⟨ledger_processEth1Data votedOk, steady_processEth1Data votedOk,
          (frame_processEth1Data votedOk).toFrame⟩
      · cases votedOk
        exact ⟨Ledger.refl _, ⟨StepKeeps.refl _, effectiveKept_refl _⟩, Frame.refl _⟩
    have toVoted : Ledger s voted paid ∅ 0 0 0 :=
      (ledger_processBlockHeader headedOk).zero_left
        ((executedLedger.zero_right (ledger_processRandao revealedOk)).zero_right votedLedger)
    have steadyVoted : Steady s voted :=
      (steady_processBlockHeader headedOk).trans <| executedSteady.trans <|
        (steady_processRandao revealedOk).trans votedSteady
    have frameVoted : Frame s voted :=
      (frame_processBlockHeader headedOk).toFrame.trans <| executedFrame.trans <|
        (frame_processRandao revealedOk).toFrame.trans votedFrame
    have executedVoted : actualBalanceAt ⟨fork, voted⟩ v.toNat =
        actualBalanceAt ⟨fork, executed⟩ v.toNat := by
      have one := (ledger_processRandao revealedOk).up v
      have two := (ledger_processRandao revealedOk).down v (Finset.notMem_empty v)
        (Finset.notMem_empty v)
      have three := votedLedger.up v
      have four := votedLedger.down v (Finset.notMem_empty v) (Finset.notMem_empty v)
      simp only [Pi.zero_apply, add_zero] at one two three four
      omega
    obtain ⟨proposer, credit, slashed, deposited, conv, other, slash, ops, convCount⟩ :=
      credited_processOperations early (frameVoted.balancesMatch matched) operatedOk
    obtain ⟨proposer', reward, share, sync, rewardOk, -, -, seats, syncLedger⟩ :=
      ledger_processSyncAggregate synced
    have syncKept := kept_processSyncAggregate synced
    have total : getTotalActiveBalance operated = getTotalActiveBalance s :=
      (steadyVoted.trans ops.kept.steady).total
    have operatedClear : ∀ w, operated.validators.data[v.toNat]? = some w → w.slashed = false := by
      intro w wFound
      have inside : v.toNat < t.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp wFound).1 syncKept.frame.registryGrows
      cases flag : w.slashed
      · rfl
      · have := syncKept.frame.slashed v.toNat w _ wFound (Array.getElem?_eq_getElem inside) flag
        rw [unslashed _ (Array.getElem?_eq_getElem inside)] at this
        cases this
    have middle := operationsFloor ops convCount
      (fun validator read => toVoted.kept v validator (Finset.notMem_empty v) read) operatedClear
    have syncUp := syncLedger.down v (Finset.notMem_empty v) (Finset.notMem_empty v)
    simp only [Pi.zero_apply, add_zero] at syncUp
    refine ⟨sync v, ?_,
      fun _ => ⟨reward, by rw [← syncParticipantReward_congr total]; exact rewardOk, seats v⟩,
      fun before => absurd altair (Nat.not_le_of_lt before)⟩
    rw [queue]
    have headedBalance : actualBalanceAt ⟨fork, headed⟩ v.toNat =
        actualBalanceAt ⟨fork, s⟩ v.toNat := by
      simp only [actualBalanceAt, headedSame.2.1]
    omega
  · rename_i altair
    simp only [bind_ok_iff] at computed
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := computed
    have notElectra : fork < .pectra := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
    have toVoted : Ledger s voted ∅ ∅ 0 0 0 :=
      (ledger_processBlockHeader headedOk).zero_left
        ((ledger_processRandao revealedOk).zero_right (ledger_processEth1Data votedOk))
    have frameVoted : Frame s voted :=
      (frame_processBlockHeader headedOk).toFrame.trans <|
        (frame_processRandao revealedOk).toFrame.trans (frame_processEth1Data votedOk).toFrame
    obtain ⟨proposer, credit, slashed, deposited, conv, other, slash, ops, convCount⟩ :=
      credited_processOperations early (frameVoted.balancesMatch matched) operatedOk
    have middle := operationsFloor ops convCount
      (fun validator read => toVoted.kept v validator (Finset.notMem_empty v) read) unslashed
    have queue : blockQueuePaid s block v = 0 := by
      unfold blockQueuePaid
      split
      · rename_i electra
        exact absurd electra.1 (Nat.not_le_of_lt notElectra)
      · rfl
    have one := toVoted.up v
    have two := toVoted.down v (Finset.notMem_empty v) (Finset.notMem_empty v)
    simp only [Pi.zero_apply, add_zero] at one two
    refine ⟨0, ?_, fun altair' => absurd altair' altair, fun _ => rfl⟩
    rw [queue]
    omega

/-! ## The floor of a balance over the blocks of one epoch -/

/-- A slot inside one epoch only caches the slot, and moves no balance. -/
private theorem slot_same_epoch {middle last : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks middle = .ok last)
    (same : getCurrentEpoch last.state = getCurrentEpoch middle.state) :
    ∃ (cached : BeaconState preset middle.fork) (next : Slot),
      processSlot middle.state = .ok cached ∧
        last = ⟨middle.fork, { cached with slot := next }⟩ := by
  obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
  have epoch : getCurrentEpoch next = getCurrentEpoch middle.state := by
    have slot : last.state.slot = next.slot := processUpgrades_induction
      (property := fun t => t.state.slot = next.slot)
      (fun prior ok => (upgradeFrame_upgradeNext ok).slot.trans prior) rfl upgraded
    have eq : getCurrentEpoch last.state = getCurrentEpoch next := by
      simp only [getCurrentEpoch, slot]
    exact eq.symm.trans same
  obtain ⟨slot, cached, epoched, sum, cachedOk, epochOk, rfl⟩ := advanceSlot_ok advanced
  have notFirst : slot % preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro firstSlot
    have rem : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat firstSlot
    have eq := congrArg UInt64.toNat epoch
    simp only [getCurrentEpoch_toNat] at eq
    have divide := Nat.mod_add_div slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have before := Nat.mod_add_div middle.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [eq] at divide
    omega
  rw [processUpgrades_of_not_due (upgradeDue_of_not_first notFirst)] at upgraded
  cases upgraded
  simp only [epochIfLast, ite_eq_right notFirst, pure, Except.pure, Except.ok.injEq] at epochOk
  subst epoched
  exact ⟨cached, slot, cachedOk, rfl⟩

/-- A run without blocks pays nothing from the queue. -/
private theorem queuePaid_eq_zero {x y : ForkedBeaconState preset} (run : Run config checks x y)
    (none : run.blockCount = 0) (v : ValidatorIndex) : run.queuePaid v = 0 := by
  induction run with
  | nil => rfl
  | snoc pre step ih =>
    cases step with
    | slot ok =>
      simp only [Run.blockCount] at none
      simp [Run.queuePaid, ih none, Step.queuePaid]
    | block engine signed due ok => simp [Run.blockCount] at none

/-- Take a run inside one epoch.

Each of its blocks keeps the floor with a sync amount at most `S`.

Then a balance falls below the smaller of its start and a reference by at most a sum.

The sum adds those sync amounts and the queued payments.

With one block, the queued payments count only up to the reference above the activation balance.
-/
private theorem run_floor {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    {v : ValidatorIndex} {EB S : ℕ}
    (unslashed : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false)
    (step : ∀ {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
      {block : BeaconBlock preset f}, Run config checks x ⟨f, s⟩ →
      getCurrentEpoch s = getCurrentEpoch x.state →
      processBlock config checks engine s block = .ok t →
      (∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) →
      ∃ sync : ℕ, min (actualBalanceAt ⟨f, s⟩ v.toNat) EB ≤ actualBalanceAt ⟨f, t⟩ v.toNat +
        sync + min (blockQueuePaid s block v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat) ∧
        sync ≤ S) :
    ∃ extra : ℕ, min (actualBalanceAt x v.toNat) EB ≤
        actualBalanceAt y v.toNat + tail.blockCount * S + extra ∧
      extra ≤ tail.queuePaid v ∧
      (tail.blockCount ≤ 1 →
        extra ≤ min (tail.queuePaid v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat)) := by
  induction tail with
  | nil => exact ⟨0, by simp [Run.blockCount], Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | @snoc middle last pre stepped ih =>
    have low := currentEpoch_le_of_chainSteps pre.chainSteps
    have high := stepped.chainStep.currentEpoch_le
    have midEpoch : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      UInt64.le_antisymm (same ▸ high) low
    have midClear : ∀ w, middle.state.validators.data[v.toNat]? = some w → w.slashed = false := by
      intro w read
      cases flag : w.slashed
      · rfl
      · obtain ⟨w', read', marked⟩ := stepped.slashedPersistence v.toNat w read flag
        rw [unslashed w' read'] at marked
        cases marked
    obtain ⟨extra, floor, paid, single⟩ := ih midEpoch midClear
    cases stepped with
    | slot ok =>
      obtain ⟨cached, next, cachedOk, rfl⟩ := slot_same_epoch ok (same.trans midEpoch.symm)
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      refine ⟨extra, ?_, ?_, ?_⟩
      · simpa [Run.blockCount, actualBalanceAt] using floor
      · simpa [Run.queuePaid, Step.queuePaid] using paid
      · intro count
        simpa [Run.queuePaid, Step.queuePaid] using single (by simpa [Run.blockCount] using count)
    | @block f before after engine signed due ok =>
      obtain ⟨sync, blockFloor, bounded⟩ := step pre midEpoch (applySignedBlock_ok ok).2.1 unslashed
      rw [← queuePaid_block (due := due) (ok := ok)] at blockFloor
      refine ⟨extra + min ((Step.block engine signed due ok).queuePaid v)
        (EB - preset.MIN_ACTIVATION_BALANCE.toNat), ?_, ?_, ?_⟩
      · simp only [Run.blockCount, Nat.add_mul, Nat.one_mul]
        have := Nat.mul_le_mul_right S (Nat.le_refl pre.blockCount)
        omega
      · simp only [Run.queuePaid]
        have := Nat.min_le_left ((Step.block engine signed due ok).queuePaid v)
          (EB - preset.MIN_ACTIVATION_BALANCE.toNat)
        omega
      · intro count
        simp only [Run.blockCount] at count
        have none : pre.blockCount = 0 := by omega
        have zero := queuePaid_eq_zero pre none v
        have extraZero : extra = 0 := by
          have := single (by omega)
          rw [zero] at this
          omega
        simp only [Run.queuePaid, zero, zero_add, extraZero]
        exact Nat.le_refl _

/-- A run inside one epoch keeps its fork.

No upgrade comes before the first slot of an epoch. -/
private theorem fork_eq_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    y.fork = x.fork := by
  induction tail with
  | nil => rfl
  | @snoc middle last pre step ih =>
    have low := currentEpoch_le_of_chainSteps pre.chainSteps
    have high := step.chainStep.currentEpoch_le
    have midEpoch : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      UInt64.le_antisymm (same ▸ high) low
    have prior := ih midEpoch
    cases step with
    | block engine signed due ok => exact prior
    | slot ok =>
      obtain ⟨cached, next, -, rfl⟩ := slot_same_epoch ok (same.trans midEpoch.symm)
      exact prior

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

Before Electra, they pay none. -/
private theorem blockQueuePaid_support {fork : Fork} (before : BeaconState preset fork)
    (block : BeaconBlock preset fork) :
    ∃ indices : Finset ValidatorIndex, indices.card ≤
        (if .pectra ≤ fork then preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat else 0) ∧
      ∀ v, blockQueuePaid before block v ≠ 0 → v ∈ indices := by
  by_cases electra : .pectra ≤ fork ∧ fork < .glamsterdam
  · cases headedOk : processBlockHeader before block with
    | error =>
      exact ⟨∅, by simp, fun v paid => by
        simp [blockQueuePaid, electra, headedOk, bind, Except.bind, Except.toOption] at paid⟩
    | ok headed =>
      cases partialsOk : getPendingPartialWithdrawals headed electra.1
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra.1)) #[] with
      | error =>
        exact ⟨∅, by simp, fun v paid => by
          simp [blockQueuePaid, electra, headedOk, partialsOk, bind, Except.bind,
            Except.toOption] at paid⟩
      | ok result =>
        obtain ⟨partials, next, count⟩ := result
        refine ⟨(partials.toList.map (·.validatorIndex)).toFinset, ?_, fun v paid => ?_⟩
        · simp only [electra.1, ↓reduceIte]
          refine (List.toFinset_card_le _).trans ?_
          simp only [List.length_map, Array.length_toList]
          exact partials_size_le partialsOk
        · simp only [blockQueuePaid, electra, and_self, dite_true, headedOk, partialsOk, bind,
            Except.bind, pure, Except.pure, Except.toOption, Option.getD_some] at paid
          obtain ⟨amount, inside, positive⟩ := List.exists_mem_ne_zero_of_sum_ne_zero paid
          obtain ⟨w, kept, rfl⟩ := List.mem_map.mp inside
          obtain ⟨present, named⟩ := List.mem_filter.mp kept
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨w, present, by simpa using named⟩)
  · exact ⟨∅, by simp, fun v paid => by simp [blockQueuePaid, electra] at paid⟩

/-- Take a run with at most one block.

It pays from the queue at most the validators that one sweep of partial withdrawals may pay.

Before Electra, it pays none from the queue. -/
private theorem owed_card {x y : ForkedBeaconState preset} (run : Run config checks x y)
    (single : run.blockCount ≤ 1) :
    ∃ owed : Finset ValidatorIndex, owed.card ≤
        (if .pectra ≤ y.fork then preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat else 0) ∧
      ∀ v, run.queuePaid v ≠ 0 → v ∈ owed := by
  induction run with
  | nil => exact ⟨∅, by simp, fun v paid => by simp [Run.queuePaid] at paid⟩
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨owed, card, covers⟩ := ih (by simpa [Run.blockCount] using single)
      refine ⟨owed, card.trans ?_, fun v paid => covers v (by
        simpa [Run.queuePaid, Step.queuePaid] using paid)⟩
      have grows : middle.fork ≤ last.fork := (Step.slot ok).chainStep.fork_le
      split
      · rename_i electra
        split
        · exact Nat.le_refl _
        · rename_i later
          exact absurd (Nat.le_trans electra grows) later
      · exact Nat.zero_le _
    | @block f before after engine signed due ok =>
      have none : pre.blockCount = 0 := by simp [Run.blockCount] at single; omega
      obtain ⟨indices, card, covers⟩ := blockQueuePaid_support before signed.message
      refine ⟨indices, card, fun v paid => covers v ?_⟩
      rw [← queuePaid_block (due := due) (ok := ok)]
      simpa [Run.queuePaid, queuePaid_eq_zero pre none v] using paid

/-- Before Electra, a run pays nothing from the queue. -/
private theorem queuePaid_eq_zero_of_lt {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (before : y.fork < .pectra) (v : ValidatorIndex) :
    run.queuePaid v = 0 := by
  induction run with
  | nil => rfl
  | @snoc middle last pre step ih =>
    have earlier := Nat.lt_of_le_of_lt step.chainStep.fork_le before
    cases step with
    | slot ok => simp [Run.queuePaid, ih earlier, Step.queuePaid]
    | block engine signed due ok =>
      simp only [Run.queuePaid, ih earlier, zero_add]
      simp only [Step.queuePaid]
      split
      · rename_i electra
        exact absurd electra.1 (Nat.not_le_of_lt before)
      · rfl

/-! ## What every reachable state keeps -/

/-- Every state of a run from genesis keeps the invariant of the transition. -/
private theorem run_invariant {g x : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (run : Run config checks g x) :
    Invariant x.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    exact (initializeBeaconStateFromEth1_invariant ok).2
  | snoc pre step ih =>
    cases step with
    | slot ok => exact (advanceSlotAcross_invariant ih ok).1
    | block engine signed due ok =>
      exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih

/-- Before Gloas, take every state of a run from genesis.

The sources of its pending consolidations exit with the withdrawal delay. -/
private theorem run_pendingConsolidations {g x : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (run : Run config checks g x)
    (early : x.fork < .glamsterdam) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    PendingConsolidationInvariant config x.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    have before := (initializeBeaconStateFromEth1_invariant ok).1
    intro electra
    exact False.elim (Nat.not_le_of_lt (Nat.lt_trans before (by decide)) electra)
  | snoc pre step ih =>
    exact PendingConsolidationInvariant.step step early
      (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)) delay

/-- Inside one epoch, the fork and the keys of the current sync committee stay.

The prefix of the validator keys also stays. -/
private theorem epoch_reads {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    y.fork = x.fork ∧ validatorKeys x.state <+: validatorKeys y.state ∧
      ∀ (altair : .altair ≤ y.fork) (altair' : .altair ≤ x.fork),
        (y.state.currentSyncCommittee altair).value.pubkeys.toList =
          (x.state.currentSyncCommittee altair').value.pubkeys.toList :=
  Run.induction_of_same_epoch
    (fun w => w.fork = x.fork ∧ validatorKeys x.state <+: validatorKeys w.state ∧
      ∀ (altair : .altair ≤ w.fork) (altair' : .altair ≤ x.fork),
        (w.state.currentSyncCommittee altair).value.pubkeys.toList =
          (x.state.currentSyncCommittee altair').value.pubkeys.toList)
    ⟨rfl, List.prefix_refl _, fun _ _ => rfl⟩
    (fun _ _ ok prior => ⟨prior.1, prior.2.1.trans (frame_processBlock ok).pubkeysPrefix,
      fun altair altair' => by
        rw [congrFun (SameSyncCommittees.processBlock ok).1 altair]
        exact prior.2.2 altair altair'⟩)
    (fun cachedOk prior => by
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      exact prior)
    tail early same

/-- The effective balances active in an epoch sum the same when three things stay.

These are activity in that epoch, the effective balances and the registry before. -/
private theorem activeSum_eq {f h : Fork} {a : BeaconState preset f} {b : BeaconState preset h}
    {e : Epoch} (active : ∀ i, isActiveAt b e i = isActiveAt a e i) (kept : EffectiveKept a b)
    (grows : a.validators.data.size ≤ b.validators.data.size) :
    ∑ i ∈ (Finset.range b.validators.data.size).filter (fun i => isActiveAt b e i = true),
        ((b.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
      ∑ i ∈ (Finset.range a.validators.data.size).filter (fun i => isActiveAt a e i = true),
        ((a.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
  rw [Finset.sum_filter, Finset.sum_filter]
  obtain ⟨extra, sizes⟩ : ∃ extra, b.validators.data.size = a.validators.data.size + extra :=
    ⟨_, (Nat.add_sub_of_le grows).symm⟩
  rw [sizes, Finset.sum_range_add]
  have tail : ∑ k ∈ Finset.range extra, (if isActiveAt b e (a.validators.data.size + k) = true then
      ((b.validators.data[a.validators.data.size + k]?).map (·.effectiveBalance.toNat)).getD 0
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [active]
    simp [isActiveAt]
  rw [tail, add_zero]
  refine Finset.sum_congr rfl fun i member => ?_
  rw [active, show ((b.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
    effectiveAt ⟨h, b⟩ i from rfl, kept i (Finset.mem_range.mp member)]
  rfl

/-- A prefix of the validator keys keeps the key at each old position. -/
private theorem pubkey_of_prefix {f h : Fork} {a : BeaconState preset f}
    {b : BeaconState preset h} (pre : validatorKeys a <+: validatorKeys b) {i : ℕ}
    (inside : i < a.validators.data.size) :
    (b.validators.data[i]?).map (·.pubkey) = (a.validators.data[i]?).map (·.pubkey) := by
  obtain ⟨rest, keys⟩ := pre
  have read : ∀ {g : Fork} (c : BeaconState preset g),
      (c.validators.data[i]?).map (·.pubkey) = (validatorKeys c)[i]? := by
    intro g c
    simp [validatorKeys]
  rw [read, read, ← keys, List.getElem?_append_left (by simpa [validatorKeys] using inside)]

/-- Take two states with the same keys of the current sync committee.

They also hold the same key at the position of a validator.

Then the seats of that validator read the same from both states. -/
private theorem seats_eq {f h : Fork} {a : BeaconState preset f} {b : BeaconState preset h}
    (altairA : .altair ≤ f) (altairB : .altair ≤ h) {i : ℕ}
    (keys : (a.currentSyncCommittee altairA).value.pubkeys.toList =
      (b.currentSyncCommittee altairB).value.pubkeys.toList)
    (pub : (a.validators.data[i]?).map (·.pubkey) = (b.validators.data[i]?).map (·.pubkey)) :
    ((a.currentSyncCommittee altairA).value.pubkeys.toList.filter fun key =>
        (a.validators.data[i]?).any (·.pubkey == key)).length =
      ((b.currentSyncCommittee altairB).value.pubkeys.toList.filter fun key =>
        (b.validators.data[i]?).any (·.pubkey == key)).length := by
  have any : ∀ (o : Option Validator) (key : Cryptography.Bls.BLSPubkey),
      o.any (·.pubkey == key) = (o.map (·.pubkey)).any (· == key) := by
    intro o key
    cases o <;> rfl
  rw [keys]
  congr 1
  refine List.filter_congr fun key _ => ?_
  rw [any, any, pub]

/-- A successful sync participant reward is the formula of some effective balances.

These are the effective balances active in the current epoch. -/
private theorem syncReward_value {f : Fork} {s : BeaconState preset f} {reward : Gwei}
    (computed : syncParticipantReward s = .ok reward) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let total := max inc (∑ i ∈ (Finset.range s.validators.data.size).filter
      (fun i => isActiveAt s (getCurrentEpoch s) i = true),
        ((s.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
    reward.toNat = total / inc * (inc * preset.BASE_REWARD_FACTOR.toNat /
      (integerSquareroot (UInt64.ofNat total)).toNat) * SYNC_REWARD_WEIGHT.toNat /
        WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
          preset.SYNC_COMMITTEE_SIZE.toNat := by
  intro inc total
  obtain ⟨read, _, readOk, _⟩ := syncParticipantReward_ok computed
  rw [syncParticipantReward_toNat readOk computed, getTotalActiveBalance_toNat readOk]

/-! ## Piece 14: the fall of a voter (G4‴) -/

/-- The fall of the effective balance of a voter that is never slashed, over the end of an epoch.

This is the loss bound (fall′) of the fast confirmation rule.

It is read by `quorumDrift_le_quorumReserve`.

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

That amount is how far the boundary block's queued payments took it below its effective balance.

Those queued amounts add up to at most what one block can pay below the largest effective balance.

The increment must fit in the upward band (`bands`), so no upward update lowers effective balances.
-/
theorem effectiveFall_le {g R T P y : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (history : Run config checks g R)
    (boundary : Run config checks R T) (tailP : Run config checks T P)
    (tailS : Run config checks T y) (caps : CapOrder preset)
    (bands : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (hysteresis : Hysteresis R.state) (early : y.fork < .glamsterdam)
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
  have delayPos : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := withdrawDelay
  -- The branch of `y` leaves the epoch at one slot.
  have nextT : (getCurrentEpoch y.state).toNat = (getCurrentEpoch T.state).toNat + 1 := by
    rw [boundaryEpoch]; exact next
  obtain ⟨z, z', toZ, edge, fromZ', zEpoch, z'Epoch⟩ := run_split_next tailS nextT
  -- The forks inside the epoch.
  have Tearly : T.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tailS.chainSteps) early
  have RT : T.fork = R.fork := fork_eq_of_same_epoch boundary boundaryEpoch
  have PT : P.fork = T.fork := fork_eq_of_same_epoch tailP (callEpoch.trans boundaryEpoch.symm)
  have ZT : z.fork = T.fork := fork_eq_of_same_epoch toZ zEpoch
  have Rearly : R.fork < .glamsterdam := RT ▸ Tearly
  have Pearly : P.fork < .glamsterdam := PT ▸ Tearly
  have Zearly : z.fork < .glamsterdam := ZT ▸ Tearly
  have z'Early : z'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps fromZ'.chainSteps) early
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
    fun run wEarly same => ⟨epoch_reads run wEarly same,
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
  refine ⟨fun v => min (boundary.queuePaid v)
    (effective v.toNat - preset.MIN_ACTIVATION_BALANCE.toNat), owed, ?_, ?_, ?_⟩
  · intro v absent
    have zero : boundary.queuePaid v = 0 := by
      by_contra paid
      exact absent (covers v paid)
    simp [zero]
  · by_cases electra : .pectra ≤ P.fork
    · have each : ∀ v ∈ owed, min (boundary.queuePaid v)
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
            simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance]
            split
            · exact UInt64.le_refl _
            · exact caps.compounding
          have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans capped top)
          simpa [effective, balanceAt, state, read] using this
      have cardBound : owed.card ≤ preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat := by
        have electraT : .pectra ≤ T.fork := PT ▸ electra
        simpa [electraT] using owedCard
      calc _ ≤ ∑ v ∈ owed, (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
            preset.MIN_ACTIVATION_BALANCE.toNat) := Finset.sum_le_sum each
        _ = owed.card * (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
            preset.MIN_ACTIVATION_BALANCE.toNat) := by simp
        _ ≤ maskCap := by
          simp only [maskCap, electra, ↓reduceIte]
          exact Nat.mul_le_mul_right _ cardBound
    · have electraT : ¬ .pectra ≤ T.fork := PT ▸ electra
      have empty : owed = ∅ := by
        simpa [electraT] using owedCard
      simp [empty]
  · intro v activeV clearY
    -- The validator is not slashed at `y`, so at no state before it.
    have clearAtY : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false := by
      intro w read
      simpa [read] using clearY
    have clearBack : ∀ {a b : ForkedBeaconState preset} (run : Run config checks a b),
        (∀ w, b.state.validators.data[v.toNat]? = some w → w.slashed = false) →
        ∀ w, a.state.validators.data[v.toNat]? = some w → w.slashed = false := by
      intro a b run clear w read
      cases flag : w.slashed
      · rfl
      · obtain ⟨w', read', marked⟩ := run.slashedPersistence v.toNat w read flag
        rw [clear w' read'] at marked
        cases marked
    have clearZ' := clearBack fromZ' clearAtY
    have clearZ := clearBack ((Run.nil.snoc (.slot edge)).append fromZ') clearAtY
    have clearT := clearBack tailS clearAtY
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
    have invR := run_invariant genesis history
    obtain ⟨balR, readR⟩ : ∃ b, R.state.balances.data[v.toNat]? = some b :=
      ⟨_, Array.getElem?_eq_getElem (by rw [invR.balancesMatch]; exact insideR)⟩
    have hysR := hysteresis.down v.toNat valR balR foundR readR
    have actualR : actualBalanceAt R v.toNat = balR.toNat := by
      simp [actualBalanceAt, readR]
    rw [hEB] at hysR
    -- The sync amount of the validator, read at `P`, bounds that of each block of the epoch.
    have totalR : total = max inc (∑ i ∈ (Finset.range R.state.validators.data.size).filter
        (fun i => isActiveAt R.state (getCurrentEpoch R.state) i = true),
        ((R.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) := by
      simp only [total, sumP]
    have syncBound : ∀ {f : Fork} {s t : BeaconState preset f} (toS : Run config checks R ⟨f, s⟩),
        getCurrentEpoch s = getCurrentEpoch R.state → f < .glamsterdam →
        validatorKeys s <+: validatorKeys t →
        (∀ altair : .altair ≤ f, t.currentSyncCommittee altair = s.currentSyncCommittee altair) →
        ∀ (altair : .altair ≤ f) (reward : Gwei), syncParticipantReward s = .ok reward →
          seatsOf t altair v * reward.toNat ≤ sync v.toNat := by
      intro f s t toS sEpoch fEarly prefixT committeeT altair reward rewardOk
      obtain ⟨⟨fEq, keysS, committeeS⟩, keptS, growsS, activeS⟩ := readsAt toS fEarly sEpoch
      have altairP : .altair ≤ P.fork := by rw [PT, RT]; exact fEq ▸ altair
      have seatsSame : seatsOf t altair v = seats v.toNat := by
        simp only [seats, altairP, dite_true, seatsOf]
        refine seats_eq altair altairP ?_ ?_
        · rw [committeeT altair, committeeS altair (fEq ▸ altair), committeeP altairP]
        · rw [pubkey_of_prefix (prefixT) (Nat.lt_of_lt_of_le insideR growsS),
            pubkey_of_prefix keysS insideR]
          exact (pubkey_of_prefix keysP insideR).symm
      have rewardSame : reward.toNat = seatReward := by
        rw [syncReward_value rewardOk]
        have sums := activeSum_eq activeS keptS growsS
        simp only [sEpoch] at sums ⊢
        simp only [seatReward, altairP, ↓reduceIte, perIncrement, root, totalR, inc, slots]
        rw [sums]
      rw [seatsSame, rewardSame]
    -- Each block of the epoch keeps the floor of the balance.
    have stepFloor : ∀ {X : ForkedBeaconState preset} (histX : Run config checks g X)
        (fromR : Run config checks R X), getCurrentEpoch X.state = getCurrentEpoch R.state →
        ∀ {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
          {block : BeaconBlock preset f}, Run config checks X ⟨f, s⟩ →
          getCurrentEpoch s = getCurrentEpoch X.state →
          processBlock config checks engine s block = .ok t →
          (∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) →
          ∃ sync' : ℕ, min (actualBalanceAt ⟨f, s⟩ v.toNat) EB ≤
            actualBalanceAt ⟨f, t⟩ v.toNat + sync' +
              min (blockQueuePaid s block v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat) ∧
            sync' ≤ sync v.toNat := by
      intro X histX fromR XEpoch f s t engine block pre sEpoch processed clearAfter
      have toS := fromR.append pre
      have sEpochR : getCurrentEpoch s = getCurrentEpoch R.state := sEpoch.trans XEpoch
      have fEq : f = R.fork := fork_eq_of_same_epoch toS sEpochR
      have fEarly : f < .glamsterdam := fEq ▸ Rearly
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
      have invS := run_invariant genesis (histX.append pre)
      have later : getCurrentEpoch s < valS.withdrawableEpoch := by
        have ordered := invS.exitsOrdered valS (Array.mem_of_getElem? foundS)
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActiveS
        rw [sEpochR]
        exact UInt64.lt_of_lt_of_le isActiveS.2 ordered
      have capS := (histX.append pre).effectiveBalance_capped genesis caps.activation
        caps.compounding fEarly valS (Array.mem_of_getElem? foundS)
      obtain ⟨sync', floor, rewardBound, phase0⟩ :=
        block_floor fEarly invS.balancesMatch processed foundS later capS clearAfter
      refine ⟨sync', by rw [← effS]; exact floor, ?_⟩
      by_cases altair : .altair ≤ f
      · obtain ⟨reward, rewardOk, bound⟩ := rewardBound altair
        exact bound.trans (syncBound toS sEpochR fEarly (frame_processBlock processed).pubkeysPrefix
          (fun altair => congrFun (SameSyncCommittees.processBlock processed).1 altair)
          altair reward rewardOk)
      · rw [phase0 (Nat.lt_of_not_le altair)]
        exact Nat.zero_le _
    -- The boundary run, with at most one block.
    obtain ⟨extraRT, floorRT, -, belowRT⟩ := run_floor boundary boundaryEpoch clearT
      (stepFloor history .nil rfl)
    have belowBound := belowRT single
    -- The blocks of the branch of `y` inside the epoch.
    have histT := history.append boundary
    obtain ⟨extraTZ, floorTZ, paidTZ, -⟩ := run_floor toZ zEpoch clearZ
      (stepFloor histT boundary boundaryEpoch)
    -- Those blocks pay at most the partial withdrawals queued at `T` and due by the epoch.
    have queueTZ : toZ.queuePaid v ≤ partials v.toNat := by
      by_cases electra : .pectra ≤ T.fork
      · have bound := DirectSafety.queuePaid_le_ancestorPartials toZ electra Zearly (ZT ▸ electra)
          (epoch := epoch) (fun {f before after engine signed due applied} contained => by
            obtain ⟨pre, -, -⟩ := Run.contains_split toZ _ contained
            have := currentEpoch_le_of_chainSteps pre.chainSteps
            simp only [epoch, state, callEpoch, ← boundaryEpoch]
            exact this)
          (by simp only [epoch, state, callEpoch, ← boundaryEpoch, zEpoch]
              exact UInt64.le_refl _) v
        simp only [partials, electra, dite_true]
        exact bound
      · rw [queuePaid_eq_zero_of_lt toZ (ZT ▸ Nat.lt_of_not_le electra) v]
        exact Nat.zero_le _
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
    have invZ := run_invariant genesis histZ
    have capZ := histZ.effectiveBalance_capped genesis caps.activation caps.compounding Zearly valZ
      (Array.mem_of_getElem? foundZ)
    have nextZ : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch z.state).toNat + 1 := by
      rw [z'Epoch, zEpochR]; exact next
    obtain ⟨cached, justified, rewarded, cachedOk, justifiedOk, altairRewards, phase0Rewards,
      fallZ⟩ := crossing_fall edge z'Early nextZ bands
        (run_pendingConsolidations genesis histZ Zearly delayPos) invZ.balancesMatch delayPos
        foundZ activeZ capZ clearZ'
    rw [effZ] at fallZ
    -- The effective balance stays through the next epoch.
    have insideZ' : v.toNat < z'.state.validators.data.size :=
      Nat.lt_of_lt_of_le insideZ (Run.nil.snoc (.slot edge)).registryLifecycle.size_le
    have yEff : effectiveAt y v.toNat = effectiveAt z' v.toNat :=
      fromZ'.effectiveKept_of_same_epoch early z'Epoch.symm v.toNat insideZ'
    -- The state that the rewards read is the last state of the epoch, after justification.
    have pendingZ := run_pendingSlots genesis histZ
    have invCached : Invariant cached := (frame_processSlot cachedOk).invariant invZ
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have pendingCached : PendingSlots cached := by rw [cachedEq]; exact pendingZ
    have finalizedRise := (processJustificationAndFinalization_invariant invCached.ordered
      invCached.settled justifiedOk).2.1
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
    have JPrevious : getPreviousEpoch justified = getPreviousEpoch P.state := by
      unfold getPreviousEpoch
      rw [JEpoch, callEpoch]
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
    have penaltyBound : actualBalanceAt z v.toNat ≤ actualBalanceAt ⟨z.fork, rewarded⟩ v.toNat +
        ((if .altair ≤ P.fork then base v.toNat else 3 * base v.toNat) + inactivity v.toNat) := by
      by_cases altairZ : .altair ≤ z.fork
      · have altairP : .altair ≤ P.fork := by rw [PT, ← ZT]; exact altairZ
        have altairT : .altair ≤ T.fork := by rw [← ZT]; exact altairZ
        obtain ⟨scored, scoredOk, rewardsOk⟩ := altairRewards altairZ
        have bound := (processRewardsAndPenalties_balance_le_of_inactivityUpdates altairZ
          (justified.validators.bound Zearly) scoredOk rewardsOk v.toNat insideJ).2
        dsimp only at bound
        rw [totalJ, effJ, balJ] at bound
        have scoreJ : (((justified.inactivityScores altairZ).data[v.toNat]?).map (·.toNat)).getD 0 =
            score v.toNat := by
          have zScore := toZ.inactivityScores_getElem?_of_same_epoch Zearly zEpoch altairT altairZ
            v.toNat (Nat.lt_of_lt_of_le insideR boundary.registryLifecycle.size_le)
          have pScore := tailP.inactivityScores_getElem?_of_same_epoch Pearly
            (callEpoch.trans boundaryEpoch.symm) altairT altairP v.toNat
            (Nat.lt_of_lt_of_le insideR boundary.registryLifecycle.size_le)
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
      · have before : z.fork < .altair := Nat.lt_of_not_le altairZ
        have altairP : ¬ .altair ≤ P.fork := by rw [PT, ← ZT]; exact altairZ
        have pendingJ := pendingCached.of_justification justifiedOk
        obtain ⟨share, -, -, each⟩ := processRewardsAndPenalties_balance_le_of_lt_altair before
          (justified.validators.bound Zearly) (phase0Rewards before)
          (fun attestations matching => pendingJ.matchingSource_slot before matching)
        have bound := (each v.toNat insideJ).2
        dsimp only at bound
        rw [totalJ, effJ, balJ] at bound
        -- Justification only raises the finalized epoch, which only shortens the delay.
        have finalizedZ : z.state.finalizedCheckpoint = T.state.finalizedCheckpoint :=
          toZ.finalizedCheckpoint_eq_of_same_epoch Zearly zEpoch
        have finalizedP : P.state.finalizedCheckpoint = T.state.finalizedCheckpoint :=
          tailP.finalizedCheckpoint_eq_of_same_epoch Pearly (callEpoch.trans boundaryEpoch.symm)
        have finalizedC : cached.finalizedCheckpoint = z.state.finalizedCheckpoint := by
          rw [cachedEq]
        rw [finalizedC, finalizedZ, ← finalizedP] at finalizedRise
        have rise := UInt64.le_iff_toNat_le.mp finalizedRise
        rw [JPrevious] at bound
        have quotient : (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat =
            p.INACTIVITY_PENALTY_QUOTIENT.toNat := by
          simp only [p]
          rw [ZT, PT]
        rw [quotient] at bound
        simp only [base, inactivity, altairP, ↓reduceIte, effV, root, delay, state]
        simp only [actualBalanceAt] at bound ⊢
        generalize hd : (getPreviousEpoch P.state).toNat -
          justified.finalizedCheckpoint.epoch.toNat = dJ at bound
        generalize hd' : (getPreviousEpoch P.state).toNat -
          P.state.finalizedCheckpoint.epoch.toNat = dP
        have shorter : dJ ≤ dP := by omega
        refine bound.trans (Nat.add_le_add_left (Nat.add_le_add_left ?_ _) _)
        split
        · rename_i long
          simp only [Nat.lt_of_lt_of_le long shorter, ↓reduceIte]
          exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_left _ shorter)) _
        · exact Nat.zero_le _
    -- Put the bounds together.
    have fallEq : fall v.toNat = fallGap preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        preset.downwardBand (effective v.toNat)
        (min (actual v.toNat - syncP v.toNat) (effective v.toNat) -
          (partials v.toNat + penalty v.toNat)) := rfl
    have penaltyEq : penalty v.toNat = ((if .altair ≤ P.fork then base v.toNat
        else 3 * base v.toNat) + inactivity v.toNat) + slots * sync v.toNat := rfl
    have syncPEq : syncP v.toNat = n * sync v.toNat := rfl
    have actualEq : actual v.toNat = actualBalanceAt P v.toNat := rfl
    have creditV := creditBound v
    rw [fallEq, syncPEq, actualEq, penaltyEq, yEff]
    beta_reduce
    rw [effV]
    have tzProduct := Nat.mul_le_mul_right (sync v.toNat) blocksTZ
    have rtProduct : boundary.blockCount * sync v.toNat + m * sync v.toNat ≤ n * sync v.toNat := by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right _ counted
    have increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := bands.1
    have incEq : inc = preset.EFFECTIVE_BALANCE_INCREMENT.toNat := rfl
    -- The balance after the rewards is at least the balance that the fall reads, lowered.
    generalize hLow : min (actualBalanceAt T v.toNat) EB - (partials v.toNat +
      ((if .altair ≤ P.fork then base v.toNat else 3 * base v.toNat) + inactivity v.toNat +
        slots * sync v.toNat)) = lowTrue
    have rewardedLow : lowTrue ≤ actualBalanceAt ⟨z.fork, rewarded⟩ v.toNat := by omega
    have gapTrue :=
      fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand EB rewardedLow
    generalize hlow : min (actualBalanceAt P v.toNat - n * sync v.toNat) EB -
      (partials v.toNat + ((if .altair ≤ P.fork then base v.toNat else 3 * base v.toNat) +
        inactivity v.toNat + slots * sync v.toNat)) = low
    by_cases zero : credit v = 0
    · -- Without other credits, the balance read at `T` covers the one that the fall reads.
      simp only [zero, ↓reduceIte, add_zero]
      have covered : low ≤ lowTrue := by omega
      have := fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand EB covered
      omega
    · -- With them, the downward band at `R` bounds what they can hide.
      simp only [zero, ↓reduceIte]
      generalize hc : min (credit v) (preset.downwardBand +
        min (boundary.queuePaid v) (EB - preset.MIN_ACTIVATION_BALANCE.toNat) +
          n * sync v.toNat) = c
      have covered : low - c ≤ lowTrue := by omega
      have one :=
        fallGap_anti preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand EB covered
      have two := fallGap_sub increment preset.downwardBand EB low c
      omega


end EthLib.Consensus
