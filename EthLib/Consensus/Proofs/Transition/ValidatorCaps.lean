module

public import EthLib.Consensus.Proofs.Transition.Totality.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.RunKept
public import EthLib.Consensus.Proofs.Proposers
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.RewardDeltas
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.DepositCarryCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Validator effective-balance caps

Each validator's effective balance is at most the cap of its withdrawal credentials.

Genesis gives it, and every step keeps it before Gloas.

An epoch and a slot keep it at every fork.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- At genesis, each validator's effective balance is at most the cap of its credentials. -/
theorem Genesis.effectiveBalance_capped {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ∀ validator ∈ g.state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset g.fork validator := by
  obtain ⟨hash, time, deposits, initialized⟩ := genesis
  exact (initializeBeaconStateFromEth1_withinBudget 0 (Nat.le_refl _) initialized).capped

/-- Unassigned validators retain their effective-balance funding and eligibility threshold. -/
private def UnassignedEligibleBalance {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.activationEpoch = FAR_FUTURE_EPOCH →
    (∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      (v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance) ∧ v.slashed = false

/-- A live candidate owns capped funding; assignment replaces it by a permanent MEB charge. -/
private def preKeyCharge {f : Fork} (candidate : Nat → Bool)
    (s : BeaconState preset f) (i : Nat) : Nat :=
  if candidate i then
    ((s.validators.data[i]?).map fun v =>
      if v.activationEpoch = FAR_FUTURE_EPOCH then
        max v.effectiveBalance.toNat
          (min ((s.balances.data[i]?.map UInt64.toNat).getD 0)
            (withdrawalMaxEffectiveBalance preset f v).toNat)
      else preset.MAX_EFFECTIVE_BALANCE.toNat).getD 0
  else 0

private theorem preKeyCharge_balance {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (credit : Nat → Nat)
    (growth : ∀ i, ((t.balances.data[i]?.map UInt64.toNat).getD 0) ≤
      ((s.balances.data[i]?.map UInt64.toNat).getD 0) + credit i) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i + credit i := by
  intro i
  have paid := growth i
  unfold preKeyCharge
  rw [same]
  split
  · cases found : s.validators.data[i]? with
    | none => simp
    | some v =>
      simp only [Option.map_some, Option.getD_some]
      split <;> omega
  · omega

private theorem preKeyCharge_same {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (balances : t.balances = s.balances) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  intro i
  simp only [preKeyCharge, same, balances]

private theorem preKeyCharge_sum_range {f : Fork} (candidate : Nat → Bool)
    (s : BeaconState preset f) {size : Nat} (contains : s.validators.data.size ≤ size) :
    (∑ i ∈ Finset.range size, preKeyCharge candidate s i) =
      ∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i := by
  symm
  apply Finset.sum_subset (Finset.range_mono contains)
  intro i _ outside
  have absent : s.validators.data[i]? = none := Array.getElem?_eq_none (by
    simpa only [Finset.mem_range, not_lt] using outside)
  simp only [preKeyCharge, absent, Option.map_none, Option.getD_none, ite_self]

private theorem preKeyCharge_notRaised {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (lowered : ∀ i, BalanceNotRaised i s t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i := by
  have growth := preKeyCharge_balance candidate same (fun _ => 0) (by
    intro i
    cases after : t.balances.data[i]? with
    | none => simp only [Option.map_none, Option.getD_none, Nat.zero_le]
    | some b =>
      obtain ⟨a, before, low⟩ := lowered i b after
      simpa only [after, before, Option.map_some, Option.getD_some, Nat.add_zero] using
        UInt64.le_iff_toNat_le.mp low)
  simpa only [Nat.add_zero] using growth

private theorem preKeyCharge_of_live_balances {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (held : UnassignedEligibleBalance s)
    (balances : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → ∀ balance,
      s.balances.data[i]? = some balance → t.balances.data[i]? = some balance) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  intro i
  cases found : s.validators.data[i]? with
  | none => simp only [preKeyCharge, same, found, Option.map_none, Option.getD_none]
  | some v =>
    by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨balance, read, _⟩ := (held i v found pending).1
      simp only [preKeyCharge, same, found, pending, ↓reduceIte, Option.map_some,
        Option.getD_some, read, balances i v found pending balance read]
    · simp only [preKeyCharge, same, found, pending, ↓reduceIte, Option.map_some,
        Option.getD_some]

/-- At genesis, unassigned validators are funded and none is eligible yet. -/
private theorem genesis_unassigned_eligible_balance {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    UnassignedEligibleBalance g.state := by
  intro i v found pending
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨funded, unassigned, unslashed⟩ := initializeBeaconStateFromEth1_unassigned_eligibility
    initialized i v found pending
  refine ⟨funded, ?_, unslashed⟩
  exact fun assigned => False.elim (assigned unassigned)

private theorem UnassignedEligibleBalance.transfer {f h : Fork}
    {s : BeaconState preset f} {t : BeaconState preset h}
    (held : UnassignedEligibleBalance s) (same : t.validators.data = s.validators.data)
    (balances : ∀ (i : Nat) (v : Validator) (b : Gwei),
      s.validators.data[i]? = some v → v.activationEpoch = FAR_FUTURE_EPOCH →
      s.balances.data[i]? = some b → v.effectiveBalance ≤ b →
      ∃ c, t.balances.data[i]? = some c ∧ v.effectiveBalance ≤ c) :
    UnassignedEligibleBalance t := by
  intro i v found pending
  have before := same ▸ found
  obtain ⟨⟨b, read, low⟩, eligible, unslashed⟩ := held i v before pending
  exact ⟨balances i v b before pending read low, eligible, unslashed⟩

private theorem UnassignedEligibleBalance.setBalance {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : UnassignedEligibleBalance s)
    (floor : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → v.effectiveBalance ≤ amount)
    (ok : s.setBalance index amount = .ok t) : UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := setBalance_ok ok
  apply held.transfer (t := s.putBalance index.toNat inside amount) rfl
  intro i v b found pending read low
  by_cases same : index.toNat = i
  · subst i
    exact ⟨amount, by simp [BeaconState.putBalance], floor v found pending⟩
  · refine ⟨b, ?_, low⟩
    simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same] using read

private theorem UnassignedEligibleBalance.increase {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : UnassignedEligibleBalance s)
    (ok : increaseBalance s index amount = .ok t) : UnassignedEligibleBalance t := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  apply held.transfer (t := s.putBalance index.toNat inside
    (s.balances.data[index.toNat] + amount)) rfl
  intro i v b _ _ read low
  by_cases same : index.toNat = i
  · subst i
    have equal := Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans read)
    subst b
    refine ⟨s.balances.data[index.toNat] + amount, by simp [BeaconState.putBalance], ?_⟩
    apply UInt64.le_trans low
    apply UInt64.le_iff_toNat_le.mpr
    rw [Uint64.toNat_add_of_lt fits]
    omega
  · refine ⟨b, ?_, low⟩
    simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same] using read

private theorem UnassignedEligibleBalance.decrease {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : UnassignedEligibleBalance s)
    (assigned : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : decreaseBalance s index amount = .ok t) : UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  apply held.transfer (t := s.putBalance index.toNat inside
    (Uint64.saturatingSub s.balances.data[index.toNat] amount)) rfl
  intro i v b found pending read low
  have different : index.toNat ≠ i := by
    rintro rfl
    exact assigned v found pending
  refine ⟨b, ?_, low⟩
  simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set, different] using read

private theorem UnassignedEligibleBalance.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (held : UnassignedEligibleBalance s) (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    UnassignedEligibleBalance t := by
  obtain ⟨validators, balances⟩ := addValidatorToRegistry_push ok matched
  have sizes : s.validators.data.size = s.balances.data.size := matched.symm
  intro i v found pending
  rw [validators, Array.getElem?_push] at found
  split at found
  · rename_i equal
    cases found
    refine ⟨⟨amount, ?_, ?_⟩, fun impossible => (impossible rfl).elim, rfl⟩
    · simp [balances, equal, sizes]
    · apply UInt64.le_iff_toNat_le.mpr
      change (min (amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT) _).toNat ≤ amount.toNat
      rw [Uint64.toNat_min]
      apply Nat.le_trans (Nat.min_le_left _ _)
      exact UInt64.le_iff_toNat_le.mp (UInt64.sub_le (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
        exact Nat.mod_le _ _))
  · rename_i different
    obtain ⟨⟨b, read, low⟩, eligible, unslashed⟩ := held i v found pending
    exact ⟨⟨b, by simpa [balances, Array.getElem?_push, ← sizes, different] using read, low⟩,
      eligible, unslashed⟩

private theorem UnassignedEligibleBalance.setValidatorAt {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {v w : Validator}
    (held : UnassignedEligibleBalance s) (found : getValidatorAt s i = .ok v)
    (set : s.setValidatorAt i w = .ok t)
    (kept : w.activationEpoch = FAR_FUTURE_EPOCH →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧
      w.effectiveBalance ≤ v.effectiveBalance ∧
      (w.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ w.effectiveBalance) ∧ w.slashed = false) :
    UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j old read pending
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read
  split at read
  · rename_i equal
    subst j
    cases read
    obtain ⟨before, lower, eligible, unslashed⟩ := kept pending
    obtain ⟨⟨b, located, funded⟩, _, _⟩ :=
      held i v (getValidatorAt_eq_ok_iff.mp found) before
    exact ⟨⟨b, located, UInt64.le_trans lower funded⟩, eligible, unslashed⟩
  · exact held j old read pending

private theorem queueForActivation_eligibility {f : Fork} {s : BeaconState preset f}
    {v w : Validator}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (eligible : v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
      preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance)
    (ok : queueForActivation s v = .ok w) :
    w.effectiveBalance = v.effectiveBalance ∧ w.activationEpoch = v.activationEpoch ∧
      w.slashed = v.slashed ∧
      (w.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ w.effectiveBalance) := by
  unfold queueForActivation at ok
  split at ok
  · rename_i queued
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    refine ⟨rfl, rfl, rfl, fun _ => ?_⟩
    unfold isEligibleForActivationQueue at queued
    split at queued
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at queued
      exact UInt64.le_trans activation queued.2
    · simp only [Bool.and_eq_true, beq_iff_eq] at queued
      exact UInt64.le_of_eq queued.2.symm
  · cases ok
    exact ⟨rfl, rfl, rfl, eligible⟩

private theorem UnassignedEligibleBalance.effective {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {v : Validator} {balance result : Gwei}
    (held : UnassignedEligibleBalance s)
    (aligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (caps : ∀ v ∈ s.validators.data,
      preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset f v)
    (found : getValidatorAt s i = .ok v) (read : getBalanceAt s i = .ok balance)
    (scalar : updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v)
      balance v.effectiveBalance = .ok result)
    (set : s.setValidatorAt i { v with effectiveBalance := result } = .ok t) :
    UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j w located pending
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at located
  split at located
  · rename_i equal
    subst j
    cases located
    obtain ⟨⟨b, owned, funded⟩, eligible, unslashed⟩ :=
      held i v (getValidatorAt_eq_ok_iff.mp found) pending
    have equal := Option.some.inj (owned.symm.trans (getBalanceAt_eq_ok_iff.mp read))
    subst b
    refine ⟨⟨balance, owned, ?_⟩, ?_, unslashed⟩
    · rcases updatedEffectiveBalance_eq_or_le scalar with rfl | ⟨lower, _⟩
      · exact funded
      · exact lower
    · intro queued
      have old := eligible queued
      rcases updatedEffectiveBalance_cases scalar with rfl | rfl
      · exact old
      · apply UInt64.le_iff_toNat_le.mpr
        rw [Uint64.toNat_min, toNat_rounded]
        apply Nat.le_min.mpr
        constructor
        · have whole := congrArg UInt64.toNat aligned
          simp only [UInt64.toNat_mod, UInt64.toNat_zero] at whole
          have low := UInt64.le_iff_toNat_le.mp (UInt64.le_trans old funded)
          have division := Nat.div_le_div_right
            (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) low
          have product := Nat.mul_le_mul_left preset.EFFECTIVE_BALANCE_INCREMENT.toNat division
          have splitOld := Nat.mod_add_div preset.MAX_EFFECTIVE_BALANCE.toNat
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          have splitBalance := Nat.mod_add_div balance.toNat
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          rw [whole] at splitOld
          omega
        · exact UInt64.le_iff_toNat_le.mp (caps v (mem_of_getValidatorAt found))
  · exact held j w located pending

private theorem UnassignedEligibleBalance.withdrawals {f : Fork}
    {s t : BeaconState preset f} {capella : .shapella ≤ f}
    {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (held : UnassignedEligibleBalance s)
    (same : t.validators.data = s.validators.data)
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (unwithdrawable : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → getCurrentEpoch s < v.withdrawableEpoch)
    (unqueued : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → ∀ electra : .pectra ≤ f,
        ∀ pending ∈ (s.pendingPartialWithdrawals electra).data,
          pending.validatorIndex.toNat ≠ i)
    (ok : processWithdrawals s capella payload = .ok t) : UnassignedEligibleBalance t := by
  apply held.transfer same
  intro i v b found pending read low
  obtain ⟨later, located, retained⟩ := processWithdrawals_capped ok found
    (unwithdrawable i v found pending) (unqueued i v found pending) b read
  refine ⟨later, located, ?_⟩
  have bound := capped v (Array.mem_of_getElem? found)
  exact UInt64.le_trans (by
      apply UInt64.le_iff_toNat_le.mpr
      rw [Uint64.toNat_min]
      exact Nat.le_min.mpr ⟨UInt64.le_iff_toNat_le.mp low, UInt64.le_iff_toNat_le.mp bound⟩)
    (UInt64.le_trans retained (by
      apply UInt64.le_iff_toNat_le.mpr
      rw [Uint64.toNat_min]
      exact Nat.min_le_left _ _))

private theorem UnassignedEligibleBalance.ineligible {f : Fork} {s : BeaconState preset f}
    {i : Nat} {v : Validator} (held : UnassignedEligibleBalance s)
    (found : s.validators.data[i]? = some v) (pending : v.activationEpoch = FAR_FUTURE_EPOCH) :
    isEligibleValidator (getPreviousEpoch s) v = .ok false := by
  have unslashed := (held i v found pending).2.2
  have inactive : isActiveValidator v (getPreviousEpoch s) = false := by
    simp only [isActiveValidator, pending, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases later : FAR_FUTURE_EPOCH ≤ getPreviousEpoch s
    · apply Or.inr
      have bound := v.exitEpoch.toNat_lt
      have high := UInt64.le_iff_toNat_le.mp later
      intro less
      have low := UInt64.lt_iff_toNat_lt.mp less
      change 18446744073709551615 ≤ (getPreviousEpoch s).toNat at high
      omega
    · exact Or.inl later
  simp [isEligibleValidator, inactive, unslashed, pure, Except.pure]

private theorem UnassignedEligibleBalance.rewardsAltair_balance {f : Fork}
    {s t : BeaconState preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) {i : Nat} {v : Validator} {b : Gwei}
    (found : s.validators.data[i]? = some v) (pending : v.activationEpoch = FAR_FUTURE_EPOCH)
    (read : s.balances.data[i]? = some b) : t.balances.data[i]? = some b := by
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · obtain rfl := Except.ok.inj ((processRewardsAndPenalties_genesis config genesis).symm.trans ok)
    exact read
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have equal : s.validators.data[i] = v := (Array.getElem?_eq_some_iff.mp found).2
  have ineligible := held.ineligible found pending
  obtain ⟨flags, inactivity, flagged, penalized, balances⟩ :=
    processRewardsAndPenalties_balances_of_altair altair genesis ok
  have zero (delta) (member : delta ∈ flags ++ [inactivity]) :
      delta.1.getD i 0 = 0 ∧ delta.2.getD i 0 = 0 := by
    rcases List.mem_append.mp member with flag | last
    · obtain ⟨j, _, computed⟩ := mapM_ok_mem flagged _ flag
      obtain ⟨_, _, _, _, _, _, entries⟩ :=
        getFlagIndexDeltas_getD (s.validators.bound early) computed
      obtain ⟨eligible, tested, empty, _⟩ := entries i inside
      rw [equal, ineligible, Except.ok.injEq] at tested
      exact empty tested.symm
    · obtain rfl := List.mem_singleton.mp last
      obtain ⟨_, _, entries⟩ := getInactivityPenaltyDeltas_getD_of_altair altair
        (s.validators.bound early) penalized
      obtain ⟨eligible, tested, reward, penalty, _⟩ := entries i inside
      rw [equal, ineligible, Except.ok.injEq] at tested
      exact ⟨reward, penalty (.inl tested.symm)⟩
  have folded : (flags ++ [inactivity]).foldl (fun balance delta =>
      Uint64.saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) b = b := by
    have unchanged : ∀ (ds : List (Array Gwei × Array Gwei)),
        (∀ d ∈ ds, d.1.getD i 0 = 0 ∧ d.2.getD i 0 = 0) →
        ds.foldl (fun balance delta =>
          Uint64.saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) b = b := by
      intro ds
      induction ds with
      | nil => exact fun _ => rfl
      | cons d ds ih =>
        intro empty
        obtain ⟨reward, penalty⟩ := empty d List.mem_cons_self
        simp only [List.foldl_cons, reward, penalty, UInt64.add_zero]
        have unchanged : Uint64.saturatingSub b 0 = b := by
          simp [Uint64.saturatingSub]
          exact fun zero => zero.symm
        rw [unchanged]
        exact ih (fun d member => empty d (List.mem_cons_of_mem _ member))
    exact unchanged _ zero
  have value := (balances i).1 inside
  rw [read] at value
  change t.balances.data[i]? = some _ at value
  dsimp only at value
  rw [folded] at value
  exact value

private theorem UnassignedEligibleBalance.rewardsAltair {f : Fork}
    {s t : BeaconState preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) : UnassignedEligibleBalance t := by
  apply held.transfer (by rw [processRewardsAndPenalties_frame ok])
  intro i v b found pending read low
  exact ⟨b, held.rewardsAltair_balance altair early ok found pending read, low⟩

private theorem preKeyCharge_rewardsAltair {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  have registry : t.validators.data = s.validators.data := by
    rw [processRewardsAndPenalties_frame ok]
  intro i
  cases found : s.validators.data[i]? with
  | none => simp only [preKeyCharge, registry, found, Option.map_none, Option.getD_none]
  | some v =>
    by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨⟨b, read, _⟩, _⟩ := held i v found pending
      have same := held.rewardsAltair_balance altair early ok found pending read
      simp only [preKeyCharge, registry, found, read, same]
    · simp only [preKeyCharge, registry, found, Option.map_some, pending, ↓reduceIte]

private theorem preKeyCharge_slashings {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (ok : processSlashings s = .ok t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i :=
  preKeyCharge_notRaised candidate (by rw [processSlashings_frame ok])
    (balanceNotRaised_processSlashings ok)

private theorem UnassignedEligibleBalance.rewards {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) : UnassignedEligibleBalance t := by
  by_cases altair : .altair ≤ f
  · exact held.rewardsAltair altair early ok
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · obtain rfl := Except.ok.inj ((processRewardsAndPenalties_genesis config genesis).symm.trans ok)
    exact held
  have before := Nat.lt_of_not_le altair
  apply held.transfer (by rw [processRewardsAndPenalties_frame ok])
  intro i v b found pending read low
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have equal : s.validators.data[i] = v := (Array.getElem?_eq_some_iff.mp found).2
  have ineligible := held.ineligible found pending
  obtain ⟨rewards, penalties, deltas, balances⟩ :=
    processRewardsAndPenalties_balances_of_lt_altair before genesis ok
  obtain ⟨source, target, head, inclusion, inactivity, sourced, targeted, headed,
    included, penalized, entries⟩ := getAttestationDeltas_getD before deltas
  have component {attestations : Array (PendingAttestation preset)}
      {deltas : Array Gwei × Array Gwei}
      (computed : getAttestationComponentDeltas s attestations = .ok deltas) :
      deltas.2.getD i 0 = 0 := by
    obtain ⟨_, _, _, _, _, _, entries⟩ :=
      getAttestationComponentDeltas_getD (s.validators.bound early) computed
    obtain ⟨eligible, tested, empty, _⟩ := entries i inside
    rw [equal, ineligible, Except.ok.injEq] at tested
    exact (empty tested.symm).2
  have sourceZero : source.2.getD i 0 = 0 := by
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp sourced
    exact component computed
  have targetZero : target.2.getD i 0 = 0 := by
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp targeted
    exact component computed
  have headZero : head.2.getD i 0 = 0 := by
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp headed
    exact component computed
  have inactivityZero : inactivity.2.getD i 0 = 0 := by
    obtain ⟨_, leak, _, quiet, leaking⟩ := getInactivityPenaltyDeltas_getD_of_lt_altair
      before (s.validators.bound early) penalized
    cases leak with
    | false => exact quiet rfl i
    | true =>
      obtain ⟨_, _, _, _, _, _, _, _, entries⟩ := leaking rfl
      obtain ⟨eligible, tested, empty, _⟩ := entries i inside
      rw [equal, ineligible, Except.ok.injEq] at tested
      exact empty tested.symm
  have penaltyZero : penalties.getD i 0 = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [sourceZero, targetZero, headZero, inactivityZero] using (entries i inside).2
  obtain ⟨old, located, fits, value⟩ := (balances i).1 inside
  obtain rfl := Option.some.inj (read.symm.trans located)
  refine ⟨b + rewards.getD i 0, ?_, UInt64.le_trans low ?_⟩
  · have zero (amount : Gwei) : Uint64.saturatingSub amount 0 = amount := by
      simp [Uint64.saturatingSub]
      exact fun equal => equal.symm
    simpa only [penaltyZero, zero] using value
  · apply UInt64.le_iff_toNat_le.mpr
    rw [Uint64.toNat_add_of_lt fits]
    omega

private theorem UnassignedEligibleBalance.slashings {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s) (ok : processSlashings s = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.transfer (by rw [processSlashings_frame ok])
  intro i v b found pending read low
  have unslashed := (held i v found pending).2.2
  have notDue : ¬ SlashingPenaltyDue preset (getCurrentEpoch s) v := by
    intro due
    simp [SlashingPenaltyDue, unslashed] at due
  by_cases electra : .pectra ≤ f
  · obtain ⟨_, _, _, _, balances⟩ := processSlashings_balances_of_electra electra
      (s.validators.bound early) ok
    obtain ⟨w, located, value⟩ := (balances i).1 (Array.getElem?_eq_some_iff.mp found).1
    obtain rfl := Option.some.inj (found.symm.trans located)
    exact ⟨b, by simpa [read, notDue] using value, low⟩
  · obtain ⟨_, _, _, _, balances⟩ := processSlashings_balances_of_lt_electra
      (Nat.lt_of_not_le electra) ok
    obtain ⟨w, located, value⟩ := (balances i).1 (Array.getElem?_eq_some_iff.mp found).1
    obtain rfl := Option.some.inj (found.symm.trans located)
    exact ⟨b, by simpa [read, notDue] using value, low⟩

private theorem UnassignedEligibleBalance.attestation {f : Fork}
    {s t : BeaconState preset f} {parentSlot : Slot} {attestation : Attestation preset f}
    (held : UnassignedEligibleBalance s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.transfer (congrArg (·.data) (processAttestation_registry ok).1)
  intro i v b _ _ read low
  by_cases altair : .altair ≤ f
  · rw [processAttestation_of_altair altair] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, balances⟩ :=
      processAttestationAltair_balance ok
    obtain ⟨now, located, value⟩ := balances i b read
    refine ⟨now, located, UInt64.le_trans low (UInt64.le_iff_toNat_le.mpr ?_)⟩
    rw [value]
    exact Nat.le_add_right _ _
  · unfold processAttestation at ok
    simp only [altair, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
    have kept := recordPendingAttestation_ok recorded
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      exact ⟨b, by rw [show _ = s.balances from congrArg (·.balances) rest]; exact read, low⟩

private theorem sync_member_not_unassigned {f : Fork} {s : BeaconState preset f}
    {altair : .altair ≤ f} {members : Array ValidatorIndex}
    (mapped : (s.currentSyncCommittee altair).value.pubkeys.toArray.mapM
      (validatorIndexOfPubkey s) = .ok members)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (excluded : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      key ≠ v.pubkey) {member : ValidatorIndex} (named : member ∈ members.toList) :
    member.toNat ≠ i := by
  intro same
  have onList : (s.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
      (validatorIndexOfPubkey s) = .ok members.toList := by
    rw [← Array.toList_mapM, mapped]
    rfl
  obtain ⟨key, keyed, image⟩ := mapM_ok_mem onList member named
  unfold validatorIndexOfPubkey at image
  split at image
  · rename_i position located
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at image
    obtain ⟨there, equal⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    rw [(Uint64.ofNatChecked_ok_iff.mp image).2] at same
    subst i
    rw [Array.getElem?_eq_getElem there, Option.some.injEq] at found
    subst v
    exact excluded key (by simpa using keyed) (beq_iff_eq.mp equal.1).symm
  · cases image

private theorem UnassignedEligibleBalance.sync {f : Fork}
    {s t : BeaconState preset f} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (held : UnassignedEligibleBalance s)
    (excluded : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH →
      ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList, key ≠ v.pubkey)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    UnassignedEligibleBalance t := by
  obtain ⟨reward, proposerReward, members, chosen, _, _, mapped, _, balances⟩ :=
    processSyncAggregate_balance ok
  obtain ⟨_, shape⟩ := processSyncAggregate_eq ok
  apply held.transfer (by rw [shape])
  intro i v b found pending read low
  obtain ⟨final, located, value⟩ := balances i b read
  have apart : ∀ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1.toNat ≠ i := by
    intro member inside
    exact sync_member_not_unassigned mapped found (excluded i v found pending)
      (List.of_mem_zip (by simpa only [Array.toList_zip] using inside)).1
  refine ⟨final, located, UInt64.le_trans low (UInt64.le_iff_toNat_le.mpr ?_)⟩
  rw [value]
  apply List.foldlRecOn (motive := fun n : Nat => b.toNat ≤ n)
    (members.zip aggregate.syncCommitteeBits.bits.toArray).toList _ (Nat.le_refl _)
  intro balance previous member inside
  by_cases signed : member.2 = true
  · simp only [signed, ↓reduceIte]
    omega
  · simpa [signed, apart member inside] using previous

/-- Ordered preset caps and retained compounding credentials make a validator's cap monotone. -/
private theorem withdrawalMaxEffectiveBalance_mono {f h : Fork} {v w : Validator}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h)
    (credentials : hasCompoundingWithdrawalCredential v = true →
      hasCompoundingWithdrawalCredential w = true) :
    withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split <;> rename_i before
  · have later : Fork.pectra ≤ h := Nat.le_trans before forks
    rw [ite_eq_left later]
    split <;> rename_i compound
    · rw [ite_eq_left (credentials compound)]
      exact UInt64.le_refl _
    · split
      · exact compounding
      · exact UInt64.le_refl _
  · split
    · split
      · exact UInt64.le_trans activation compounding
      · exact activation
    · exact UInt64.le_refl _

private theorem capped_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator}
    (capped : ∀ w ∈ s.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : s.setValidatorAt i v = .ok t) :
    ∀ w ∈ t.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  intro w member
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact capped w old
  · exact bound

/-- Cached proposers retain their registry index and assigned activation epoch. -/
private def AssignedProposers {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ fulu : .fusaka ≤ f, ∀ i ∈ (s.proposerLookahead fulu).toList,
    ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH

/-- Each end of a queued consolidation has assigned activation at its stable index. -/
private def AssignedTargets {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
    ∀ index ∈ [entry.sourceIndex, entry.targetIndex],
      ∃ v, s.validators.data[index.toNat]? = some v ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH

private theorem AssignedTargets.transfer {f : Fork} {s t : BeaconState preset f}
    (held : AssignedTargets s) (life : RegistryLifecycle s t)
    (subset : ∀ electra : .pectra ≤ f,
      ∀ entry ∈ (t.pendingConsolidations electra).data.toList,
        entry ∈ (s.pendingConsolidations electra).data.toList) : AssignedTargets t := by
  intro electra entry member index named
  obtain ⟨v, found, assigned⟩ := held electra entry (subset electra entry member) index named
  obtain ⟨w, read, kept⟩ := life.validators index.toNat v found
  exact ⟨w, read, (kept.activationEpoch assigned) ▸ assigned⟩

private theorem UnassignedEligibleBalance.consolidations {f : Fork}
    {s t : BeaconState preset f} {electra : .pectra ≤ f}
    (held : UnassignedEligibleBalance s) (sources : AssignedTargets s)
    (ok : processPendingConsolidations s electra = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.transfer (congrArg (·.data) (processPendingConsolidations_kept ok).1)
  intro i v b found pending read low
  have excluded (entry : PendingConsolidation)
      (member : entry ∈ (s.pendingConsolidations electra).data) :
      entry.sourceIndex.toNat ≠ i := by
    intro same
    obtain ⟨w, located, assigned⟩ := sources electra entry (by simpa using member)
      entry.sourceIndex (by simp)
    rw [same, found, Option.some.injEq] at located
    subst w
    exact assigned pending
  obtain ⟨now, located, rose⟩ := processPendingConsolidations_balanceNotLowered ok excluded b read
  exact ⟨now, located, UInt64.le_trans low rose⟩

private theorem assigned_of_key_provenance {f : Fork} {s : BeaconState preset f}
    {keys : List Cryptography.Bls.BLSPubkey} (unique : PubkeysDistinct s)
    (assigned : ∀ key ∈ keys,
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∀ key ∈ keys, ∀ (i : Nat) (v : Validator),
      s.validators.data[i]? = some v → v.pubkey = key →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  intro key member i v found equal
  obtain ⟨j, w, read, keyed, active⟩ := assigned key member
  obtain ⟨inside, atIndex⟩ := Array.getElem?_eq_some_iff.mp found
  obtain ⟨there, atOther⟩ := Array.getElem?_eq_some_iff.mp read
  have same : i = j := unique.eq_of_getElem_eq
    (by simpa [validatorKeys] using inside) (by simpa [validatorKeys] using there)
    (by simpa [validatorKeys, atIndex, atOther] using equal.trans keyed.symm)
  subst j
  have sameValidator := Option.some.inj (found.symm.trans read)
  subst w
  simpa only [atIndex] using active

private theorem UnassignedEligibleBalance.sync_of_provenance {f : Fork}
    {s t : BeaconState preset f} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (held : UnassignedEligibleBalance s) (unique : PubkeysDistinct s)
    (assigned : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.sync (ok := ok)
  intro i v found pending key member equal
  exact assigned_of_key_provenance unique assigned key member i v found equal.symm pending

private def AssignedPartials {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingPartialWithdrawals electra).data.toList,
    ∃ v, s.validators.data[entry.validatorIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH

private theorem AssignedPartials.transfer {f : Fork} {s t : BeaconState preset f}
    (held : AssignedPartials s) (life : RegistryLifecycle s t)
    (subset : ∀ electra : .pectra ≤ f,
      ∀ entry ∈ (t.pendingPartialWithdrawals electra).data.toList,
        entry ∈ (s.pendingPartialWithdrawals electra).data.toList) : AssignedPartials t := by
  intro electra entry member
  obtain ⟨v, found, assigned⟩ := held electra entry (subset electra entry member)
  obtain ⟨w, read, kept⟩ := life.validators entry.validatorIndex.toNat v found
  exact ⟨w, read, (kept.activationEpoch assigned) ▸ assigned⟩

private theorem AssignedPartials.drop {f : Fork} {s : BeaconState preset f}
    (held : AssignedPartials s) (electra : .pectra ≤ f) (count : Nat) :
    AssignedPartials (updatePendingPartialWithdrawals s electra count) := by
  intro witness entry member
  apply held witness entry
  simp only [updatePendingPartialWithdrawals, Array.toList_extract,
    List.extract_eq_take_drop] at member
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

private theorem AssignedPartials.increase {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (held : AssignedPartials s)
    (ok : increaseBalance s index amount = .ok t) : AssignedPartials t := by
  obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  exact held

private theorem AssignedPartials.decrease {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (held : AssignedPartials s)
    (ok : decreaseBalance s index amount = .ok t) : AssignedPartials t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  exact held

private theorem AssignedPartials.attestation {f : Fork}
    {s t : BeaconState preset f} {parentSlot : Slot} {attestation : Attestation preset f}
    (held : AssignedPartials s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    AssignedPartials t := by
  by_cases altair : .altair ≤ f
  · rw [processAttestation_of_altair altair] at ok
    unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have flags (participation : EpochParticipation preset f) :
        AssignedPartials (setEpochParticipation s
          (attestation.data.target.epoch == getCurrentEpoch s) participation) := by
      unfold setEpochParticipation
      split <;> exact held
    have paid := (flags _).increase raisedOk
    split at final
    · rw [recordPaymentWeight_eq final]
      exact paid
    · cases final
      exact paid
  · intro electra
    exact (altair (Nat.le_trans (by decide : Fork.altair ≤ .pectra) electra)).elim

private theorem AssignedPartials.excludes {f : Fork} {s : BeaconState preset f}
    (held : AssignedPartials s) {i : Nat} {v : Validator}
    (found : s.validators.data[i]? = some v)
    (pending : v.activationEpoch = FAR_FUTURE_EPOCH) (electra : .pectra ≤ f)
    (entry : PendingPartialWithdrawal)
    (member : entry ∈ (s.pendingPartialWithdrawals electra).data) :
    entry.validatorIndex.toNat ≠ i := by
  intro same
  obtain ⟨w, read, assigned⟩ := held electra entry (List.mem_toArray.mp (by simpa using member))
  rw [same, found, Option.some.injEq] at read
  subst w
  exact assigned pending

private theorem AssignedPartials.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v w : Validator} (held : AssignedPartials s)
    (found : getValidator s i = .ok v) (set : s.setValidator i w = .ok t)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH) : AssignedPartials t := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro electra entry member
  obtain ⟨old, read, active⟩ := held electra entry member
  by_cases equal : entry.validatorIndex.toNat = i.toNat
  · have same := Option.some.inj ((getValidator_eq_ok_iff.mp found).symm.trans (equal ▸ read))
    subst old
    exact ⟨w, by simp [BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, equal], assigned active⟩
  · exact ⟨old, by simpa [BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, Ne.symm equal] using read,
      active⟩

private theorem unassigned_withdrawable_far {f : Fork} {s : BeaconState preset f}
    (activation : ActivationExitOrder s) (exits : ExitsOrdered s)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (pending : v.activationEpoch = FAR_FUTURE_EPOCH) :
    v.withdrawableEpoch = FAR_FUTURE_EPOCH := by
  have member := Array.mem_of_getElem? found
  have low := UInt64.le_iff_toNat_le.mp
    (UInt64.le_trans (activation v member) (exits v member))
  rw [pending] at low
  apply UInt64.toNat_inj.mp
  have bound := v.withdrawableEpoch.toNat_lt
  change 18446744073709551615 ≤ v.withdrawableEpoch.toNat at low
  change v.withdrawableEpoch.toNat = 18446744073709551615
  omega

private theorem UnassignedEligibleBalance.withdrawals_of_provenance {f : Fork}
    {s t : BeaconState preset f} {capella : .shapella ≤ f}
    {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (held : UnassignedEligibleBalance s) (activation : ActivationExitOrder s)
    (exits : ExitsOrdered s) (partials : AssignedPartials s)
    (same : t.validators.data = s.validators.data)
    (before : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : processWithdrawals s capella payload = .ok t) : UnassignedEligibleBalance t := by
  apply held.withdrawals same capped
    (fun i v found pending => by
      rw [unassigned_withdrawable_far activation exits found pending]
      exact before)
    (fun _ _ found pending electra entry member =>
      partials.excludes found pending electra entry member) ok

private theorem assigned_of_active {v : Validator} {epoch : Epoch}
    (active : isActiveValidator v epoch = true) : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  intro far
  have less := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt active.1 active.2)
  rw [far] at less
  have bound := v.exitEpoch.toNat_lt
  change (2 ^ 64 - 1 : Nat) < v.exitEpoch.toNat at less
  omega

private theorem assigned_of_slashable {v : Validator} {epoch : Epoch}
    (slashable : isSlashableValidator v epoch = true) : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at slashable
  intro far
  have less := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt slashable.1.2 slashable.2)
  rw [far] at less
  have bound := v.withdrawableEpoch.toNat_lt
  change (2 ^ 64 - 1 : Nat) < v.withdrawableEpoch.toNat at less
  omega

private theorem assigned_draw {f : Fork} {s : BeaconState preset f} {epoch : Epoch}
    {proposers : Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat}
    (ok : getBeaconProposerIndices s epoch = .ok proposers) :
    ∀ i ∈ proposers.toList,
      ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨active, checked, rest⟩ := bind_ok_iff.mp ok
  obtain ⟨seed, _, drawn⟩ := bind_ok_iff.mp rest
  intro i member
  have selected := mem_of_computeProposerIndices drawn i member
  have selected : i ∈ active := by
    unfold proposerCandidates at selected
    split at selected
    · exact List.mem_toArray.mp (Array.mem_filter.mp selected).1
    · exact List.mem_toArray.mp selected
  obtain ⟨v, found, active⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp selected
  exact ⟨v, found, assigned_of_active active⟩

private theorem AssignedProposers.transfer {f : Fork} {s t : BeaconState preset f}
    (held : AssignedProposers s) (life : RegistryLifecycle s t)
    (same : t.proposerLookahead = s.proposerLookahead) : AssignedProposers t := by
  intro fulu i member
  rw [same] at member
  obtain ⟨v, found, assigned⟩ := held fulu i member
  obtain ⟨w, read, kept⟩ := life.validators i.toNat v found
  exact ⟨w, read, (kept.activationEpoch assigned) ▸ assigned⟩

private theorem initialized_proposers {f : Fork} {s : BeaconState preset f}
    {lookahead : Vector ValidatorIndex
      ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)}
    (ok : initializeProposerLookahead s = .ok lookahead) :
    ∀ i ∈ lookahead.toList,
      ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨epochs, drawn, flattened⟩ := bind_ok_iff.mp ok
  cases flattened
  intro i member
  obtain ⟨epoch, member, selected⟩ := Vector.mem_flatten.mp (by simpa using member)
  obtain ⟨j, inside, rfl⟩ := List.getElem_of_mem
    (show epoch ∈ epochs.toList by simpa using member)
  have draw := vector_mapM_ok_getElem drawn j (by simpa using inside)
  obtain ⟨e, _, computed⟩ := bind_ok_iff.mp draw
  exact assigned_draw computed i (by simpa using selected)

private theorem refreshed_proposers {f : Fork} {s t : BeaconState preset f}
    {fulu : .fusaka ≤ f} (held : AssignedProposers s)
    (ok : processProposerLookahead s fulu = .ok t) : AssignedProposers t := by
  obtain ⟨epoch, _, rest⟩ := bind_ok_iff.mp ok
  obtain ⟨last, drawn, final⟩ := bind_ok_iff.mp rest
  cases final
  intro _ i member
  obtain ⟨j, inside, rfl⟩ := List.getElem_of_mem member
  simp only [Vector.getElem_toList, Vector.getElem_ofFn]
  split
  · exact held fulu _ (by simp)
  · exact assigned_draw drawn _ (by simp)

private structure CapStep (config : Config) {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop where
  capped : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) →
    ∀ v ∈ t.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset h v
  monotone : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w
  forward : getCurrentEpoch s ≤ getCurrentEpoch t
  forks : f ≤ h
  proposers : h < .glamsterdam → AssignedProposers s → AssignedProposers t
  targets : h < .glamsterdam → AssignedTargets s → AssignedTargets t
  withdrawal : ∀ (i : Nat) (v w : Validator), s.validators.data[i]? = some v →
    t.validators.data[i]? = some w →
    (v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch) ∧
    (0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)

private theorem CapStep.refl {f : Fork} (s : BeaconState preset f) : CapStep config s s := by
  refine ⟨id, fun _ v found => ⟨v, found, UInt64.le_refl _⟩, UInt64.le_refl _,
    Nat.le_refl _, fun _ => id, fun _ => id, ?_⟩
  intro i v w before after
  have eq := Option.some.inj (before.symm.trans after)
  subst w
  exact ⟨fun slashed assigned => ⟨slashed, assigned, UInt64.le_refl _⟩,
    fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : CapStep config s t) (two : CapStep config t u) : CapStep config s u where
  capped := two.capped ∘ one.capped
  monotone i v found := by
    obtain ⟨w, read, first⟩ := one.monotone i v found
    obtain ⟨z, read', second⟩ := two.monotone i w read
    exact ⟨z, read', UInt64.le_trans first second⟩
  forward := UInt64.le_trans one.forward two.forward
  forks := Nat.le_trans one.forks two.forks
  proposers early := two.proposers early ∘ one.proposers (Nat.lt_of_le_of_lt two.forks early)
  targets early := two.targets early ∘ one.targets (Nat.lt_of_le_of_lt two.forks early)
  withdrawal i v z before after := by
    obtain ⟨w, middle, _⟩ := one.monotone i v before
    obtain ⟨kept, newly⟩ := one.withdrawal i v w before middle
    obtain ⟨kept', newly'⟩ := two.withdrawal i w z middle after
    constructor
    · intro slashed assigned
      obtain ⟨flag, assigned', bound⟩ := kept slashed assigned
      obtain ⟨flag', assigned'', bound'⟩ := kept' flag assigned'
      exact ⟨flag', assigned'', UInt64.le_trans bound bound'⟩
    · intro delay unslashed slashed
      cases flag : w.slashed with
      | false =>
        obtain ⟨assigned, bound⟩ := newly' delay flag slashed
        have forward := UInt64.le_iff_toNat_le.mp one.forward
        exact ⟨assigned, by omega⟩
      | true =>
        obtain ⟨assigned, bound⟩ := newly delay unslashed flag
        obtain ⟨_, assigned', bound'⟩ := kept' flag assigned
        exact ⟨assigned', Nat.le_trans bound (UInt64.le_iff_toNat_le.mp bound')⟩

private theorem CapStep.data {f : Fork} {s t : BeaconState preset f}
    (same : t.validators.data = s.validators.data := by rfl)
    (slot : t.slot = s.slot := by rfl)
    (cache : t.proposerLookahead = s.proposerLookahead := by rfl)
    (targets : AssignedTargets s → AssignedTargets t := by
      intro held electra entry member index named
      exact ⟨_, (held electra entry member index named).choose_spec.1,
        (held electra entry member index named).choose_spec.2⟩) :
    CapStep config s t := by
  constructor
  · simpa only [same] using (id : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) → _)
  · intro i v found
    exact ⟨v, same ▸ found, UInt64.le_refl _⟩
  · rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  · exact Nat.le_refl _
  · exact fun _ held => held.transfer (.of_data same) cache
  · exact fun _ => targets
  · intro i v w before after
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨fun slashed assigned => ⟨slashed, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩
private theorem CapStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ s a t, step s a = .ok t → CapStep config s t)
    (ok : xs.foldlM step s = .ok t) : CapStep config s t :=
  foldlM_ok_invariant (CapStep config s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

private theorem CapStep.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (found : getValidatorAt s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidatorAt i w = .ok t)
    (kept : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch := by
      intros; exact ⟨by assumption, by assumption, UInt64.le_refl _⟩)
    (newly : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      intro _ unslashed slashed
      exact Bool.noConfusion (unslashed.symm.trans slashed))
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH := by exact id) : CapStep config s t := by
  constructor
  · intro capped
    exact capped_setValidatorAt capped (bound (capped v (mem_of_getValidatorAt found))) ok
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    have read := getValidatorAt_eq_ok_iff.mp found
    intro j old located
    by_cases eq : j = i
    · subst j
      rw [read, Option.some.injEq] at located
      subst old
      exact ⟨w, by simp [BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set], monotone⟩
    · refine ⟨old, ?_, UInt64.le_refl _⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq] using located
  · obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
    exact UInt64.le_refl _
  · exact Nat.le_refl _
  · intro _ held fulu j member
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    obtain ⟨old, read, active⟩ := held fulu j member
    by_cases eq : j.toNat = i
    · have same := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans
        (eq ▸ read))
      subst old
      refine ⟨w, ?_, assigned active⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨old, ?_, active⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq] using read
  · intro _ held electra entry member index named
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    obtain ⟨old, read, active⟩ := held electra entry member index named
    by_cases eq : index.toNat = i
    · have same := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans
        (eq ▸ read))
      subst old
      refine ⟨w, ?_, assigned active⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨old, ?_, active⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq] using read
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    intro j old final before after
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at after
    split at after
    · rename_i eq
      subst j
      have eq := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans before)
      subst old
      cases after
      exact ⟨kept, newly⟩
    · have eq := Option.some.inj (before.symm.trans after)
      subst final
      exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
        fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v w : Validator} (found : getValidator s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidator i w = .ok t)
    (kept : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch := by
      intros; exact ⟨by assumption, by assumption, UInt64.le_refl _⟩)
    (newly : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      intro _ unslashed slashed
      exact Bool.noConfusion (unslashed.symm.trans slashed))
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH := by exact id) : CapStep config s t :=
  CapStep.setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) monotone bound
    (by rwa [← setValidator_eq_setValidatorAt]) kept newly assigned

private theorem CapStep.increase {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : increaseBalance s i amount = .ok t) : CapStep config s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact CapStep.data rfl

private theorem CapStep.decrease {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : decreaseBalance s i amount = .ok t) : CapStep config s t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  exact CapStep.data rfl

private theorem preKeyCharge_decrease {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {index amount : UInt64}
    (ok : decreaseBalance s index amount = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  have growth := preKeyCharge_balance candidate (s := s)
    (t := s.putBalance index.toNat inside
      (Uint64.saturatingSub s.balances.data[index.toNat] amount)) rfl (fun _ => 0) ?_
  · simpa only [Nat.add_zero] using growth
  · intro j
    by_cases equal : index.toNat = j
    · subst j
      simp only [BeaconState.putBalance,
        Array.getElem?_set, ↓reduceIte, Option.map_some, Option.getD_some,
        Array.getElem?_eq_getElem inside, Uint64.toNat_saturatingSub, Nat.add_zero]
      omega
    · simp only [BeaconState.putBalance,
        Array.getElem?_set, equal, ↓reduceIte, Nat.add_zero, Nat.le_refl]

private theorem preKeyCharge_increase {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {index amount : UInt64}
    (ok : increaseBalance s index amount = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
      if j = index.toNat then amount.toNat else 0 := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  apply preKeyCharge_balance candidate (s := s)
    (t := s.putBalance index.toNat inside (s.balances.data[index.toNat] + amount)) rfl
    (fun j => if j = index.toNat then amount.toNat else 0)
  intro j
  by_cases equal : j = index.toNat
  · subst j
    simp only [BeaconState.putBalance, Array.getElem?_set, ↓reduceIte,
      Option.map_some, Option.getD_some, Array.getElem?_eq_getElem inside,
      UInt64.toNat_add, Nat.mod_eq_of_lt fits, Nat.le_refl]
  · simp only [BeaconState.putBalance, Array.getElem?_set, Ne.symm equal, equal,
      ↓reduceIte, Nat.add_zero, Nat.le_refl]

private theorem preKeyCharge_increase_assigned {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {index amount : UInt64}
    (assigned : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : increaseBalance s index amount = .ok t) :
    ∀ j, preKeyCharge candidate t j = preKeyCharge candidate s j := by
  obtain ⟨inside, _, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  intro j
  by_cases equal : index.toNat = j
  · subst j
    unfold preKeyCharge
    simp only [BeaconState.putBalance]
    split
    · cases found : s.validators.data[index.toNat]? with
      | none => rfl
      | some v => simp only [Option.map_some, assigned v found, ↓reduceIte, Option.getD_some]
    · rfl
  · simp only [preKeyCharge, BeaconState.putBalance, Array.getElem?_set, equal, ↓reduceIte]

private theorem preKeyCharge_consolidations {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (candidate : Nat → Bool) (sources : AssignedTargets s)
    (ok : processPendingConsolidations s electra = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨result, passed, balances, _⟩ := processPendingConsolidations_pass ok
  let R := fun (a b : BeaconState preset f) =>
    a.validators.data = s.validators.data →
      b.validators.data = s.validators.data ∧
        ∀ j, preKeyCharge candidate b j ≤ preKeyCharge candidate a j
  have composed := passPendingConsolidations_of R
    (fun _ same => ⟨same, fun _ => Nat.le_refl _⟩)
    (fun one two same => by
      obtain ⟨middle, first⟩ := one same
      obtain ⟨last, second⟩ := two middle
      exact ⟨last, fun j => (second j).trans (first j)⟩)
    (fun entry => entry ∈ (s.pendingConsolidations electra).data.toList)
    (fun {a lowered raised entry source balance} member _ _ debit credit same => by
      have downRegistry := decreaseBalance_validators debit
      have upRegistry := increaseBalance_validators credit
      refine ⟨(congrArg (·.data) (upRegistry.trans downRegistry)).trans same, ?_⟩
      have assigned : ∀ v, lowered.validators.data[entry.targetIndex.toNat]? = some v →
          v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
        intro v read
        obtain ⟨w, located, active⟩ := sources electra entry member entry.targetIndex (by simp)
        rw [downRegistry, same, located, Option.some.injEq] at read
        subst v
        exact active
      intro j
      rw [preKeyCharge_increase_assigned candidate assigned credit j]
      exact preKeyCharge_decrease candidate debit j)
    (fun _ member => member) passed
  have output := (composed.2 rfl).2
  intro j
  simpa only [preKeyCharge, balances, (composed.2 rfl).1,
    (processPendingConsolidations_kept ok).1] using output j

/-- Record writes compare only the live reserve or its permanent assignment charge. -/
private theorem preKeyCharge_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {i : Nat} {v w : Validator}
    (found : getValidatorAt s i = .ok v) (set : s.setValidatorAt i w = .ok t)
    (effective : w.effectiveBalance = v.effectiveBalance)
    (cap : withdrawalMaxEffectiveBalance preset f w = withdrawalMaxEffectiveBalance preset f v)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH → w.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (reserve : v.activationEpoch = FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH →
      preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j
  by_cases equal : j = i
  · subst j
    have read := getValidatorAt_eq_ok_iff.mp found
    simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, ↓reduceIte, Option.map_some, Option.getD_some, read]
    by_cases chosen : candidate i = true
    · simp only [chosen, ↓reduceIte]
      by_cases before : v.activationEpoch = FAR_FUTURE_EPOCH
      · by_cases after : w.activationEpoch = FAR_FUTURE_EPOCH
        · simp only [before, after, ↓reduceIte, effective, cap, Nat.le_refl]
        · simp only [before, after, ↓reduceIte]
          exact (UInt64.le_iff_toNat_le.mp (reserve before after)).trans (Nat.le_max_left _ _)
      · simp only [before, assigned before, ↓reduceIte, Nat.le_refl]
    · simp only [chosen, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, Ne.symm equal, ↓reduceIte, Nat.le_refl]

private theorem preKeyCharge_setAssigned {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {i : ValidatorIndex} {v w : Validator}
    (found : getValidator s i = .ok v) (set : s.setValidator i w = .ok t)
    (before : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (after : w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∀ j, preKeyCharge candidate t j = preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read := getValidator_eq_ok_iff.mp found
  intro j
  by_cases equal : i.toNat = j
  · subst j
    simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set_self, read, Option.map_some, before, after, ↓reduceIte,
      Option.getD_some]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, equal, ↓reduceIte]

private theorem CapStep.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) := by
  obtain ⟨v, found, unchanged | ⟨unassigned, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact ⟨CapStep.refl _, id, id, fun _ _ => Nat.le_refl _⟩
  · have same := (exitQueue_validators queue).1
    have cache : queued.proposerLookahead = s.proposerLookahead := by
      obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (CapStep.data (congrArg (·.data) same) (frame_exitQueue queue).slot cache
        (by obtain ⟨_, _, rfl⟩ := exitQueue_eq queue; exact id)).trans
        (CapStep.setValidator (v := v)
          (by rw [getValidator_of_validators_eq same]; exact found)
          (by exact UInt64.le_refl _) (by exact id) set
          (fun _ assigned => False.elim (assigned unassigned)))
    · intro held
      have balances : queued.balances = s.balances := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      have middle := held.transfer (congrArg (·.data) same)
        (fun _ _ b _ _ read low => ⟨b, by rw [balances]; exact read, low⟩)
      have foundAt : getValidatorAt queued i.toNat = .ok v := by
        rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]
        exact found
      rw [setValidator_eq_setValidatorAt] at set
      apply middle.setValidatorAt foundAt set
      intro pending
      obtain ⟨_, eligible, unslashed⟩ := held i.toNat v (getValidator_eq_ok_iff.mp found) pending
      exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩
    · intro held witness entry member
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      have queueSame : queued.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      obtain ⟨old, read, active⟩ := held witness entry
        (by simpa [BeaconState.putValidator, queueSame] using member)
      by_cases equal : entry.validatorIndex.toNat = i.toNat
      · have eq := Option.some.inj ((getValidator_eq_ok_iff.mp found).symm.trans (equal ▸ read))
        subst old
        exact ⟨{ v with exitEpoch := epoch, withdrawableEpoch := withdrawal },
          by simp [BeaconState.putValidator,
          Serialization.Ssz.RootedForkList.data_set, equal], active⟩
      · exact ⟨old, by simpa [BeaconState.putValidator,
          Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set,
          (Ne.symm equal), same] using read, active⟩
    · intro candidate j
      have balances : queued.balances = s.balances := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      have step := preKeyCharge_setValidatorAt candidate
        (s := queued) (t := t) (i := i.toNat) (v := v)
        (w := { v with exitEpoch := epoch, withdrawableEpoch := withdrawal })
        (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
        (by rwa [← setValidator_eq_setValidatorAt]) rfl rfl id
        (fun pending assigned => (assigned pending).elim) j
      simpa only [preKeyCharge, same, balances] using step

private theorem CapStep.slash {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s i whistleblower = .ok t) :
    CapStep config s t ∧
      (UnassignedEligibleBalance s →
        (∃ w, s.validators.data[i.toNat]? = some w ∧
          w.activationEpoch ≠ FAR_FUTURE_EPOCH) → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) := by
  obtain ⟨exitedState, v, withdrawal, marked, _, _, slashings, _, _, _, _, last,
    exited, found, summed, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have assigned (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
      v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    obtain ⟨old, read, unchanged | ⟨_, queued, epoch, withdrawable, _, add, written⟩⟩ :=
      initiateValidatorExit_ok exited
    · rw [unchanged.2] at found
      have eq := Except.ok.inj (read.symm.trans found)
      exact eq ▸ unchanged.1
    · obtain ⟨inside, rfl⟩ := setValidator_ok written
      simp only [getValidator, BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set_self,
        Except.ok.injEq] at found
      subst v
      intro far
      have sum := Base.Uint64.addChecked_ok_iff.mp add
      change epoch = FAR_FUTURE_EPOCH at far
      rw [far] at sum
      have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      rw [farNat] at sum
      omega
  have first := (CapStep.exit exited).1.trans
    (CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set
      (fun _ assigned => ⟨rfl, assigned, by
        apply UInt64.le_iff_toNat_le.mpr
        exact (Base.Uint64.toNat_max _ _).symm ▸ Nat.le_max_left _ _⟩)
      (fun delay _ _ => ⟨assigned delay, by
        have sum := Base.Uint64.addChecked_ok_iff.mp summed
        have epoch : getCurrentEpoch exitedState = getCurrentEpoch s := by
          rw [getCurrentEpoch, getCurrentEpoch, (frame_initiateValidatorExit exited).slot]
        change (getCurrentEpoch exitedState).toNat + _ ≤
          (max v.withdrawableEpoch withdrawal).toNat
        rw [epoch, Base.Uint64.toNat_max]
        omega⟩))
  have second := (CapStep.decrease (config := config) lowered).trans
    ((CapStep.increase raised).trans (CapStep.increase paid))
  have total := first.trans ((CapStep.data (s := marked)
    (t := { marked with slashings })).trans second)
  have funding (held : UnassignedEligibleBalance s)
      (active : ∃ w, s.validators.data[i.toNat]? = some w ∧
        w.activationEpoch ≠ FAR_FUTURE_EPOCH) : UnassignedEligibleBalance last := by
    obtain ⟨old, located, assigned⟩ := active
    obtain ⟨afterExit, read, life⟩ :=
      (registryLifecycle_initiateValidatorExit exited).validators i.toNat old located
    have equal := Option.some.inj (read.symm.trans (getValidator_eq_ok_iff.mp found))
    subst afterExit
    have notFar : v.activationEpoch ≠ FAR_FUTURE_EPOCH :=
      (life.activationEpoch assigned) ▸ assigned
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    have funded := ((CapStep.exit exited).2.1 held).setValidatorAt foundAt setAt
      (fun far => (notFar far).elim)
    have markedAssigned : ∀ w, marked.validators.data[i.toNat]? = some w →
        w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      intro w located
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set_self, Option.some.injEq] at located
      subst w
      exact notFar
    have slashingFunded := funded.transfer (t := { marked with slashings }) rfl
      (fun _ _ b _ _ read low => ⟨b, read, low⟩)
    exact ((slashingFunded.decrease markedAssigned lowered).increase raised).increase paid
  have partials (held : AssignedPartials s) : AssignedPartials last := by
    have exitedHeld := (CapStep.exit exited).2.2.1 held
    have markedHeld := exitedHeld.setValidator found set (fun assigned => assigned)
    have slashingHeld : AssignedPartials { marked with slashings } := markedHeld
    exact ((slashingHeld.decrease lowered).increase raised).increase paid
  split
  · exact ⟨total.trans (CapStep.data rfl), (fun held active =>
      (funding held active).transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)), partials⟩
  · exact ⟨total, funding, partials⟩

private theorem preKeyCharge_add {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
      if j = s.validators.data.size then amount.toNat else 0 := by
  obtain ⟨validators, balances⟩ := addValidatorToRegistry_push ok matched
  have sizes : s.balances.data.size = s.validators.data.size := matched
  intro j
  by_cases equal : j = s.validators.data.size
  · subst j
    have funded : (getValidatorFromDeposit preset f key credentials amount).effectiveBalance.toNat ≤
        amount.toNat := by
      change (min (amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT) _).toNat ≤ amount.toNat
      rw [Uint64.toNat_min]
      apply (Nat.min_le_left _ _).trans
      exact UInt64.le_iff_toNat_le.mp (UInt64.sub_le (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
        exact Nat.mod_le _ _))
    simp only [preKeyCharge, validators, balances, Array.getElem?_push,
      sizes, ↓reduceIte, Option.map_some, Option.getD_some]
    split
    · change max (getValidatorFromDeposit preset f key credentials amount).effectiveBalance.toNat
        (min amount.toNat _) ≤ _
      omega
    · omega
  · simp only [preKeyCharge, validators, balances, Array.getElem?_push,
      sizes, equal, ↓reduceIte, Nat.add_zero, Nat.le_refl]

private theorem CapStep.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    CapStep config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) := by
  have data := addValidatorToRegistry_validators_eq_push ok
  have partials : t.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
    unfold addValidatorToRegistry at ok
    split at ok
    · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
        pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
      rfl
    · split at ok <;> cases ok
      rfl
  refine ⟨?_, (fun matched held => held.add matched ok), fun held =>
    held.transfer (.append data) (fun _ _ member => partials ▸ member)⟩
  constructor
  · intro capped v member
    rw [data, Array.mem_push] at member
    rcases member with old | rfl
    · exact capped v old
    · unfold getValidatorFromDeposit
      exact UInt64.le_iff_toNat_le.mpr (by rw [Base.Uint64.toNat_min]; exact Nat.min_le_right _ _)
  · intro i v found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨v, ?_, UInt64.le_refl _⟩
    simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found
  · rw [getCurrentEpoch, getCurrentEpoch, addValidatorToRegistry_slot ok]
    exact UInt64.le_refl _
  · exact Nat.le_refl _
  · have cache : t.proposerLookahead = s.proposerLookahead := by
      unfold addValidatorToRegistry at ok
      split at ok
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
        rfl
      · split at ok
        · cases ok; rfl
        · cases ok
    intro _ held fulu i member
    rw [cache] at member
    obtain ⟨v, found, assigned⟩ := held fulu i member
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨v, by simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found,
      assigned⟩
  · have queue : t.pendingConsolidations = s.pendingConsolidations := by
      unfold addValidatorToRegistry at ok
      split at ok
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
        rfl
      · split at ok <;> cases ok
        rfl
    intro _ held
    exact held.transfer (.append data) (fun _ _ member => queue ▸ member)
  · intro i v w before after
    have inside := (Array.getElem?_eq_some_iff.mp before).1
    have read : t.validators.data[i]? = some v := by
      simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using before
    have eq := Option.some.inj (read.symm.trans after)
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem preKeyCharge_deposit_growth {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {deposit : PendingDeposit} (matched : BalancesMatch s)
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    ∀ j, ((s.balances.data[j]?.map UInt64.toNat).getD 0) ≤
        ((t.balances.data[j]?.map UInt64.toNat).getD 0) ∧
      preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
        (((t.balances.data[j]?.map UInt64.toNat).getD 0) -
          ((s.balances.data[j]?.map UInt64.toNat).getD 0)) := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨index, raised⟩ | ⟨_, added⟩
  · exact fun _ => ⟨Nat.le_refl _, by simp⟩
  · have growth := preKeyCharge_increase candidate raised
    obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    intro j
    have bound := growth j
    by_cases equal : j = index.toNat
    · subst j
      simp only [BeaconState.putBalance, Array.getElem?_set, ↓reduceIte,
        Option.map_some, Option.getD_some, Array.getElem?_eq_getElem inside,
        UInt64.toNat_add, Nat.mod_eq_of_lt fits] at bound ⊢
      exact ⟨Nat.le_add_right _ _, by omega⟩
    · simp only [BeaconState.putBalance, Array.getElem?_set, Ne.symm equal,
        equal, ↓reduceIte, Nat.add_zero] at bound ⊢
      exact ⟨Nat.le_refl _, by simpa using bound⟩
  · have growth := preKeyCharge_add candidate matched added
    obtain ⟨_, balances⟩ := addValidatorToRegistry_push added matched
    have sizes : s.balances.data.size = s.validators.data.size := matched
    intro j
    have bound := growth j
    by_cases equal : j = s.validators.data.size
    · subst j
      simp only [balances, Array.getElem?_push, sizes, ↓reduceIte,
        Array.getElem?_eq_none (by omega : s.balances.data.size ≤ s.validators.data.size),
        Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at bound ⊢
      exact ⟨Nat.zero_le _, by simpa using bound⟩
    · simp only [balances, Array.getElem?_push, sizes, equal, ↓reduceIte,
        Nat.add_zero] at bound ⊢
      exact ⟨Nat.le_refl _, by simpa using bound⟩

private theorem CapStep.deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    CapStep config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact ⟨CapStep.refl _, fun _ => id, id⟩
  · exact ⟨CapStep.increase raised, (fun _ held => held.increase raised),
      fun held => held.increase raised⟩
  · exact CapStep.add added

private theorem CapStep.applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : Consensus.applyDeposit config checks s key credentials amount signature = .ok t) :
    CapStep config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (.pectra ≤ f → BalancesMatch s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact ⟨(CapStep.add added).1.trans (CapStep.data rfl), (fun matched held =>
          ((CapStep.add (config := config) added).2.1 matched held).transfer rfl
            (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
          (CapStep.add (config := config) added).2.2, fun _ matched candidate i => by
            have growth := preKeyCharge_add candidate matched added i
            simpa only [preKeyCharge, UInt64.toNat_zero, ite_self, Nat.add_zero] using growth⟩
      · cases ok
        exact ⟨CapStep.refl _, fun _ => id, id, fun _ _ _ _ => Nat.le_refl _⟩
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact ⟨CapStep.data rfl, (fun _ held => held.transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩)), id, fun _ _ _ _ => Nat.le_refl _⟩
  · obtain ⟨step, funded, partials⟩ := CapStep.deposit ok
    exact ⟨step, funded, partials, fun electra => (by contradiction)⟩

private theorem CapStep.processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    CapStep config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (.pectra ≤ f → BalancesMatch s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact ⟨(CapStep.data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans
      (CapStep.applyDeposit credited).1, (fun matched held =>
        (CapStep.applyDeposit (config := config) credited).2.1 matched
          (held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩))),
      (CapStep.applyDeposit (config := config) credited).2.2.1,
      fun electra matched candidate i =>
        (CapStep.applyDeposit (config := config) credited).2.2.2 electra matched candidate i⟩

private theorem CapStep.registryEntry {f : Fork} {s t : BeaconState preset f}
    {i : Nat} (ok : updateRegistryEntry config s i = .ok t) :
    CapStep config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have preserved : queued.activationEpoch = v.activationEpoch ∧
      (queued.effectiveBalance = v.effectiveBalance ∧
      queued.withdrawalCredentials = v.withdrawalCredentials) ∧
      (queued.slashed = v.slashed ∧ queued.exitEpoch = v.exitEpoch ∧
        queued.withdrawableEpoch = v.withdrawableEpoch) := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    · cases queue; exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  obtain ⟨epoch, same, records⟩ := preserved
  have cap : withdrawalMaxEffectiveBalance preset f queued =
      withdrawalMaxEffectiveBalance preset f v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
      hasCompoundingWithdrawalCredential, same.2]
    rfl
  have first := CapStep.setValidatorAt (config := config) found
    (by rw [cap]; exact UInt64.le_refl _) (by simp only [same.1, cap]; exact id) set
    (by simp only [records.1, records.2.1, records.2.2];
        exact fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩)
    (by intro _ unslashed slashed
        exact Bool.noConfusion (unslashed.symm.trans (records.1.symm.trans slashed)))
    (by rw [epoch]; exact id)
  have funded (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
      (held : UnassignedEligibleBalance s) : UnassignedEligibleBalance marked := by
    apply held.setValidatorAt found set
    intro pending
    have before : v.activationEpoch = FAR_FUTURE_EPOCH := epoch ▸ pending
    obtain ⟨_, eligible, unslashed⟩ := held i v (getValidatorAt_eq_ok_iff.mp found) before
    obtain ⟨effective, _, flags, floor⟩ := queueForActivation_eligibility activation eligible queue
    exact ⟨before, UInt64.le_of_eq effective, floor, flags.trans unslashed⟩
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    obtain ⟨last, retained, _⟩ := CapStep.exit exited
    exact ⟨first.trans last, fun activation held => retained (funded activation held)⟩
  · cases ok; exact ⟨first, funded⟩

private theorem CapStep.activate {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v : Validator} (found : getValidator s i = .ok v)
    (far : v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : activateValidator s i = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨old, read, _, _, set⟩ := ok
  obtain rfl : old = v := Except.ok.inj (read.symm.trans found)
  refine ⟨CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set
    (assigned := fun assigned => (assigned far).elim), ?_⟩
  intro held
  rw [setValidator_eq_setValidatorAt] at set
  apply held.setValidatorAt (by simpa only [getValidator_eq_getValidatorAt] using found) set
  intro _
  obtain ⟨_, eligible, unslashed⟩ := held i.toNat old
    (by simpa only [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] using found) far
  exact ⟨far, UInt64.le_refl _, eligible, unslashed⟩

private theorem CapStep.registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {i : Nat}
    (ok : updateRegistryEntryElectra config epoch s i = .ok t) :
    CapStep config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (UnassignedEligibleBalance s → s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        ∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    refine ⟨CapStep.setValidatorAt found (by exact UInt64.le_refl _)
      (by exact id) set, ?_, (fun held =>
        held.transfer (.setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩)
          (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact fun _ _ => id)), ?_⟩
    · intro activation held
      apply held.setValidatorAt found set
      intro pending
      obtain ⟨_, _, unslashed⟩ := held i v (getValidatorAt_eq_ok_iff.mp found) pending
      refine ⟨pending, UInt64.le_refl _, fun _ => ?_, unslashed⟩
      have queued : isEligibleForActivationQueue preset f v = true := by assumption
      simp only [isEligibleForActivationQueue, Bool.and_eq_true, beq_iff_eq] at queued
      split at queued
      · exact UInt64.le_trans activation (of_decide_eq_true queued.2)
      · exact UInt64.le_of_eq (beq_iff_eq.mp queued.2).symm
    · intro _ _ candidate
      exact preKeyCharge_setValidatorAt candidate found set rfl rfl id
        (fun pending assigned => (assigned pending).elim)
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact ⟨(CapStep.exit exited).1, (fun _ => (CapStep.exit exited).2.1),
      (CapStep.exit (config := config) exited).2.2.1,
      fun _ _ => (CapStep.exit (config := config) exited).2.2.2⟩
  split at ok
  · have set := liftAccessor_ok.mp ok
    refine ⟨CapStep.setValidatorAt found (by exact UInt64.le_refl _) (by exact id) set
      (assigned := fun assigned => (assigned (activationEpoch_of_isEligibleForActivation
        (by assumption))).elim), ?_, (fun held =>
          held.transfer (.setValidatorAt found set
            ⟨fun assigned => (assigned (activationEpoch_of_isEligibleForActivation
              (by assumption))).elim, fun _ => rfl⟩)
            (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact fun _ _ => id)), ?_⟩
    · intro _ held
      apply held.setValidatorAt found set
      intro _
      have pending := activationEpoch_of_isEligibleForActivation (by assumption)
      obtain ⟨_, eligible, unslashed⟩ := held i v (getValidatorAt_eq_ok_iff.mp found) pending
      exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩
    · intro held finite candidate
      have eligible : isEligibleForActivation s v = true := by assumption
      have pending := activationEpoch_of_isEligibleForActivation eligible
      apply preKeyCharge_setValidatorAt candidate found set rfl rfl
        (fun assigned => (assigned pending).elim)
      intro _ _
      apply (held i v (getValidatorAt_eq_ok_iff.mp found) pending).2.1
      have low : v.activationEligibilityEpoch ≤ s.finalizedCheckpoint.epoch := by
        simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq] at eligible
        exact eligible.1
      intro equal
      have strict := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt low finite)
      rw [equal] at strict
      omega
  · cases ok; exact ⟨CapStep.refl _, fun _ => id, id, fun _ _ _ _ => Nat.le_refl _⟩

private theorem CapStep.registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) :
    CapStep config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (.pectra ≤ f → preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        ∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) := by
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (AssignedPartials a → AssignedPartials b) ∧
    (.pectra ≤ f → preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      UnassignedEligibleBalance a → a.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
      ∀ (candidate : Nat → Bool) j, preKeyCharge candidate b j ≤ preKeyCharge candidate a j) ∧
    b.finalizedCheckpoint = a.finalizedCheckpoint
  have refl (a) : R a a :=
    ⟨CapStep.refl a, fun _ => id, id, fun _ _ _ _ _ _ => Nat.le_refl _, rfl⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, (fun activation => two.2.1 activation ∘ one.2.1 activation),
      two.2.2.1 ∘ one.2.2.1,
      (fun electra activation held finite candidate j =>
        (two.2.2.2.1 electra activation (one.2.1 activation held)
          (by rw [one.2.2.2.2]; exact finite) candidate j).trans
          (one.2.2.2.1 electra activation held finite candidate j)),
      two.2.2.2.2.trans one.2.2.2.2⟩
  suffices held : R s t from ⟨held.1, held.2.1, held.2.2.1, held.2.2.2.1⟩
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM_ok_invariant (R s)
      (fun _ _ _ previous edge => trans previous
        ⟨(CapStep.registryElectra edge).1, (CapStep.registryElectra edge).2.1,
          (CapStep.registryElectra edge).2.2.1,
          (fun _ _ => (CapStep.registryElectra edge).2.2.2),
          (frame_updateRegistryEntryElectra edge).finalized⟩) (refl s) ok
  · rename_i notElectra
    simp only [bind_ok_iff] at ok
    obtain ⟨middle, updated, activated⟩ := ok
    have before : f < .glamsterdam :=
      Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
    have small : middle.validators.data.size < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (middle.validators.bound before) (UInt64.toNat_lt _)
    have first : R s middle := foldlM_ok_invariant (R s)
      (fun _ _ _ previous edge => trans previous
        ⟨(CapStep.registryEntry edge).1, (CapStep.registryEntry edge).2,
          (fun _ electra => (notElectra electra).elim),
          (fun electra => (notElectra electra).elim),
          (frame_updateRegistryEntry edge).finalized⟩) (refl s) updated
    refine trans first
      (foldActivateValidator_of_unassigned R refl
        (fun one two => trans one two) (fun found far ok =>
          ⟨(CapStep.activate found far ok).1,
            (fun _ => (CapStep.activate (config := config) found far ok).2),
            (fun _ electra => (notElectra electra).elim),
            (fun electra => (notElectra electra).elim),
            (frame_activateValidator ok).finalized⟩)
        (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
        (fun i member => ?_) activated)
    obtain ⟨position, v, equal, found, eligible⟩ :=
      mem_activationQueue (List.mem_of_mem_take member)
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have exactIndex : i.toNat = position := by
      have fits : position < UInt64.size := by
        change position < 2 ^ 64
        omega
      rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
    exact ⟨v, by simp [getValidator, exactIndex, found],
      activationEpoch_of_isEligibleForActivation eligible⟩

private theorem CapStep.excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra i = .ok t) :
    CapStep config s t ∧
      (UnassignedEligibleBalance s →
        (∀ v, s.validators.data[i.toNat]? = some v →
          v.activationEpoch = FAR_FUTURE_EPOCH →
          v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        UnassignedEligibleBalance t) ∧
      t.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, middle, set, rfl⟩ := ok
    refine ⟨?_, ?_, by obtain ⟨_, rfl⟩ := setBalance_ok set; rfl⟩
    · obtain ⟨_, rfl⟩ := setBalance_ok set
      exact CapStep.data rfl
    · intro held retained
      exact (held.setBalance retained set).transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩)
  · cases ok
    exact ⟨CapStep.refl _, fun held _ => held, rfl⟩

private theorem preKeyCharge_excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex} (candidate : Nat → Bool)
    (ok : queueExcessActiveBalance s electra index = .ok t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i := by
  apply preKeyCharge_notRaised candidate
    (congrArg (·.data) (queueExcessActiveBalance_validators ok))
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨balance, read, ok⟩ := ok
  split at ok
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, middle, set, rfl⟩ := ok
    obtain ⟨inside, rfl⟩ := setBalance_ok set
    intro i amount located
    by_cases equal : index.toNat = i
    · subst i
      simp only [BeaconState.putBalance, Array.getElem?_set_self, Option.some.injEq] at located
      subst amount
      exact ⟨balance, getBalance_eq_ok_iff.mp read, UInt64.le_of_lt above⟩
    · exact ⟨amount, by simpa [BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, equal] using located,
        UInt64.le_refl _⟩
  · cases ok
    exact fun _ amount read => ⟨amount, read, UInt64.le_refl _⟩

private theorem CapStep.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator s electra i = .ok t) :
    CapStep config s t ∧
      (UnassignedEligibleBalance s →
        (∀ v, s.validators.data[i.toNat]? = some v →
          v.activationEpoch ≠ FAR_FUTURE_EPOCH) → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      ((∀ v, s.validators.data[i.toNat]? = some v →
        v.activationEpoch ≠ FAR_FUTURE_EPOCH) → ∀ candidate j,
        preKeyCharge candidate t j ≤ preKeyCharge candidate s j) := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨v, found, middle, set, queued⟩ := ok
  obtain ⟨cap, funding, partials⟩ := CapStep.excess (config := config) queued
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply CapStep.trans (CapStep.setValidator found ?_ ?_ set) cap
    · simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
        getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
        isCompoundingWithdrawalCredential]
      simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
      by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
      · simp only [h]; exact UInt64.le_refl _
      · simp only [h]; exact order
    · intro bound
      apply UInt64.le_trans bound
      simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
        getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
        isCompoundingWithdrawalCredential]
      simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
      by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
      · simp only [h]; exact UInt64.le_refl _
      · simp only [h]; exact order
  · intro held assigned
    have notFar := assigned v (getValidator_eq_ok_iff.mp found)
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    apply funding (held.setValidatorAt foundAt setAt (fun far => (notFar far).elim))
    intro w located pending
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set_self, Option.some.injEq] at located
    subst w
    exact (notFar pending).elim
  · intro held
    exact (held.setValidator found set id).transfer
      (.of_data (congrArg (·.data) (queueExcessActiveBalance_validators queued)))
      (fun _ _ member => by simpa [partials] using member)
  · intro assigned candidate j
    have active := assigned v (getValidator_eq_ok_iff.mp found)
    have charge := preKeyCharge_setAssigned candidate found set active active j
    exact (preKeyCharge_excess candidate queued j).trans (Nat.le_of_eq charge)

private theorem CapStep.blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  obtain ⟨v, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
  have before : hasCompoundingWithdrawalCredential v = false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      BLS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  have after : hasCompoundingWithdrawalCredential
      { v with withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
      false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential,
      executionCredentials_prefix, ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  have cap : withdrawalMaxEffectiveBalance preset f
      { v with withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
      withdrawalMaxEffectiveBalance preset f v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, before, after]
  refine ⟨?_, ?_, (fun held => held.setValidator found set id), ?_⟩
  rotate_left
  · intro held
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    apply held.setValidatorAt foundAt setAt
    intro pending
    obtain ⟨_, eligible, unslashed⟩ := held _ v
      (getValidator_eq_ok_iff.mp found) pending
    exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩
  · intro candidate i
    exact preKeyCharge_setValidatorAt candidate
      (v := v) (w := { v with
        withdrawalCredentials := executionCredentials signed.message.toExecutionAddress })
      (by simpa only [getValidator_eq_getValidatorAt] using found)
      (by simpa only [setValidator_eq_setValidatorAt] using set) rfl cap id
      (fun far assigned => (assigned far).elim) i
  · apply CapStep.setValidator found (UInt64.le_of_eq cap.symm) ?_ set
    simpa only [cap] using (id : v.effectiveBalance ≤
      withdrawalMaxEffectiveBalance preset f v → _)

private theorem CapStep.consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (sourceAssigned : source.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (target : ∃ v, s.validators.data[targetIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, withdrawal, _, marked, set, pending, appended, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  have partials : churned.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churn
    obtain ⟨_, _, _, _, _, _, rest⟩ := churn
    cases rest; rfl
  have charge : ∀ candidate i, preKeyCharge candidate
      { marked with pendingConsolidations := fun _ => pending } i ≤ preKeyCharge candidate s i := by
    intro candidate i
    have step := preKeyCharge_setAssigned candidate read set sourceAssigned sourceAssigned i
    have balances : churned.balances = s.balances := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    simpa only [preKeyCharge, validators, balances] using Nat.le_of_eq step
  refine ⟨?_, ?_, ?_, charge⟩
  rotate_left 2
  · intro held
    have middle := held.transfer (.of_data (congrArg (·.data) validators))
      (fun _ _ member => by simpa [partials] using member)
    exact (middle.setValidator read set id).transfer (.of_data rfl)
      (fun _ _ member => member)
  rotate_left
  · intro held
    have balances : churned.balances = s.balances := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    have middle := held.transfer (congrArg (·.data) validators)
      (fun _ _ b _ _ located low => ⟨b, by rw [balances]; exact located, low⟩)
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    have retained := middle.setValidatorAt
      (by simpa only [getValidator_eq_getValidatorAt] using read) setAt (fun pending => by
        obtain ⟨_, eligible, unslashed⟩ := held sourceIndex.toNat source found pending
        exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩)
    exact retained.transfer rfl (fun _ _ b _ _ located low => ⟨b, located, low⟩)
  have cache : churned.proposerLookahead = s.proposerLookahead := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churn
    obtain ⟨_, _, _, _, _, _, rest⟩ := churn
    cases rest; rfl
  have queue : churned.pendingConsolidations = s.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churn
    obtain ⟨_, _, _, _, _, _, rest⟩ := churn
    cases rest; rfl
  have first := (CapStep.data (config := config) (by rw [validators])
    (frame_computeConsolidationEpochAndUpdateChurn churn).slot cache
    (fun held => held.transfer (.of_data (congrArg (·.data) validators))
      (fun _ _ member => queue ▸ member))).trans
    (CapStep.setValidator read (by exact UInt64.le_refl _) (by exact id) set
      (fun _ assigned => False.elim (assigned far)))
  refine first.trans (CapStep.data rfl rfl rfl ?_)
  intro held witness entry member
  have data := appendWithinLimit_data appended
  change entry ∈ pending.data.toList at member
  rw [data, Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact held witness entry old
  · intro index named
    have located : ∃ v, s.validators.data[index.toNat]? = some v ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at named
      rcases named with rfl | rfl
      · exact ⟨source, found, sourceAssigned⟩
      · exact target
    obtain ⟨v, foundTarget, assigned⟩ := located
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    by_cases eq : index.toNat = sourceIndex.toNat
    · have same := Option.some.inj (found.symm.trans (eq ▸ foundTarget))
      subst v
      refine ⟨{ source with exitEpoch := epoch, withdrawableEpoch := withdrawal }, ?_, assigned⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨v, ?_, assigned⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq, validators] using foundTarget

private theorem CapStep.consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  unfold processConsolidationRequest at ok
  split at ok
  · split at ok
    · rename_i position located
      simp only [bind_ok_iff] at ok
      obtain ⟨index, checked, ok⟩ := ok
      split at ok
      · rename_i valid
        obtain ⟨step, retained, partials, charge⟩ :=
          CapStep.compounding order (liftAccessor_ok.mp ok)
        have assigned : ∀ v, s.validators.data[index.toNat]? = some v →
            v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
          intro v found
          have read := getElem?_toNat_of_ofNatChecked (state := s) checked
          have equal := Option.some.inj (read.symm.trans found)
          subst v
          apply assigned_of_active (epoch := getCurrentEpoch s)
          simp only [isValidSwitchToCompoundingRequest, Bool.and_eq_true] at valid
          exact valid.1.2
        exact ⟨step, (fun held => retained held assigned), partials, charge assigned⟩
      · cases ok; exact ⟨CapStep.refl _, id, id, fun _ _ => Nat.le_refl _⟩
    · cases ok; exact ⟨CapStep.refl _, id, id, fun _ _ => Nat.le_refl _⟩
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact ⟨CapStep.refl _, id, id, fun _ _ => Nat.le_refl _⟩)
    | (refine CapStep.consolidate (getElem?_toNat_of_ofNatChecked (by assumption))
        (by clear ok; simp_all)
        (assigned_of_active (epoch := getCurrentEpoch s) (by clear ok; simp_all)) ?_ ok
       refine ⟨_, getElem?_toNat_of_ofNatChecked (by assumption), ?_⟩
       apply assigned_of_active (epoch := getCurrentEpoch s)
       clear ok; simp_all)

private theorem CapStep.partialWithdrawal {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra i v amount owed = .ok t) :
    CapStep config s t ∧
      (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s →
        (∃ w, s.validators.data[i.toNat]? = some w ∧
          w.activationEpoch ≠ FAR_FUTURE_EPOCH) → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨middle, _⟩, churned, _, _, pending, appended, rfl⟩ := ok
    have validators := (computeExitEpochAndUpdateChurn_earliest churned).2.1
    have queue : middle.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churned
      obtain ⟨_, _, _, _, _, _, rest⟩ := churned
      cases rest; rfl
    have balances : middle.balances = s.balances := by
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churned
      obtain ⟨_, _, _, _, _, _, rest⟩ := churned
      cases rest; rfl
    refine ⟨?_, ?_, ?_, fun candidate i => Nat.le_of_eq
      (preKeyCharge_same candidate (congrArg (·.data) validators) balances i)⟩
    · exact CapStep.data (by rw [validators])
        (frame_computeExitEpochAndUpdateChurn churned).slot
        (by
          simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
            Except.ok.injEq] at churned
          obtain ⟨_, _, _, _, _, _, rest⟩ := churned
          cases rest; rfl)
        (by
          simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
            Except.ok.injEq] at churned
          obtain ⟨_, _, _, _, _, _, rest⟩ := churned
          cases rest; exact id)
    · intro held
      apply held.transfer (congrArg (·.data) validators)
      intro j w b found far read low
      have balances : middle.balances = s.balances := by
        simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at churned
        obtain ⟨_, _, _, _, _, _, rest⟩ := churned
        cases rest; rfl
      exact ⟨b, by simpa [balances] using read, low⟩
    · intro held assigned witness entry member
      change entry ∈ pending.data.toList at member
      rw [appendWithinLimit_data appended, Array.toList_push,
        List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · obtain ⟨w, read, active⟩ := held witness entry (by simpa [queue] using old)
        exact ⟨w, by simpa [validators] using read, active⟩
      · obtain ⟨w, read, active⟩ := assigned
        exact ⟨w, by simpa [validators] using read, active⟩
  · cases ok; exact ⟨CapStep.refl _, id, fun held _ => held, fun _ _ => Nat.le_refl _⟩

private theorem CapStep.withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact ⟨CapStep.refl _, id, id, fun _ _ => Nat.le_refl _⟩)
    | (have step := CapStep.exit (liftAccessor_ok.mp ok)
       exact ⟨step.1, step.2.1, step.2.2.1, step.2.2.2⟩)
    | (obtain ⟨step, funded, retained, charge⟩ := CapStep.partialWithdrawal ok
       rename_i noRoom candidate position located checkedResult index checked credentials
         acceptedResult allowed accepted yes owedResult owed owedOk isPartial
       refine ⟨step, funded, (fun held => retained held ?_), charge⟩
       have read := getElem?_toNat_of_ofNatChecked (by assumption)
       refine ⟨_, read, ?_⟩
       apply assigned_of_active (epoch := getCurrentEpoch s)
       have acceptedTrue : canRequest config s s.validators.data[position] = .ok true :=
         yes ▸ accepted
       unfold canRequest at acceptedTrue
       dsimp only at acceptedTrue
       split at acceptedTrue
       · cases acceptedTrue
       · rename_i active
         have both := (not_or.mp (by simpa only [Bool.or_eq_true] using active)).1
         simpa using both)

private theorem CapStep.depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact ⟨CapStep.data rfl, fun held => held.transfer rfl
    (fun _ _ b _ _ read low => ⟨b, read, low⟩), id, fun _ _ => Nat.le_refl _⟩

private theorem CapStep.requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processExecutionRequests config s body electra = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (AssignedPartials a → AssignedPartials b) ∧
    (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i)
  have refl (a) : R a a := ⟨CapStep.refl a, id, id, fun _ _ => Nat.le_refl _⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, two.2.1 ∘ one.2.1, two.2.2.1 ∘ one.2.2.1,
      fun candidate i => (two.2.2.2 candidate i).trans (one.2.2.2 candidate i)⟩
  have fold {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (kept : ∀ a x b, step a x = .ok b → R a b)
      {a b : BeaconState preset f} {xs : List α} (ok : xs.foldlM step a = .ok b) : R a b :=
    foldlM_ok_invariant (R a)
      (fun _ _ _ previous computed => trans previous (kept _ _ _ computed)) (refl a) ok
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  exact trans (fold (fun _ _ _ => CapStep.depositRequest) deposits)
    (trans (fold (fun _ _ _ => CapStep.withdrawalRequest) withdrawals)
      (fold (fun _ _ _ => CapStep.consolidationRequest order) consolidations))

private theorem AssignedProposers.selected {f : Fork} {s : BeaconState preset f}
    (held : AssignedProposers s) {proposer : ValidatorIndex}
    (ok : getBeaconProposerIndex s = .ok proposer) :
    ∃ v, s.validators.data[proposer.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  unfold getBeaconProposerIndex at ok
  split at ok
  · rename_i fulu
    split at ok
    · cases ok
    · cases ok
      exact held fulu _ (by apply List.getElem_mem)
  · obtain ⟨seed, _, rest⟩ := bind_ok_iff.mp ok
    obtain ⟨active, checked, drawn⟩ := bind_ok_iff.mp rest
    obtain ⟨v, found, live⟩ :=
      (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp
        (List.mem_toArray.mp (mem_of_computeProposerIndex drawn))
    exact ⟨v, found, assigned_of_active live⟩

private theorem preKeyCharge_slash {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (candidate : Nat → Bool) (proposers : AssignedProposers s)
    (early : f < .glamsterdam)
    (ok : slashValidator config s index none = .ok t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i := by
  obtain ⟨exited, validator, withdrawal, marked, _, _, slashings, lowered, proposer,
    reward, raised, last, exitOk, found, _, set, _, _, _, debit, chosen, _, credit,
    paid, result⟩ := slashValidator_ok ok
  have markCharge := preKeyCharge_setValidatorAt candidate
    (v := validator) (w := { validator with
      slashed := true
      withdrawableEpoch := max validator.withdrawableEpoch withdrawal })
    (by simpa only [getValidator_eq_getValidatorAt] using found)
    (by simpa only [setValidator_eq_setValidatorAt] using set) rfl rfl id
    (fun far assigned => (assigned far).elim)
  have exitedProposers := (CapStep.exit exitOk).1.proposers early proposers
  have markedProposers : AssignedProposers marked := exitedProposers.transfer
    (.setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩) (by
      obtain ⟨_, rfl⟩ := setValidator_ok set
      rfl)
  have loweredProposers : AssignedProposers lowered :=
    (CapStep.decrease (config := config) debit).proposers early markedProposers
  have assigned : ∀ v, lowered.validators.data[proposer.toNat]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro v read
    obtain ⟨w, named, active⟩ := loweredProposers.selected chosen
    obtain rfl := Option.some.inj (named.symm.trans read)
    exact active
  have first := preKeyCharge_increase_assigned candidate assigned credit
  have second := preKeyCharge_increase_assigned candidate (by
    intro v read
    apply assigned v
    simpa only [increaseBalance_validators credit, Option.getD_none] using read) paid
  rw [result]
  simp only [show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early, ↓reduceDIte]
  intro i
  have down := preKeyCharge_decrease candidate debit i
  have markedCharge := markCharge i
  have exitedCharge := (CapStep.exit exitOk).2.2.2 candidate i
  rw [second i, first i]
  exact down.trans (markedCharge.trans exitedCharge)

private theorem CapStep.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam → AssignedProposers s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, slashable, _, _, _, _, slashed⟩ := ok
  obtain ⟨step, retained, partials⟩ := CapStep.slash slashed
  exact ⟨step, (fun held => retained held
    ⟨v, getValidator_eq_ok_iff.mp found, assigned_of_slashable slashable⟩), partials,
    fun early proposers candidate => preKeyCharge_slash candidate proposers early slashed⟩

private theorem CapStep.attesterSlashing_of {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (R : BeaconState preset f → BeaconState preset f → Prop)
    (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (each : ∀ {a b : BeaconState preset f} {index : ValidatorIndex},
      slashValidator config a index none = .ok b → R a b)
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧ R s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun (step : BeaconState preset f × Bool) =>
    CapStep config s step.1 ∧
    (UnassignedEligibleBalance s → UnassignedEligibleBalance step.1) ∧
    (AssignedPartials s → AssignedPartials step.1) ∧ R s step.1) ?_
    ⟨CapStep.refl s, id, id, refl s⟩ folded
  intro step i next previous ok
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    obtain ⟨step, retained, partials⟩ := CapStep.slash slashed
    exact ⟨previous.1.trans step, (fun held => retained (previous.2.1 held)
      ⟨v, getValidator_eq_ok_iff.mp found, assigned_of_slashable (by assumption)⟩),
      partials ∘ previous.2.2.1, trans previous.2.2.2 (each slashed)⟩
  · cases ok; exact previous

private theorem CapStep.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam → AssignedProposers s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  have whole := CapStep.attesterSlashing_of
    (fun a b => CapStep config a b ∧
      (f < .glamsterdam → AssignedProposers a → ∀ candidate i,
        preKeyCharge candidate b i ≤ preKeyCharge candidate a i))
    (fun a => ⟨CapStep.refl a, fun _ _ _ _ => Nat.le_refl _⟩)
    (fun one two => ⟨one.1.trans two.1,
      fun early proposers candidate i =>
        (two.2 early (one.1.proposers early proposers) candidate i).trans
          (one.2 early proposers candidate i)⟩)
    (fun slashed => ⟨(CapStep.slash slashed).1,
      fun early proposers candidate => preKeyCharge_slash candidate proposers early slashed⟩) ok
  exact ⟨whole.1, whole.2.1, whole.2.2.1, whole.2.2.2.2⟩

private theorem preKeyCharge_attestation {f : Fork} {s t : BeaconState preset f}
    {parentSlot : Slot} {attestation : Attestation preset f}
    (altair : .altair ≤ f) (candidate : Nat → Bool) (held : UnassignedEligibleBalance s)
    (proposers : AssignedProposers s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  have registry := congrArg (·.data) (processAttestation_registry ok).1
  rw [processAttestation_of_altair altair] at ok
  obtain ⟨_, _, _, proposer, _, _, _, chosen, _, _, _, balances⟩ :=
    processAttestationAltair_balance ok
  apply preKeyCharge_of_live_balances candidate registry held
  intro i v found pending balance read
  obtain ⟨final, located, value⟩ := balances i balance read
  have different : proposer.toNat ≠ i := by
    intro equal
    obtain ⟨w, named, assigned⟩ := proposers.selected chosen
    rw [equal, found, Option.some.injEq] at named
    subst w
    exact assigned pending
  have same : final = balance := by
    apply UInt64.toNat_inj.mp
    simpa only [different, ↓reduceIte, Nat.add_zero] using value
  exact same ▸ located

private theorem preKeyCharge_sync {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (candidate : Nat → Bool) (held : UnassignedEligibleBalance s)
    (assigned : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v → v.pubkey = key →
        v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (proposers : AssignedProposers s)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  obtain ⟨_, _, members, proposer, _, _, mapped, chosen, balances⟩ :=
    processSyncAggregate_balance ok
  obtain ⟨_, shape⟩ := processSyncAggregate_eq ok
  apply preKeyCharge_of_live_balances candidate (by rw [shape]) held
  intro i v found pending balance read
  obtain ⟨final, located, value⟩ := balances i balance read
  have apart : ∀ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1.toNat ≠ i := by
    intro member inside
    apply sync_member_not_unassigned mapped found
      (fun key keyed equal => assigned key keyed i v found equal.symm pending)
    exact (List.of_mem_zip (by simpa only [Array.toList_zip] using inside)).1
  have same : final = balance := by
    apply UInt64.toNat_inj.mp
    rw [value]
    apply List.foldlRecOn (motive := fun n : Nat => n = balance.toNat)
      (members.zip aggregate.syncCommitteeBits.bits.toArray).toList _ rfl
    intro amount previous member inside
    by_cases signed : member.2 = true
    · have different : proposer.toNat ≠ i := by
        intro equal
        obtain ⟨w, named, active⟩ := proposers.selected (chosen ⟨member, inside, signed⟩)
        rw [equal, found, Option.some.injEq] at named
        subst w
        exact active pending
      simpa only [signed, ↓reduceIte, apart member inside, different, Nat.add_zero] using previous
    · simpa only [signed, Bool.false_eq_true, ↓reduceIte, apart member inside] using previous
  exact same ▸ located

private theorem CapStep.withdrawals {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (early : f < .glamsterdam)
    (ok : processWithdrawals s capella payload = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      t.validators.data = s.validators.data ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  obtain ⟨expected, _, _, applied⟩ := processWithdrawals_expected early ok
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (AssignedPartials a → AssignedPartials b) ∧ b.validators.data = a.validators.data ∧
    (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i)
  have kept : R s t := by
    apply applyExpectedWithdrawals_of_updates R
      (fun a => ⟨CapStep.refl a, id, rfl, fun _ _ => Nat.le_refl _⟩)
      (fun one two => ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
        two.2.2.1.trans one.2.2.1,
        fun candidate i => (two.2.2.2 candidate i).trans (one.2.2.2 candidate i)⟩)
      (fun withdrawn => by
        have lowered := withdrawn
        simp only [applyWithdrawal, show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early,
          false_and, ↓reduceDIte] at lowered
        rw [applyWithdrawal_eq withdrawn]
        exact ⟨CapStep.data rfl, id, rfl, fun candidate i => by
          simpa only [preKeyCharge, decreaseBalance_validators lowered] using
            preKeyCharge_decrease candidate lowered i⟩) _ _ _ _ _
      (fun _ electra count => ⟨CapStep.data rfl, fun held => held.drop electra count, rfl,
        fun _ _ => Nat.le_refl _⟩)
      applied
    all_goals exact fun _ _ => ⟨CapStep.data rfl, id, rfl, fun _ _ => Nat.le_refl _⟩
  exact ⟨kept.1, kept.2.1, fun activation exits partials before capped held =>
    held.withdrawals_of_provenance activation exits partials kept.2.2.1 before capped ok,
    kept.2.2⟩

private theorem CapStep.execution {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {body : BeaconBlockBody preset f}
    {bellatrix : .bellatrix ≤ f}
    (early : f < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      t.validators.data = s.validators.data ∧ t.slot = s.slot ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (AssignedPartials a → AssignedPartials b) ∧ b.validators.data = a.validators.data ∧
    b.slot = a.slot ∧
    (ActivationExitOrder a → ExitsOrdered a → AssignedPartials a →
      getCurrentEpoch a < FAR_FUTURE_EPOCH → EffectiveBalancesCapped a →
      UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i)
  have refl (a) : R a a :=
    ⟨CapStep.refl a, id, rfl, rfl, (fun _ _ _ _ _ => id), fun _ _ => Nat.le_refl _⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c := by
    refine ⟨one.1.trans two.1, two.2.1 ∘ one.2.1, two.2.2.1.trans one.2.2.1,
      two.2.2.2.1.trans one.2.2.2.1, ?_,
      fun candidate i => (two.2.2.2.2.2 candidate i).trans (one.2.2.2.2.2 candidate i)⟩
    intro activation exits partials before capped held
    apply two.2.2.2.2.1
    · simpa only [ActivationExitOrder, one.2.2.1] using activation
    · simpa only [ExitsOrdered, one.2.2.1] using exits
    · exact one.2.1 partials
    · simpa only [getCurrentEpoch, one.2.2.2.1] using before
    · exact one.1.capped capped
    · exact one.2.2.2.2.1 activation exits partials before capped held
  have whole : R s t := by
    apply processBlockExecution_of R refl (fun one two => trans one two)
      (fun paid => by
        obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
        exact ⟨CapStep.data rfl, id, rfl, rfl, (fun _ _ _ _ _ held =>
          held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
          fun _ _ => Nat.le_refl _⟩)
      (fun _ => (Nat.not_le_of_lt early ‹.glamsterdam ≤ f›).elim)
      (fun withdrawn => by
        obtain ⟨step, partials, funded, same, charge⟩ := CapStep.withdrawals early withdrawn
        exact ⟨step, partials, same, (frame_processWithdrawals withdrawn).slot, funded, charge⟩) ok
  exact ⟨whole.1, whole.2.1, whole.2.2.2.2.1, whole.2.2.1, whole.2.2.2.1,
    whole.2.2.2.2.2⟩

private theorem CapStep.block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) :
    CapStep config s t ∧
      (f < .glamsterdam → AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam → ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH) →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (.pectra ≤ f → f < .glamsterdam → AssignedProposers s →
        ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH) →
        UnassignedEligibleBalance s → ∀ candidate i,
          preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  have same {a b : BeaconState preset f} (validators : b.validators = a.validators)
      (slot : b.slot = a.slot) (cache : b.proposerLookahead = a.proposerLookahead)
      (queue : b.pendingConsolidations = a.pendingConsolidations) :
      CapStep config a b := CapStep.data (congrArg (·.data) validators) slot cache
        (fun held => held.transfer (.of_data (congrArg (·.data) validators))
          (fun _ _ member => queue ▸ member))
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have framed {a b : BeaconState preset f} (frame : BlockFrame a b)
      (validators : b.validators = a.validators)
      (cache : f < .glamsterdam → b.proposerLookahead = a.proposerLookahead)
      (queue : f < .glamsterdam → b.pendingConsolidations = a.pendingConsolidations) :
      CapStep config a b := by
    have data := congrArg (·.data) validators
    refine {
      capped := fun held v member => held v (data ▸ member)
      monotone := fun _ v found => ⟨v, data ▸ found, UInt64.le_refl _⟩
      forward := by rw [getCurrentEpoch, getCurrentEpoch, frame.slot]; exact UInt64.le_refl _
      forks := Nat.le_refl _
      proposers := fun early held =>
        held.transfer (.of_data (congrArg (·.data) validators)) (cache early)
      targets := fun early held => held.transfer (.of_data (congrArg (·.data) validators))
        (fun _ _ member => queue early ▸ member)
      withdrawal := ?_ }
    intro i v w before after
    rw [data, before, Option.some.injEq] at after
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (f < .glamsterdam → b.validators.data = a.validators.data ∧ b.slot = a.slot ∧
      (AssignedPartials a → AssignedPartials b) ∧
      b.currentSyncCommittee = a.currentSyncCommittee ∧
      (ActivationExitOrder a → ExitsOrdered a → AssignedPartials a →
        getCurrentEpoch a < FAR_FUTURE_EPOCH → EffectiveBalancesCapped a →
        UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
      (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i))
  have refl (a) : R a a :=
    ⟨CapStep.refl a, fun _ => ⟨rfl, rfl, id, rfl, (fun _ _ _ _ _ => id),
      fun _ _ => Nat.le_refl _⟩⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c := by
    refine ⟨one.1.trans two.1, fun early => ?_⟩
    obtain ⟨registry, slot, partials, committee, funded, charge⟩ := one.2 early
    obtain ⟨registry', slot', partials', committee', funded', charge'⟩ := two.2 early
    refine ⟨registry'.trans registry, slot'.trans slot, partials' ∘ partials,
      committee'.trans committee, ?_, fun candidate i => (charge' candidate i).trans
        (charge candidate i)⟩
    intro activation exits queue before capped held
    apply funded'
    · simpa only [ActivationExitOrder, registry] using activation
    · simpa only [ExitsOrdered, registry] using exits
    · exact partials queue
    · simpa only [getCurrentEpoch, slot] using before
    · exact one.1.capped capped
    · exact funded activation exits queue before capped held
  have plain {a b : BeaconState preset f} (step : CapStep config a b)
      (registry : b.validators.data = a.validators.data) (slot : b.slot = a.slot)
      (balances : b.balances = a.balances)
      (partials : b.pendingPartialWithdrawals = a.pendingPartialWithdrawals)
      (committee : b.currentSyncCommittee = a.currentSyncCommittee := by rfl) : R a b :=
    ⟨step, fun _ => ⟨registry, slot,
      fun held => held.transfer (.of_data registry) (fun _ _ member => partials ▸ member),
      committee,
      fun _ _ _ _ _ held => held.transfer registry
        (fun _ _ amount _ _ read low => ⟨amount, by rw [balances]; exact read, low⟩),
      fun candidate i => Nat.le_of_eq (by simp only [preKeyCharge, registry, balances])⟩⟩
  -- From Gloas, a block first applies the payload of the parent, which runs the validator requests.
  have head : R s input :=
    started.step_of R refl (fun one two => trans one two)
      (fun gloas paid => ⟨processParentExecutionPayload_step_of (CapStep config) CapStep.refl
        (fun one two => one.trans two) (fun frame validators => framed frame validators
          (fun early => (Nat.not_le_of_lt early gloas).elim)
          (fun early => (Nat.not_le_of_lt early gloas).elim))
        (fun ok => (CapStep.withdrawalRequest ok).1)
        (fun ok => (CapStep.consolidationRequest order ok).1) paid,
        fun early => (Nat.not_le_of_lt early gloas).elim⟩)
      (fun headed => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
        exact plain (same rfl rfl rfl rfl) rfl rfl rfl rfl)
      (fun _ executed => by
        by_cases early : f < .glamsterdam
        · obtain ⟨step, partials, funded, registry, slot, charge⟩ :=
            CapStep.execution early executed
          exact ⟨step, fun _ => ⟨registry, slot, partials,
            funext fun altair => processBlockExecution_currentSyncCommittee altair executed,
            funded, charge⟩⟩
        · exact ⟨framed (frame_processBlockExecution executed)
            (processBlockExecution_validators executed)
            (fun _ => processBlockExecution_proposerLookahead executed)
            (fun before => SamePendingQueue.blockExecution before executed),
            fun before => (early before).elim⟩)
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact plain (same rfl rfl rfl rfl) rfl rfl rfl rfl)
      (fun _ voted => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest]
        exact plain (same rfl rfl rfl rfl) rfl rfl rfl rfl)
  let P := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (f < .glamsterdam → AssignedPartials a → AssignedPartials b) ∧
    (BalancesMatch a → BalancesMatch b) ∧
    (BalancesMatch a → UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (.pectra ≤ f → f < .glamsterdam → AssignedProposers a → BalancesMatch a →
      UnassignedEligibleBalance a → ∀ candidate i,
        preKeyCharge candidate b i ≤ preKeyCharge candidate a i)
  have reflP (a) : P a a :=
    ⟨CapStep.refl a, fun _ => id, id, fun _ => id,
      fun _ _ _ _ _ _ _ => Nat.le_refl _⟩
  have transP {a b c} (one : P a b) (two : P b c) : P a c :=
    ⟨one.1.trans two.1, fun early => two.2.1 early ∘ one.2.1 early,
      two.2.2.1 ∘ one.2.2.1,
      (fun matched => two.2.2.2.1 (one.2.2.1 matched) ∘ one.2.2.2.1 matched),
      fun electra early proposers matched funded candidate i =>
        (two.2.2.2.2 electra early (one.1.proposers early proposers)
          (one.2.2.1 matched) (one.2.2.2.1 matched funded) candidate i).trans
          (one.2.2.2.2 electra early proposers matched funded candidate i)⟩
  have foldP {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (each : ∀ a x b, step a x = .ok b → P a b)
      {a b : BeaconState preset f} {items : List α} (ok : items.foldlM step a = .ok b) :
      P a b := (foldlM_ok_steps P reflP (fun one two => transP one two) each ok).1
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of P reflP (fun one two => transP one two)
      (fun ok => ⟨(CapStep.processDeposit ok).1,
        fun _ => (CapStep.processDeposit (config := config) ok).2.2.1,
        (frame_processDeposit ok).balancesMatch, (CapStep.processDeposit ok).2.1,
        fun electra _ _ matched _ =>
          (CapStep.processDeposit (config := config) ok).2.2.2 electra matched⟩)
      (fun exited => ⟨(CapStep.exit (processVoluntaryExit_initiates exited)).1,
        fun _ => (CapStep.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.2.1,
        (frame_processVoluntaryExit exited).balancesMatch,
        fun _ => (CapStep.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.1,
        fun _ _ _ _ _ => (CapStep.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.2.2⟩)
      (fun ok => ⟨(CapStep.blsChange ok).1,
        fun _ => (CapStep.blsChange (config := config) ok).2.2.1,
        (frame_processBlsToExecutionChange ok).balancesMatch,
        fun _ => (CapStep.blsChange (config := config) ok).2.1,
        fun _ _ _ _ _ => (CapStep.blsChange (config := config) ok).2.2.2⟩)
      (fun ok => ⟨(CapStep.requests order ok).1,
        fun _ => (CapStep.requests (config := config) order ok).2.2.1,
        (frame_processExecutionRequests ok).balancesMatch,
        fun _ => (CapStep.requests (config := config) order ok).2.1,
        fun _ _ _ _ _ => (CapStep.requests (config := config) order ok).2.2.2⟩)
      (fun attested => by
        rw [processPayloadAttestation_eq attested]
        exact reflP _) operated
  have tail : CapStep config last t ∧
      (f < .glamsterdam → AssignedPartials last → AssignedPartials t) := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact ⟨same rfl rfl rfl rfl, fun _ => id⟩
    · cases synced
      exact ⟨CapStep.refl _, fun _ => id⟩
  have operations : P input last :=
    transP (foldP (fun _ _ _ ok => ⟨(CapStep.proposerSlashing ok).1,
      fun _ => (CapStep.proposerSlashing (config := config) ok).2.2.1,
      (frame_processProposerSlashing ok).balancesMatch,
      fun _ => (CapStep.proposerSlashing (config := config) ok).2.1,
      fun _ early proposers _ _ =>
        (CapStep.proposerSlashing (config := config) ok).2.2.2 early proposers⟩) proposersOk) <|
    transP (foldP (fun _ _ _ ok => ⟨(CapStep.attesterSlashing ok).1,
      fun _ => (CapStep.attesterSlashing (config := config) ok).2.2.1,
      (frame_processAttesterSlashing ok).balancesMatch,
      fun _ => (CapStep.attesterSlashing (config := config) ok).2.1,
      fun _ early proposers _ _ =>
        (CapStep.attesterSlashing (config := config) ok).2.2.2 early proposers⟩) slashingsOk) <|
    transP (foldP (fun _ _ _ attested => ⟨same (processAttestation_registry attested).1
      (frame_processAttestation attested).slot (processAttestation_proposerLookahead attested)
      (by
        by_cases electra : .pectra ≤ f
        · exact SamePendingQueue.attestation electra attested
        · funext witness; exact (electra witness).elim),
      fun _ held => held.attestation attested,
      (frame_processAttestation attested).balancesMatch,
      (fun _ held => held.attestation attested),
      fun electra _ proposers _ held candidate i => Nat.le_of_eq
        (preKeyCharge_attestation (Nat.le_trans (by decide) electra)
          candidate held proposers attested i)⟩) attestedOk) rest
  refine ⟨head.1.trans (operations.1.trans tail.1), fun early =>
    tail.2 early ∘ operations.2.1 early ∘ (head.2 early).2.2.1, ?_, ?_⟩
  rotate_left
  · intro electra early proposers activation exits partials finite capped matched unique
      assigned held
    obtain ⟨registry, slot, _, committee, funded, charge⟩ := head.2 early
    have inputFunded := funded activation exits partials finite capped held
    have inputMatched := (frame_operationsInput started).balancesMatch matched
    have lastFunded := operations.2.2.2.1 inputMatched inputFunded
    have operatedCharge := operations.2.2.2.2 electra early
      (head.1.proposers early proposers) inputMatched inputFunded
    have inputAssigned (altair : .altair ≤ f) :
        ∀ key ∈ (input.currentSyncCommittee altair).value.pubkeys.toList,
          ∃ (i : Nat) (v : Validator), input.validators.data[i]? = some v ∧ v.pubkey = key ∧
            v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      simpa only [committee, registry] using assigned altair
    intro candidate i
    apply Nat.le_trans ?_ ((operatedCharge candidate i).trans (charge candidate i))
    split at synced
    · apply Nat.le_of_eq (preKeyCharge_sync candidate lastFunded ?_
        (operations.1.proposers early (head.1.proposers early proposers)) synced i)
      exact assigned_of_key_provenance
        ((frame_processOperations operated).pubkeysDistinct
          ((frame_operationsInput started).pubkeysDistinct unique))
        (processOperations_syncCommittee_activation_assigned _ (inputAssigned _) operated)
    · cases synced; exact Nat.le_refl _
  intro early activation exits partials finite capped matched unique assigned held
  obtain ⟨registry, slot, _, committee, funded, _⟩ := head.2 early
  have inputFunded := funded activation exits partials finite capped held
  have lastFunded := operations.2.2.2.1 (frame_operationsInput started |>.balancesMatch matched)
    inputFunded
  have inputAssigned (altair : .altair ≤ f) :
      ∀ key ∈ (input.currentSyncCommittee altair).value.pubkeys.toList,
        ∃ (i : Nat) (v : Validator), input.validators.data[i]? = some v ∧ v.pubkey = key ∧
          v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    simpa only [committee, registry] using assigned altair
  split at synced
  · exact lastFunded.sync_of_provenance
      ((frame_processOperations operated).pubkeysDistinct
        ((frame_operationsInput started).pubkeysDistinct unique))
      (processOperations_syncCommittee_activation_assigned _ (inputAssigned _) operated) synced
  · cases synced
    exact lastFunded

private theorem CapStep.pending {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t) :
    CapStep config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (BalancesMatch s → ∀ (candidate : Nat → Bool) j,
        preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
          (((t.balances.data[j]?.map UInt64.toNat).getD 0) -
            ((s.balances.data[j]?.map UInt64.toNat).getD 0))) := by
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (BalancesMatch a → BalancesMatch b) ∧
    (BalancesMatch a → UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (AssignedPartials a → AssignedPartials b) ∧
    (BalancesMatch a → ∀ (candidate : Nat → Bool) j,
      ((a.balances.data[j]?.map UInt64.toNat).getD 0) ≤
          ((b.balances.data[j]?.map UInt64.toNat).getD 0) ∧
        preKeyCharge candidate b j ≤ preKeyCharge candidate a j +
          (((b.balances.data[j]?.map UInt64.toNat).getD 0) -
            ((a.balances.data[j]?.map UInt64.toNat).getD 0)))
  have refl (a) : R a a :=
    ⟨CapStep.refl a, id, fun _ => id, id, fun _ _ _ => ⟨Nat.le_refl _, by simp⟩⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c := by
    refine ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
      (fun matched held => two.2.2.1 (one.2.1 matched) (one.2.2.1 matched held)),
      two.2.2.2.1 ∘ one.2.2.2.1, ?_⟩
    intro matched candidate j
    obtain ⟨first, paid⟩ := one.2.2.2.2 matched candidate j
    obtain ⟨second, paid'⟩ := two.2.2.2.2 (one.2.1 matched) candidate j
    exact ⟨first.trans second, by omega⟩
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → R state result.1.state :=
    fun ok => passPendingDeposits_of R refl (fun one two => trans one two)
      (fun credited => ⟨(CapStep.deposit credited).1,
        (applyPendingDeposit_kept credited).1, (CapStep.deposit credited).2.1,
        (CapStep.deposit (config := config) credited).2.2,
        fun matched candidate => preKeyCharge_deposit_growth candidate matched credited⟩) ok
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals
    have passed := pass ‹_›
    exact ⟨passed.1.trans (CapStep.data rfl), (fun matched held =>
      (passed.2.2.1 matched held).transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
      passed.2.2.2.1, fun matched candidate j => (passed.2.2.2.2 matched candidate j).2⟩

/-- Rounding an effective balance cannot raise the capped Pre potential. -/
private theorem pre_effective_le {largest balance effective result : Gwei}
    (ok : updatedEffectiveBalance preset largest balance effective = .ok result) :
    max result.toNat (min balance.toNat largest.toNat) ≤
      max effective.toNat (min balance.toNat largest.toNat) := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · exact Nat.le_refl _
  · have remainder : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    have rounded := UInt64.le_iff_toNat_le.mp (UInt64.sub_le remainder)
    simp only [Uint64.toNat_min]
    omega

private theorem preKeyCharge_effective {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {i : Nat} {v : Validator} {balance result : Gwei}
    (found : getValidatorAt s i = .ok v) (read : getBalanceAt s i = .ok balance)
    (updated : updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v)
      balance v.effectiveBalance = .ok result)
    (set : s.setValidatorAt i { v with effectiveBalance := result } = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j
  by_cases equal : j = i
  · subst j
    have atIndex := getValidatorAt_eq_ok_iff.mp found
    have atBalance := getBalanceAt_eq_ok_iff.mp read
    simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, ↓reduceIte, Option.map_some, Option.getD_some, atIndex, atBalance]
    by_cases chosen : candidate i = true
    · simp only [chosen, ↓reduceIte]
      split
      · exact pre_effective_le updated
      · exact Nat.le_refl _
    · simp only [chosen, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, Ne.symm equal, ↓reduceIte, Nat.le_refl]

private theorem CapStep.effective {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) :
    CapStep config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) := by
  unfold processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun t => CapStep config s t ∧
    (preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
      (∀ {h : Fork} (v : Validator),
        preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
      UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
    (AssignedPartials s → AssignedPartials t) ∧
    (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j)) ?_
    ⟨CapStep.refl s, fun _ _ => id, id, fun _ _ => Nat.le_refl _⟩ ok
  intro middle i final previous ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, balance, read, next, changed, set⟩ := ok
  refine ⟨?_, ?_, (fun held => (previous.2.2.1 held).transfer
    (.setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩)
    (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact fun _ _ => id)),
    fun candidate j => (preKeyCharge_effective candidate found read changed set j).trans
      (previous.2.2.2 candidate j)⟩
  · refine previous.1.trans (CapStep.setValidatorAt found ?_ ?_ set)
    · exact UInt64.le_refl _
    · intro bound
      have potential := pre_effective_le changed
      have capped := UInt64.le_iff_toNat_le.mp bound
      apply UInt64.le_iff_toNat_le.mpr
      change next.toNat ≤ (withdrawalMaxEffectiveBalance preset f v).toNat
      omega
  · intro aligned caps held
    exact (previous.2.1 aligned caps held).effective aligned (fun v _ => caps v)
      found read changed set

private theorem epochEdge_frame {f : Fork} {a b : BeaconState preset f} {k : EpochStage}
    (edge : EpochStage.Edge config checks k a b) (other : k ≠ .justification) :
    Frame a b := by
  by_cases ordinary : k ≠ .payments ∧ k ≠ .participation ∧ k ≠ .pendingDeposits
  · exact mutatorEpochFrameLaws.toEpochStepLaws.epochEdge
      ⟨other, ordinary⟩ (EpochStage.action_cases.mpr edge) |>.toFrame
  cases k
  case payments =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (frame_processBuilderPendingPayments edge).toFrame
    · cases edge; exact Frame.refl _
  case participation =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · cases edge; exact (frame_processParticipationFlagUpdates _ _).toFrame
    · exact (frame_processParticipationRecordUpdates edge).toFrame
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact (frame_processPendingDeposits edge).toFrame
    · cases edge; exact Frame.refl _
  all_goals exact (ordinary ⟨nofun, nofun, nofun⟩).elim

private theorem preKeyCharge_epochEdge {f : Fork} {a b : BeaconState preset f} {k : EpochStage}
    (edge : EpochStage.Edge config checks k a b) (other : k ≠ .pendingDeposits)
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (held : UnassignedEligibleBalance a) (targets : AssignedTargets a)
    (finite : a.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH)
    (candidate : Nat → Bool) :
    ∀ i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i := by
  cases k
  case registry => exact (CapStep.registry edge).2.2.2 electra activation held finite candidate
  case effectiveBalances => exact (CapStep.effective (config := config) edge).2.2.2 candidate
  case rewards =>
    exact fun i => Nat.le_of_eq (preKeyCharge_rewardsAltair candidate
      (Nat.le_trans (by decide) electra) early held edge i)
  case slashings => exact preKeyCharge_slashings candidate edge
  case pendingDeposits => exact (other rfl).elim
  case pendingConsolidations =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact preKeyCharge_consolidations candidate targets edge
  all_goals
    obtain ⟨validators, balances, _⟩ :=
      edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    exact fun i => Nat.le_of_eq
      (preKeyCharge_same candidate (congrArg (·.data) validators) balances i)

/-- Each epoch stage keeps caps and the indexed assignment provenance. -/
private theorem CapStep.epochEdge {f : Fork} {a b : BeaconState preset f} {k : EpochStage}
    (edge : EpochStage.Edge config checks k a b) :
    CapStep config a b ∧ (AssignedPartials a → AssignedPartials b) := by
  cases k
  case registry => exact ⟨(CapStep.registry edge).1, (CapStep.registry edge).2.2.1⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact ⟨(CapStep.pending edge).1, (CapStep.pending edge).2.2.1⟩
    · exact edge ▸ ⟨CapStep.refl _, id⟩
  case effectiveBalances =>
    exact ⟨(CapStep.effective edge).1, (CapStep.effective (config := config) edge).2.2.1⟩
  case rewards =>
    refine ⟨CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [EpochStage.Edge] at edge; rw [processRewardsAndPenalties_frame edge])
      (by rw [processRewardsAndPenalties_frame edge])
      (fun held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩)))
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member)), ?_⟩
    intro held
    apply held.transfer edge.registryLifecycle
    intro electra entry member
    rw [processRewardsAndPenalties_frame edge] at member
    exact member
  case slashings =>
    refine ⟨CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [EpochStage.Edge] at edge; rw [processSlashings_frame edge])
      (by rw [processSlashings_frame edge])
      (fun held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩)))
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member)), ?_⟩
    intro held
    apply held.transfer edge.registryLifecycle
    intro electra entry member
    rw [processSlashings_frame edge] at member
    exact member
  case pendingConsolidations =>
    have targets : AssignedTargets a → AssignedTargets b := by
      intro held
      simp only [EpochStage.Edge] at edge
      split at edge
      · intro electra entry member index named
        obtain ⟨result, passed, _, queue⟩ := processPendingConsolidations_pass edge
        rw [queue] at member
        have before : entry ∈ (a.pendingConsolidations electra).data.toList :=
          List.mem_of_mem_drop member
        obtain ⟨v, found, assigned⟩ := held electra entry before index named
        exact ⟨v, by rw [(processPendingConsolidations_kept edge).1]; exact found, assigned⟩
      · cases edge; exact held
    refine ⟨CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      ?_ ?_ targets, ?_⟩
    · simp only [EpochStage.Edge] at edge
      split at edge
      · exact (frame_processPendingConsolidations edge).slot
      · exact edge ▸ rfl
    · simp only [EpochStage.Edge] at edge
      split at edge
      · exact processPendingConsolidations_proposerLookahead edge
      · exact edge ▸ rfl
    · intro held
      apply held.transfer edge.registryLifecycle
      simp only [EpochStage.Edge] at edge
      split at edge
      · rw [processPendingConsolidations_pendingPartialWithdrawals edge]
        exact fun _ _ => id
      · cases edge; exact fun _ _ => id
  case proposerLookahead =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · have assigned := fun held => refreshed_proposers held edge
      simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨{ CapStep.data (s := a) (t := a) with
        proposers := fun _ => assigned }, id⟩
    · exact edge ▸ ⟨CapStep.refl _, id⟩
  all_goals
    suffices fields : b.proposerLookahead = a.proposerLookahead ∧
        b.pendingPartialWithdrawals = a.pendingPartialWithdrawals by
      exact ⟨CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2 fields.1
      (fun held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩)))
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member)),
        fun held => held.transfer edge.registryLifecycle (by rw [fields.2]; exact fun _ _ => id)⟩
    constructor <;>
    simp only [EpochStage.Edge] at edge
    all_goals
    first
    | (obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
       · rfl
       · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
         rw [← rest])
    | (split at edge
       · rw [processInactivityUpdates_frame edge]
       · exact edge ▸ rfl)
    | (split at edge
       · rw [processEth1DataReset_frame edge]
       · exact edge ▸ rfl)
    | (split at edge
       · rw [processBuilderPendingPayments_eq edge]
       · exact edge ▸ rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge; rfl)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge; rfl)
    | (split at edge
       · unfold processHistoricalSummariesUpdate at edge
         simp only [bind, Except.bind, pure, Except.pure] at edge
         repeat' (split at edge <;> try cases edge)
         all_goals rfl
       · unfold processHistoricalRootsUpdate at edge
         split at edge
         · cases edge
         simp only [bind_ok_iff, liftAccessor_ok] at edge
         obtain ⟨_, _, edge⟩ := edge
         split at edge
         · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at edge
           obtain ⟨_, _, _, _, rfl⟩ := edge
           rfl
         · cases edge; rfl)
    | (split at edge
       · subst edge; rfl
       · obtain ⟨u, computed, _, _, restored⟩ :=
           processParticipationRecordUpdates_eq (state := a) (Nat.lt_of_not_le (by assumption))
         obtain rfl := Except.ok.inj (computed.symm.trans edge)
         first
         | exact congrArg (·.proposerLookahead) restored
         | exact congrArg (·.pendingPartialWithdrawals) restored)
    | (split at edge
       · unfold processSyncCommitteeUpdates at edge
         simp only [bind, Except.bind, pure, Except.pure] at edge
         repeat' (split at edge <;> try cases edge)
         all_goals rfl
       · exact edge ▸ rfl)
    | (split at edge
       · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
         obtain ⟨_, _, _, _, rfl⟩ := edge; rfl
       · exact edge ▸ rfl)

private theorem CapStep.epoch_of {f : Fork} {s t : BeaconState preset f}
    (Q : List EpochStage → BeaconState preset f → Prop)
    (start : Q EpochStage.epochStages s)
    (each : ∀ k rest a b, EpochStage.Edge config checks k a b →
      CapStep config s a → (BalancesMatch s → BalancesMatch a) →
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance a) →
      Q (k :: rest) a → Q rest b)
    (ok : processEpoch config checks s = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧ Q [] t := by
  let R := fun (a b : BeaconState preset f) => CapStep config a b ∧
    (BalancesMatch a → BalancesMatch b) ∧
    (AssignedPartials a → AssignedPartials b) ∧
    (f < .glamsterdam →
      preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
      (∀ {h : Fork} (v : Validator),
        preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
      BalancesMatch a → AssignedTargets a →
      UnassignedEligibleBalance a → UnassignedEligibleBalance b)
  have refl (a) : R a a := ⟨CapStep.refl a, id, id, fun _ _ _ _ _ _ => id⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
      two.2.2.1 ∘ one.2.2.1,
      fun early activation aligned caps matched targets held =>
        two.2.2.2 early activation aligned caps (one.2.1 matched)
          (one.1.targets early targets)
          (one.2.2.2 early activation aligned caps matched targets held)⟩
  have step k {a b : BeaconState preset f}
      (edge : EpochStage.Edge config checks k a b) : R a b := by
      refine ⟨(CapStep.epochEdge edge).1, ?_, (CapStep.epochEdge edge).2, ?_⟩
      · by_cases justification : k = .justification
        · subst k
          obtain ⟨validators, balances, _⟩ :=
            edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          simpa only [BalancesMatch, validators, balances] using (id : BalancesMatch a → _)
        · exact (epochEdge_frame edge justification).balancesMatch
      · intro early activation aligned caps matched targets held
        cases k
        case registry => exact (CapStep.registry edge).2.1 activation held
        case rewards => exact held.rewards early edge
        case slashings => exact held.slashings early edge
        case effectiveBalances =>
          exact (CapStep.effective (config := config) edge).2.1 aligned caps held
        case pendingDeposits | pendingConsolidations =>
          simp only [EpochStage.Edge] at edge
          split at edge
          · first
            | exact (CapStep.pending edge).2.1 matched held
            | exact held.consolidations targets edge
          · cases edge; exact held
        all_goals
          obtain ⟨validators, balances, _⟩ :=
            edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          exact held.transfer (congrArg (·.data) validators)
            (fun _ _ b _ _ read low => ⟨b, by rw [balances]; exact read, low⟩)
  have whole := (processEpoch_trace ok).induction_on
    (fun rest b => R s b ∧ Q rest b) ⟨refl s, start⟩ (by
      intro k rest a b computed held
      have edge := EpochStage.action_cases.mp computed
      exact ⟨trans held.1 (step k edge),
        each k rest a b edge held.1.1 held.1.2.1 held.1.2.2.2 held.2⟩)
  exact ⟨whole.1.1, whole.1.2.2.1, whole.1.2.2.2, whole.2⟩

private theorem CapStep.epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) := by
  have whole := CapStep.epoch_of (fun _ _ => True) True.intro
    (fun _ _ _ _ _ _ _ _ _ => True.intro) ok
  exact ⟨whole.1, whole.2.1, whole.2.2.1⟩

private theorem CapStep.slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) := by
  have later := (runKept_advanceSlot ok).later
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨step, partials, funded⟩ := CapStep.epoch advance
    refine ⟨⟨step.capped, step.monotone, later, step.forks, step.proposers, step.targets,
      step.withdrawal⟩, partials, ?_⟩
    intro early activation aligned caps matched targets held
    exact (funded early activation aligned caps matched targets held).transfer rfl
      (fun _ _ b _ _ read low => ⟨b, read, low⟩)
  · cases advance
    exact ⟨⟨id, fun _ v found => ⟨v, found, UInt64.le_refl _⟩, later,
      Nat.le_refl _, fun _ => id, fun _ => id, (CapStep.refl s).withdrawal⟩,
      id,
      fun _ _ _ _ _ _ held => held.transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩)⟩

private theorem CapStep.carry {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h) (slot : t.slot = s.slot := by rfl)
    (proposers : h < .glamsterdam → AssignedProposers s → AssignedProposers t := by
      intro _ _
      unfold AssignedProposers
      intro fulu
      have impossible := fulu
      simp +decide at impossible)
    (targets : h < .glamsterdam → AssignedTargets s → AssignedTargets t := by
      intro _ held
      unfold AssignedTargets
      intro electra entry member
      first
      | (have impossible := electra; simp +decide at impossible)
      | simp [carryFields] at member) : CapStep config s t where
  capped capped v member := UInt64.le_trans (capped v (same ▸ member))
    (withdrawalMaxEffectiveBalance_mono activation compounding forks id)
  monotone _i v found := ⟨v, same ▸ found,
    withdrawalMaxEffectiveBalance_mono activation compounding forks id⟩
  forward := by
    rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  forks := forks
  proposers := proposers
  targets := targets
  withdrawal i v w before after := by
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.preActivation {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queuePreActivation s electra i = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      t.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  refine ⟨?_, ?_, ?_⟩
  · have changed := CapStep.setValidator (config := config) (v := v)
      (by simpa only [getValidator, BeaconState.putBalance] using found)
      (by exact UInt64.le_refl _) (by intro _; exact UInt64.zero_le) validator
    exact ⟨changed.capped, changed.monotone, changed.forward, changed.forks, changed.proposers,
      changed.targets, changed.withdrawal⟩
  · intro held
    obtain ⟨_, rfl⟩ := setValidator_ok validator
    intro j w located pending
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at located
    split at located
    · rename_i equal
      subst j
      cases located
      have before := getValidator_eq_ok_iff.mp found
      have unslashed := (held i.toNat v before pending).2.2
      exact ⟨⟨0, by simp [BeaconState.putValidator, BeaconState.putBalance], UInt64.le_refl _⟩,
        fun impossible => (impossible rfl).elim, unslashed⟩
    · rename_i different
      obtain ⟨⟨b, read, low⟩, eligible, unslashed⟩ := held j w located pending
      refine ⟨⟨b, ?_, low⟩, eligible, unslashed⟩
      simpa [BeaconState.putValidator, BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, different] using read
  · obtain ⟨_, rfl⟩ := setValidator_ok validator
    rfl

private theorem CapStep.upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) :
    CapStep config s.state t.val.state ∧
      (t.val.fork < .glamsterdam → AssignedPartials s.state → AssignedPartials t.val.state) ∧
      (t.val.fork < .glamsterdam →
        (∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        UnassignedEligibleBalance s.state → UnassignedEligibleBalance t.val.state) := by
  have frame := upgradeFrame_upgradeNext ok
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact ⟨CapStep.carry (upgradeToAltair_spec upgraded).1
      activation compounding (by change Fork.phase0 ≤ .altair; decide) frame.slot,
      fun _ _ impossible => (by decide : ¬ Fork.pectra ≤ .altair) impossible |>.elim,
      fun _ _ held => held.transfer (upgradeToAltair_spec upgraded).1
        (fun _ _ b _ _ read low => ⟨b, by
          rw [(upgradeToAltair_spec upgraded).2.1]; exact read, low⟩)⟩
  · subst ok
    exact ⟨CapStep.carry rfl activation compounding (by change Fork.altair ≤ .bellatrix; decide),
      fun _ _ impossible => (by decide : ¬ Fork.pectra ≤ .bellatrix) impossible |>.elim,
      fun _ _ held => held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)⟩
  · subst ok
    exact ⟨CapStep.carry rfl activation compounding (by change Fork.bellatrix ≤ .shapella; decide),
      fun _ _ impossible => (by decide : ¬ Fork.pectra ≤ .shapella) impossible |>.elim,
      fun _ _ held => held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)⟩
  · subst ok
    exact ⟨CapStep.carry rfl activation compounding (by change Fork.shapella ≤ .dencun; decide),
      fun _ _ impossible => (by decide : ¬ Fork.pectra ≤ .dencun) impossible |>.elim,
      fun _ _ held => held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)⟩
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    let R := fun (a b : BeaconState preset .pectra) => CapStep config a b ∧
      ((∀ v ∈ a.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        ∀ v ∈ b.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) ∧
      ((∀ v ∈ a.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
      b.pendingPartialWithdrawals = a.pendingPartialWithdrawals
    have trans {a b c} (one : R a b) (two : R b c) : R a c :=
      ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
        (fun bound => two.2.2.1 (one.2.1 bound) ∘ one.2.2.1 bound),
        two.2.2.2.trans one.2.2.2⟩
    have queuedStep : R _ _ := foldlM_ok_invariant (R _)
      (fun a index b previous computed => trans previous (by
        refine ⟨(CapStep.preActivation computed).1, ?_,
          (fun _ => (CapStep.preActivation (config := config) computed).2.1),
          (CapStep.preActivation (config := config) computed).2.2⟩
        intro bound
        simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at computed
        obtain ⟨v, _, _, _, _, _, middle, balance, last, validator, rfl⟩ := computed
        obtain ⟨_, rfl⟩ := setBalance_ok balance
        obtain ⟨inside, rfl⟩ := setValidator_ok validator
        intro w member
        rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
        · exact bound w old
        · exact UInt64.zero_le))
      ⟨CapStep.refl _, id, (fun _ => id), rfl⟩ queued
    have compoundedStep : R _ _ := foldlM_ok_invariant (R _)
      (fun a index b previous computed => trans previous (by
        unfold queueCompoundingExcess at computed
        split at computed
        · split at computed
          · have excess := liftAccessor_ok.mp computed
            exact ⟨(CapStep.excess excess).1,
              fun bound w member => bound w
                (by rw [queueExcessActiveBalance_validators excess] at member; exact member),
              (fun bound held => (CapStep.excess (config := config) excess).2.1 held
                (fun v found _ => bound v (Array.mem_of_getElem? found))),
              (CapStep.excess (config := config) excess).2.2⟩
          · cases computed; exact ⟨CapStep.refl _, id, (fun _ => id), rfl⟩
        · cases computed; exact ⟨CapStep.refl _, id, (fun _ => id), rfl⟩))
      ⟨CapStep.refl _, id, (fun _ => id), rfl⟩ compounded
    refine ⟨(CapStep.carry (s := state) (by rfl)
      activation compounding (by decide) (by rfl)
      (by intro _ _ fulu; exact (by decide : ¬ Fork.fusaka ≤ .pectra) fulu |>.elim)
      (by intro _ _ electra entry member
          simp [carryFields, show ¬ Fork.pectra ≤ .dencun by decide] at member)).trans
        (queuedStep.1.trans compoundedStep.1), ?_, ?_⟩
    · intro _ _ electra entry member
      rw [compoundedStep.2.2.2, queuedStep.2.2.2] at member
      simp [carryFields, show ¬ Fork.pectra ≤ .dencun by decide] at member
    · intro _ capped held
      have bound : ∀ v ∈ state.validators.data,
          v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE := by
        intro v member
        exact UInt64.le_trans (capped v member) (by
          simpa [withdrawalMaxEffectiveBalance, show ¬ Fork.pectra ≤ .dencun by decide]
            using activation)
      exact compoundedStep.2.2.1 (queuedStep.2.1 bound)
        (queuedStep.2.2.1 bound (held.transfer rfl
          (fun _ _ b _ _ read low => ⟨b, read, low⟩)))
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine ⟨CapStep.carry (upgradeToFulu_spec upgraded).1
      activation compounding (by change Fork.pectra ≤ .fusaka; decide) frame.slot
      (fun _ _ => ?_) (fun _ held => ?_), ?_, fun _ _ held =>
        held.transfer (upgradeToFulu_spec upgraded).1
          (fun _ _ b _ _ read low => ⟨b, by
            rw [(upgradeToFulu_spec upgraded).2.1]; exact read, low⟩)⟩
    · obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      intro _ i member
      exact initialized_proposers (liftAccessor_ok.mp initialized) i member
    · obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      intro electra entry member
      simpa [carryFields, carryRooted] using
        held (show Fork.pectra ≤ .pectra by decide) entry
          (by simpa [carryFields, carryList] using member)
    · intro _ held electra entry member
      obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      simpa [carryFields, carryRooted] using
        held (show Fork.pectra ≤ .pectra by decide) entry
          (by simpa [carryFields, carryList] using member)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact ⟨CapStep.carry (upgradeToGloas_spec upgraded).1
      activation compounding (by change Fork.fusaka ≤ .glamsterdam; decide) frame.slot
      (fun early => (Nat.lt_irrefl _ early).elim)
      (fun early => (Nat.lt_irrefl _ early).elim),
      (fun early => (Nat.lt_irrefl _ early).elim),
      fun early => (Nat.lt_irrefl _ early).elim⟩
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact ⟨CapStep.carry (upgradeHezeFields_lists state).1
      activation compounding (by change Fork.glamsterdam ≤ .hegota; decide) frame.slot
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim)
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim),
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim),
      fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim⟩

private theorem preKeyCharge_upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t)
    (electra : .pectra ≤ s.fork) (early : t.val.fork < .glamsterdam)
    (candidate : Nat → Bool) :
    ∀ i, preKeyCharge candidate t.val.state i = preKeyCharge candidate s.state i := by
  obtain ⟨fork, state⟩ := s
  cases fork <;> try simp +decide at electra
  all_goals
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨validators, balances, _⟩ := upgradeToFulu_spec upgraded
    intro i
    simp only [preKeyCharge, validators, balances, withdrawalMaxEffectiveBalance,
      show Fork.pectra ≤ .pectra from by decide,
      show Fork.pectra ≤ .fusaka from by decide]
  · obtain ⟨_, _, rfl⟩ := ok
    exact (Nat.lt_irrefl _ early).elim
  · obtain ⟨_, _, rfl⟩ := ok
    exact ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim

private theorem CapStep.upgrades {s t : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processUpgrades config checks s = .ok t) :
    CapStep config s.state t.state ∧
      (t.fork < .glamsterdam → AssignedPartials s.state → AssignedPartials t.state) ∧
      (t.fork < .glamsterdam →
        (∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        UnassignedEligibleBalance s.state → UnassignedEligibleBalance t.state) ∧
      (.pectra ≤ s.fork → t.fork < .glamsterdam → ∀ candidate i,
        preKeyCharge candidate t.state i = preKeyCharge candidate s.state i) := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    obtain ⟨first, partials, funded⟩ := CapStep.upgrade activation compounding nextOk
    obtain ⟨last, assigned, retained, charge⟩ := ih next rest
    exact ⟨first.trans last,
      (fun early => assigned early ∘ partials (Nat.lt_of_le_of_lt last.forks early)),
      (fun early capped => retained early (first.capped capped) ∘
        funded (Nat.lt_of_le_of_lt last.forks early) capped),
      fun electra early candidate i =>
        (charge (Nat.le_trans electra first.forks) early candidate i).trans
          (preKeyCharge_upgrade nextOk electra (Nat.lt_of_le_of_lt last.forks early)
            candidate i)⟩
  | case2 s notDue =>
    cases ok
    exact ⟨CapStep.refl _, fun _ => id, (fun _ _ => id), fun _ _ _ _ => rfl⟩

private theorem CapStep.step {s t : ForkedBeaconState preset}
    (step : Step config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) :
    CapStep config s.state t.state ∧ (AssignedPartials s.state → AssignedPartials t.state) := by
  cases step with
  | block engine signed due ok =>
    have block := CapStep.block compounding (applySignedBlock_ok ok).2.1
    exact ⟨block.1, block.2.1 early⟩
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨first, partials, _⟩ := CapStep.slot slotOk
    obtain ⟨last, assigned, _⟩ := CapStep.upgrades activation compounding upgrades
    exact ⟨first.trans last, assigned early ∘ partials⟩

private theorem CapStep.run_of {g s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (shared : Run config checks g s)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (base : CapStep config g.state s.state ∧
      (AssignedPartials g.state → AssignedPartials s.state) ∧
      (Invariant g.state → Invariant s.state) ∧
      (Genesis (config := config) (checks := checks) g → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch s.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance s.state))
    (Q : ∀ {a}, Run config checks s a → Prop) (initial : Q .nil)
    (next : ∀ {a b}, (pre : Run config checks s a) → (step : Step config checks a b) →
      b.fork < .glamsterdam → CapStep config g.state a.state →
      (AssignedPartials g.state → AssignedPartials a.state) →
      (Invariant g.state → Invariant a.state) →
      (Genesis (config := config) (checks := checks) g → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch a.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance a.state) →
      Q pre → Q (pre.snoc step))
    (early : t.fork < .glamsterdam) :
    (CapStep config g.state t.state ∧ (AssignedPartials g.state → AssignedPartials t.state) ∧
      (Invariant g.state → Invariant t.state) ∧
      (Genesis (config := config) (checks := checks) g → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch t.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance t.state)) ∧
      Q run := by
  induction run with
  | nil => exact ⟨base, initial⟩
  | snoc pre step ih =>
    obtain ⟨⟨first, assigned, invariant, funded⟩, carried⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    refine ⟨?_, next pre step early first assigned invariant funded carried⟩
    obtain ⟨last, partials⟩ := CapStep.step step activation compounding early
    refine ⟨first.trans last, partials ∘ assigned, ?_, ?_⟩
    · intro held
      cases step with
      | block _ _ _ ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant
          (invariant held)
      | slot ok => exact (advanceSlotAcross_invariant (invariant held) ok).1
    · intro genesis aligned finite
      have finiteBefore := UInt64.lt_of_le_of_lt last.forward finite
      have held := funded genesis aligned finiteBefore
      have genesisWitness := genesis
      obtain ⟨_, _, _, initialized⟩ := genesisWitness
      have initialPartials : AssignedPartials g.state := by
        intro electra
        have before := (initializeBeaconStateFromEth1_ok initialized).1
        exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) electra)).elim
      have initialTargets : AssignedTargets g.state := by
        intro electra
        have before := (initializeBeaconStateFromEth1_ok initialized).1
        exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) electra)).elim
      have valid := invariant (initializeBeaconStateFromEth1_invariant initialized).2
      have capped := first.capped genesis.effectiveBalance_capped
      have targets := first.targets (Nat.lt_of_le_of_lt last.forks early) initialTargets
      have assigned := assigned initialPartials
      have caps {h : Fork} (v : Validator) :
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v := by
        unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        split
        · split
          · exact UInt64.le_trans activation compounding
          · exact activation
        · exact UInt64.le_refl _
      cases step with
      | block engine signed due ok =>
        exact (CapStep.block compounding (applySignedBlock_ok ok).2.1).2.2.1 early
          ((shared.append pre).activationExitOrder genesis) valid.exitsOrdered assigned
          finiteBefore capped
          valid.balancesMatch
          (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
            (shared.append pre).chainSteps).2
          (fun altair => ((shared.append pre).syncCommittee_activation_assigned genesis altair).1)
          held
      | slot ok =>
        obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
        obtain ⟨slotStep, _, slotFunded⟩ := CapStep.slot slotOk
        obtain ⟨upStep, _, upFunded, _⟩ := CapStep.upgrades activation compounding upgrades
        exact upFunded early (slotStep.capped capped)
          (slotFunded (Nat.lt_of_le_of_lt upStep.forks early) activation aligned.1
            caps valid.balancesMatch targets held)

private theorem CapStep.run {s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) :
    CapStep config s.state t.state ∧ (AssignedPartials s.state → AssignedPartials t.state) ∧
      (Invariant s.state → Invariant t.state) ∧
      (Genesis (config := config) (checks := checks) s → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch t.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance t.state) :=
  (CapStep.run_of run .nil activation compounding
    ⟨CapStep.refl _, id, id, fun genesis _ _ => genesis_unassigned_eligible_balance genesis⟩
    (fun _ => True) trivial
    (fun _ _ _ _ _ _ _ _ => trivial) early).1

private theorem run_unassigned_eligible_balance {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    UnassignedEligibleBalance x.state :=
  (CapStep.run run activation compounding early).2.2.2 genesis aligned finite

private theorem preKeyCharge_assigned {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (lifecycle : RegistryLifecycle s t)
    (candidate : Nat → Bool) {i : Nat} {v : Validator}
    (found : s.validators.data[i]? = some v)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    preKeyCharge candidate t i = preKeyCharge candidate s i := by
  obtain ⟨w, read, kept⟩ := lifecycle.validators i v found
  have later : w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [kept.activationEpoch assigned]
    exact assigned
  simp only [preKeyCharge, found, read, Option.map_some, assigned, later,
    ↓reduceIte, Option.getD_some]

private theorem preKeyCharge_pending {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (candidate : Nat → Bool)
    (ok : processPendingDeposits config checks s electra = .ok t)
    (matched : BalancesMatch s) (activation : ActivationExitOrder s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (budget : Nat)
    (funded : (∑ i ∈ Finset.range t.validators.data.size,
      if (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false then 0
      else ((t.balances.data[i]?.map UInt64.toNat).getD 0) -
        ((s.balances.data[i]?.map UInt64.toNat).getD 0)) +
      (t.depositBalanceToConsume electra).toNat ≤ budget) :
    (∑ i ∈ Finset.range t.validators.data.size, preKeyCharge candidate t i) +
      (t.depositBalanceToConsume electra).toNat ≤
        (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) + budget := by
  have growth := (CapStep.pending (config := config) ok).2.2.2 matched candidate
  have each (i : Nat) : preKeyCharge candidate t i ≤ preKeyCharge candidate s i +
      if (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false then 0
      else ((t.balances.data[i]?.map UInt64.toNat).getD 0) -
        ((s.balances.data[i]?.map UInt64.toNat).getD 0) := by
    split
    · rename_i withdrawn
      cases found : s.validators.data[i]? with
      | none => simp [found] at withdrawn
      | some v =>
        have member := Array.mem_of_getElem? found
        have first := UInt64.le_iff_toNat_le.mp (activation v member)
        have second := UInt64.le_iff_toNat_le.mp (exits v member)
        have last := UInt64.lt_iff_toNat_lt.mp finite
        have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
          simp only [found, Option.map_some, Option.getD_some, decide_eq_true_eq] at withdrawn
          intro far
          rw [far] at first
          omega
        rw [preKeyCharge_assigned (registryLifecycle_processPendingDeposits ok)
          candidate found assigned]
        omega
    · exact growth i
  have sums := Finset.sum_le_sum (s := Finset.range t.validators.data.size)
    (fun i _ => each i)
  rw [Finset.sum_add_distrib] at sums
  rw [preKeyCharge_sum_range candidate s (registryLifecycle_processPendingDeposits ok).size_le]
    at sums
  omega

private theorem preKeyCharge_epoch {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (aligned : MaxEffectiveBalancesAligned preset)
    (caps : ∀ {h : Fork} (v : Validator),
      preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v)
    (valid : Invariant s) (ordered : ActivationExitOrder s) (targets : AssignedTargets s)
    (held : UnassignedEligibleBalance s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (candidate : Nat → Bool)
    (pendingLaw : ∀ (a b : BeaconState preset f),
      processPendingDeposits config checks a electra = .ok b → BalancesMatch a →
      (∑ i ∈ Finset.range b.validators.data.size,
        if (a.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch a).toNat))).getD false then 0
        else ((b.balances.data[i]?.map UInt64.toNat).getD 0) -
          ((a.balances.data[i]?.map UInt64.toNat).getD 0)) +
        (b.depositBalanceToConsume electra).toNat ≤
          (a.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (ok : processEpoch config checks s = .ok t) :
    (∑ i ∈ Finset.range t.validators.data.size, preKeyCharge candidate t i) +
      (t.depositBalanceToConsume electra).toNat ≤
        (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) +
          (s.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  let cap := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let pendingStage : EpochStage → Bool := fun k =>
    match k with | .pendingDeposits => true | _ => false
  let total (a : BeaconState preset f) :=
    (∑ i ∈ Finset.range a.validators.data.size, preKeyCharge candidate a i) +
      (a.depositBalanceToConsume electra).toNat
  let Q (rest : List EpochStage) (a : BeaconState preset f) :=
    (EpochStage.justification ∈ rest → rest = EpochStage.epochStages ∧ a = s) ∧
      a.slot = s.slot ∧
      ActivationExitOrder a ∧ ExitsOrdered a ∧
      a.finalizedCheckpoint.epoch ≤ getCurrentEpoch s ∧
      total a + cap * rest.countP pendingStage ≤ total s + cap
  have finalized : s.finalizedCheckpoint.epoch ≤ getCurrentEpoch s :=
    UInt64.le_trans valid.ordered.1 (UInt64.le_trans valid.ordered.2
      (UInt64.le_trans valid.settled (getPreviousEpoch_le s)))
  have start : Q EpochStage.epochStages s := by
    refine ⟨fun _ => ⟨rfl, rfl⟩, rfl, ordered, valid.exitsOrdered, finalized, ?_⟩
    simp [EpochStage.epochStages, EpochStage.prefixStages, EpochStage.middleStages,
      EpochStage.tailStages, pendingStage]
  have whole := CapStep.epoch_of Q start (fun k rest a b edge previous matched funded state => by
    obtain ⟨first, slot, activationOrder, exits, checkpoint, budget⟩ := state
    have finiteA : getCurrentEpoch a < FAR_FUTURE_EPOCH := by
      simpa only [getCurrentEpoch, slot] using finite
    have slotStep : b.slot = a.slot := by
      by_cases justification : k = .justification
      · subst k
        exact (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2
      · exact (epochEdge_frame edge justification).slot
    refine ⟨?_, slotStep.trans slot, edge.activationExitOrder activationOrder, ?_, ?_, ?_⟩
    · intro remains
      have schedule := (first (List.mem_cons_of_mem k remains)).1
      simp only [EpochStage.epochStages, EpochStage.prefixStages, EpochStage.middleStages,
        EpochStage.tailStages, List.cons_append, List.nil_append, List.cons.injEq] at schedule
      obtain ⟨rfl, rfl⟩ := schedule
      simp at remains
    · by_cases justification : k = .justification
      · subst k
        obtain ⟨validators, _, _⟩ := edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        simpa only [ExitsOrdered, validators] using exits
      · exact (epochEdge_frame edge justification).exitsOrdered exits
    · by_cases justification : k = .justification
      · subst k
        have same := (first List.mem_cons_self).2
        subst a
        have result :=
          processJustificationAndFinalization_invariant valid.ordered valid.settled edge
        exact UInt64.le_trans result.1.1 (UInt64.le_trans result.1.2 result.2.2.1)
      · simpa only [(epochEdge_frame edge justification).finalized] using checkpoint
    · by_cases pending : k = .pendingDeposits
      · subst k
        have processed : processPendingDeposits config checks a electra = .ok b := by
          simpa only [EpochStage.Edge, electra, ↓reduceDIte] using edge
        have paid := preKeyCharge_pending candidate processed (matched valid.balancesMatch)
          activationOrder exits finiteA _ (pendingLaw a b processed (matched valid.balancesMatch))
        have count : (EpochStage.pendingDeposits :: rest).countP pendingStage =
            rest.countP pendingStage + 1 := by
          simp only [List.countP_cons, pendingStage, ↓reduceIte]
        rw [count] at budget
        rw [Nat.mul_add, Nat.mul_one] at budget
        change total b + cap * rest.countP pendingStage ≤ total s + cap
        have paid' : total b ≤ total a + cap := by
          simpa only [total, cap, Nat.add_assoc] using paid
        omega
      · have keywise := preKeyCharge_epochEdge edge pending electra early activation
          (funded early activation aligned.1 caps valid.balancesMatch targets held)
          (previous.targets early targets) (UInt64.lt_of_le_of_lt checkpoint finite) candidate
        have summed := Finset.sum_le_sum (s := Finset.range b.validators.data.size)
          (fun i _ => keywise i)
        rw [preKeyCharge_sum_range candidate a edge.registryLifecycle.size_le] at summed
        have carry := edge.depositCarry pending
        have absent : pendingStage k = false := by cases k <;> simp_all [pendingStage]
        simp only [List.countP_cons, absent, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero] at budget
        change total b + cap * rest.countP pendingStage ≤ total s + cap
        dsimp only [total] at budget ⊢
        rw [carry]
        omega) ok
  simpa only [total, cap, List.countP_nil, Nat.mul_zero, Nat.add_zero]
    using whole.2.2.2.2.2.2.2.2

private theorem preKeyCharge_slot {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (candidate : Nat → Bool)
    (epochBound : ∀ (a b : BeaconState preset f),
      processSlot s = .ok a →
      a.validators = s.validators → a.balances = s.balances →
      a.slot = s.slot → a.depositBalanceToConsume = s.depositBalanceToConsume →
      processEpoch config checks a = .ok b →
      (∑ i ∈ Finset.range b.validators.data.size, preKeyCharge candidate b i) +
        (b.depositBalanceToConsume electra).toNat ≤
          (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) +
            (s.depositBalanceToConsume electra).toNat +
              config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (ok : advanceSlot config checks s = .ok t) :
    (∑ i ∈ Finset.range t.validators.data.size, preKeyCharge candidate t i) +
      (t.depositBalanceToConsume electra).toNat ≤
        (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) +
          (s.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
              ((getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have slot := (frame_processSlot cachedOk).slot
  have fields : cached.validators = s.validators ∧ cached.balances = s.balances ∧
      cached.depositBalanceToConsume = s.depositBalanceToConsume := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl, rfl⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epoch := nextSlot_epoch_of_boundary sum boundary
    have paid := epochBound cached epoched cachedOk fields.1 fields.2.1 slot fields.2.2 epochedOk
    have difference : next.toNat / preset.SLOTS_PER_EPOCH.toNat -
        s.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = 1 := by omega
    simpa only [preKeyCharge, getCurrentEpoch_toNat, difference, Nat.mul_one] using paid
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have epoch := nextSlot_epoch_of_inside sum inside
    have difference : next.toNat / preset.SLOTS_PER_EPOCH.toNat -
        s.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = 0 := by omega
    simp only [preKeyCharge, getCurrentEpoch_toNat, difference, Nat.mul_zero,
      Nat.add_zero, fields.1, fields.2.1, fields.2.2, Nat.le_refl]

private theorem preKeyCharge_upgrades {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (candidate : Nat → Bool)
    (charge : ∀ i, preKeyCharge candidate t.state i = preKeyCharge candidate s.state i)
    (ok : processUpgrades config checks s = .ok t) :
    (∑ i ∈ Finset.range t.state.validators.data.size, preKeyCharge candidate t.state i) +
      (t.state.depositBalanceToConsume (Nat.le_trans electra
        (processUpgrades_fork_le ok))).toNat =
        (∑ i ∈ Finset.range s.state.validators.data.size, preKeyCharge candidate s.state i) +
          (s.state.depositBalanceToConsume electra).toNat := by
  have total :
      (∑ i ∈ Finset.range t.state.validators.data.size, preKeyCharge candidate t.state i) =
        ∑ i ∈ Finset.range s.state.validators.data.size, preKeyCharge candidate s.state i := by
    rw [← preKeyCharge_sum_range candidate t.state
      (Nat.le_max_right s.state.validators.data.size t.state.validators.data.size),
      ← preKeyCharge_sum_range candidate s.state (Nat.le_max_left _ _)]
    exact Finset.sum_congr rfl (fun i _ => charge i)
  have carry := depositCarry_processUpgrades ok early
  have later : .pectra ≤ t.fork := Nat.le_trans electra (processUpgrades_fork_le ok)
  simp only [electra, later, ↓reduceDIte] at carry
  rw [total, carry]

private theorem preKeyCharge_step {s t : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (candidate : Nat → Bool)
    (blocks : ∀ (engine : ExecutionEngine preset s.fork)
      (block : BeaconBlock preset s.fork) (b : BeaconState preset s.fork),
      processBlock config checks engine s.state block = .ok b →
      (∑ i ∈ Finset.range b.validators.data.size, preKeyCharge candidate b i) +
        (b.depositBalanceToConsume electra).toNat ≤
          (∑ i ∈ Finset.range s.state.validators.data.size,
            preKeyCharge candidate s.state i) + (s.state.depositBalanceToConsume electra).toNat)
    (epochs : ∀ (a b : BeaconState preset s.fork),
      processSlot s.state = .ok a →
      a.validators = s.state.validators → a.balances = s.state.balances →
      a.slot = s.state.slot → a.depositBalanceToConsume = s.state.depositBalanceToConsume →
      processEpoch config checks a = .ok b →
      (∑ i ∈ Finset.range b.validators.data.size, preKeyCharge candidate b i) +
        (b.depositBalanceToConsume electra).toNat ≤
          (∑ i ∈ Finset.range s.state.validators.data.size,
            preKeyCharge candidate s.state i) +
            (s.state.depositBalanceToConsume electra).toNat +
              config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (step : Step config checks s t) :
    (∑ i ∈ Finset.range t.state.validators.data.size, preKeyCharge candidate t.state i) +
      (if h : .pectra ≤ t.fork then (t.state.depositBalanceToConsume h).toNat else 0) ≤
        (∑ i ∈ Finset.range s.state.validators.data.size, preKeyCharge candidate s.state i) +
          (s.state.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
              ((getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat) := by
  cases step with
  | block engine signed due ok =>
    have bound := blocks engine signed.message _ (applySignedBlock_ok ok).2.1
    have slot := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
    simpa only [electra, ↓reduceDIte, getCurrentEpoch, slot, Nat.sub_self, Nat.mul_zero,
      Nat.add_zero] using bound
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have bound := preKeyCharge_slot electra candidate epochs slotOk
    have up := CapStep.upgrades activation compounding upgrades
    have unchanged := preKeyCharge_upgrades (s := ⟨s.fork, advanced⟩) electra early candidate
      (up.2.2.2 electra early candidate) upgrades
    have slot := processUpgrades_slot upgrades
    have later : Fork.pectra ≤ t.fork :=
      Nat.le_trans electra (processUpgrades_fork_le (forked := ⟨s.fork, advanced⟩) upgrades)
    simp only [later, ↓reduceDIte]
    rw [unchanged]
    simpa only [getCurrentEpoch, slot] using bound

private theorem preKeyCharge_run {g x u : ForkedBeaconState preset}
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (head : Run config checks x u)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : u.fork < .glamsterdam)
    (candidate : Nat → Bool)
    (pendingLaw : ∀ {f : Fork} (a b : BeaconState preset f) (e : .pectra ≤ f),
      f < .glamsterdam → processPendingDeposits config checks a e = .ok b → BalancesMatch a →
      (∑ i ∈ Finset.range b.validators.data.size,
        if (a.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch a).toNat))).getD false then 0
        else ((b.balances.data[i]?.map UInt64.toNat).getD 0) -
          ((a.balances.data[i]?.map UInt64.toNat).getD 0)) +
        (b.depositBalanceToConsume e).toNat ≤ (a.depositBalanceToConsume e).toNat +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (blockLaw : ∀ {f : Fork} (a b : BeaconState preset f)
      (engine : ExecutionEngine preset f) (block : BeaconBlock preset f),
      f < .glamsterdam → processBlock config checks engine a block = .ok b →
      b.depositBalanceToConsume = a.depositBalanceToConsume)
    (finite : getCurrentEpoch u.state < FAR_FUTURE_EPOCH) :
    (∑ i ∈ Finset.range u.state.validators.data.size, preKeyCharge candidate u.state i) +
      (if h : .pectra ≤ u.fork then (u.state.depositBalanceToConsume h).toNat else 0) ≤
        (∑ i ∈ Finset.range x.state.validators.data.size, preKeyCharge candidate x.state i) +
          (x.state.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
              ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) := by
  let total (a : ForkedBeaconState preset) :=
    (∑ i ∈ Finset.range a.state.validators.data.size, preKeyCharge candidate a.state i) +
      (if h : .pectra ≤ a.fork then (a.state.depositBalanceToConsume h).toNat else 0)
  let cap := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let Q := fun {a : ForkedBeaconState preset} (_ : Run config checks x a) =>
    .pectra ≤ a.fork ∧ getCurrentEpoch x.state ≤ getCurrentEpoch a.state ∧
      (getCurrentEpoch a.state < FAR_FUTURE_EPOCH →
        total a ≤ total x + cap *
          ((getCurrentEpoch a.state).toNat - (getCurrentEpoch x.state).toNat))
  have before := Nat.lt_of_le_of_lt (fork_le_of_chainSteps head.chainSteps) early
  have result := CapStep.run_of head shared activation compounding
    (CapStep.run shared activation compounding before) Q
    ⟨electra, UInt64.le_refl _, fun _ => by simp [total]⟩
    (fun {a b} pre step early first partials invariant funded previous => by
      have last := (CapStep.step step activation compounding early).1
      refine ⟨Nat.le_trans previous.1 last.forks,
        UInt64.le_trans previous.2.1 last.forward, ?_⟩
      intro finiteB
      have finiteA := UInt64.lt_of_le_of_lt last.forward finiteB
      have held := funded genesis aligned finiteA
      obtain ⟨_, _, _, initialized⟩ := genesis
      have valid := invariant (initializeBeaconStateFromEth1_invariant initialized).2
      have initialPartials : AssignedPartials g.state := by
        intro e
        exact (Nat.not_le_of_lt (initializeBeaconStateFromEth1_ok initialized).1
          (Nat.le_trans (by decide) e)).elim
      have initialTargets : AssignedTargets g.state := by
        intro e
        exact (Nat.not_le_of_lt (initializeBeaconStateFromEth1_ok initialized).1
          (Nat.le_trans (by decide) e)).elim
      have initialProposers : AssignedProposers g.state := by
        intro e
        exact (Nat.not_le_of_lt (initializeBeaconStateFromEth1_ok initialized).1
          (Nat.le_trans (by decide) e)).elim
      have earlyA := Nat.lt_of_le_of_lt last.forks early
      have reachable := shared.append pre
      have ordered := reachable.activationExitOrder ⟨_, _, _, initialized⟩
      have capped := first.capped
        (Genesis.effectiveBalance_capped ⟨_, _, _, initialized⟩)
      have targets := first.targets earlyA initialTargets
      have caps {h : Fork} (v : Validator) :
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v := by
        unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        split
        · split
          · exact UInt64.le_trans activation compounding
          · exact activation
        · exact UInt64.le_refl _
      have paid := preKeyCharge_step activation compounding previous.1 early candidate
        (fun engine block after ok => by
          have charge := (CapStep.block compounding ok).2.2.2 previous.1 earlyA
            (first.proposers earlyA initialProposers) ordered valid.exitsOrdered
            (partials initialPartials) finiteA capped valid.balancesMatch
            (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
              reachable.chainSteps).2
            (fun altair => (reachable.syncCommittee_activation_assigned
              ⟨_, _, _, initialized⟩ altair).1) held candidate
          have summed := Finset.sum_le_sum (s := Finset.range after.validators.data.size)
            (fun i _ => charge i)
          rw [preKeyCharge_sum_range candidate a.state
            (frame_processBlock ok).registryGrows] at summed
          rw [blockLaw _ _ engine block earlyA ok]
          omega)
        (fun cached after cacheOk validators balances slot carry ok => by
          have cacheValid := (frame_processSlot cacheOk).invariant valid
          have cacheTargets : AssignedTargets cached := by
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cacheOk
            exact targets
          have epoch := preKeyCharge_epoch previous.1 earlyA activation aligned caps cacheValid
            (by simpa only [ActivationExitOrder, validators] using ordered) cacheTargets
            (held.transfer (congrArg (·.data) validators) (fun i v amount found pending read low =>
              ⟨amount, by rw [balances]; exact read, low⟩))
            (by simpa only [getCurrentEpoch, slot] using finiteA) candidate
            (fun c d ok matched => pendingLaw c d previous.1 earlyA ok matched) ok
          simpa only [preKeyCharge, validators, balances, carry] using epoch) step
      have prior := previous.2.2 finiteA
      have low := UInt64.le_iff_toNat_le.mp previous.2.1
      have high := UInt64.le_iff_toNat_le.mp last.forward
      have difference : (getCurrentEpoch b.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch a.state).toNat - (getCurrentEpoch x.state).toNat) +
            ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) := by omega
      dsimp only [total, cap] at prior ⊢
      simp only [previous.1, ↓reduceDIte] at paid prior
      rw [difference, Nat.mul_add]
      omega) early
  simpa only [Q, total, cap, electra, ↓reduceDIte] using result.2.2.2 finite

private theorem run_unassigned_eligible_at_assignment {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    {epoch : Epoch} (computed : computeActivationExitEpoch preset (getCurrentEpoch x.state) =
      .ok epoch) {i : Nat} {v : Validator} (found : x.state.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH)
    (eligible : v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH) :
    preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance := by
  have room := (computeActivationExitEpoch_ok_iff.mp computed).1
  have finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (getCurrentEpoch x.state).toNat < 18446744073709551615
    omega
  exact ((run_unassigned_eligible_balance run genesis activation compounding aligned early
    finite) i v found unassigned).2.1 eligible

/-- An actual checked assignment can spend MEB from the same key's live reserve. -/
private theorem preKeyCharge_at_assignment {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    {epoch : Epoch} (computed : computeActivationExitEpoch preset (getCurrentEpoch x.state) =
      .ok epoch) (candidate : Nat → Bool) {i : Nat} (chosen : candidate i = true)
    {v : Validator} (found : x.state.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH)
    (eligible : v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH) :
    preset.MAX_EFFECTIVE_BALANCE.toNat ≤ preKeyCharge candidate x.state i := by
  have reserve := UInt64.le_iff_toNat_le.mp
    (run_unassigned_eligible_at_assignment run genesis activation compounding aligned early
      computed found unassigned eligible)
  simp only [preKeyCharge, chosen, ↓reduceIte, found, Option.map_some, unassigned,
    Option.getD_some]
  exact reserve.trans (Nat.le_max_left _ _)

private theorem preKeyCharge_assign {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    {epoch : Epoch} (computed : computeActivationExitEpoch preset (getCurrentEpoch x.state) =
      .ok epoch) (candidate : Nat → Bool) {i : Nat} {v : Validator}
    (found : getValidatorAt x.state i = .ok v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH)
    (eligible : v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH)
    {t : BeaconState preset x.fork}
    (set : x.state.setValidatorAt i { v with activationEpoch := epoch } = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate x.state j := by
  have atIndex := getValidatorAt_eq_ok_iff.mp found
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j
  by_cases equal : j = i
  · subst j
    by_cases chosen : candidate i = true
    · have reserve := preKeyCharge_at_assignment run genesis activation compounding aligned
        early computed candidate chosen atIndex unassigned eligible
      by_cases assigned : epoch = FAR_FUTURE_EPOCH
      · have same : { v with activationEpoch := epoch } = v := by
          rw [assigned, ← unassigned]
        simp only [same, preKeyCharge, BeaconState.putValidator,
          Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, ↓reduceIte,
          atIndex, Nat.le_refl]
      · simpa only [preKeyCharge, chosen, BeaconState.putValidator,
          Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, ↓reduceIte,
          Option.map_some, Option.getD_some, assigned] using reserve
    · simp only [preKeyCharge, chosen, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, Ne.symm equal, ↓reduceIte, Nat.le_refl]

private theorem run_assigned_partials {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) : AssignedPartials x.state := by
  apply (CapStep.run run activation compounding early).2.1
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨before, _⟩ := initializeBeaconStateFromEth1_ok initialized
  intro electra
  exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) electra)).elim

private theorem run_assigned_proposers {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) : AssignedProposers x.state := by
  apply (CapStep.run run activation compounding early).1.proposers early
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨before, _⟩ := initializeBeaconStateFromEth1_ok initialized
  intro fulu
  exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fulu)).elim

private theorem run_assigned_targets {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) : AssignedTargets x.state := by
  apply (CapStep.run run activation compounding early).1.targets early
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨before, _⟩ := initializeBeaconStateFromEth1_ok initialized
  intro electra
  exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) electra)).elim

private theorem unassigned_not_consolidation_target {f : Fork} {s : BeaconState preset f}
    (held : AssignedTargets s) {electra : .pectra ≤ f} {entry : PendingConsolidation}
    (member : entry ∈ (s.pendingConsolidations electra).data.toList)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) : entry.targetIndex.toNat ≠ i := by
  intro eq
  obtain ⟨w, read, assigned⟩ := held electra entry member entry.targetIndex (by simp)
  rw [eq, found, Option.some.injEq] at read
  subst w
  exact assigned unassigned

private theorem unassigned_not_cached_proposer {f : Fork} {s : BeaconState preset f}
    (held : AssignedProposers s) {fulu : .fusaka ≤ f} {proposer : ValidatorIndex}
    (member : proposer ∈ (s.proposerLookahead fulu).toList)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) : proposer.toNat ≠ i := by
  intro eq
  obtain ⟨w, read, assigned⟩ := held fulu proposer member
  rw [eq, found, Option.some.injEq] at read
  subst w
  exact assigned unassigned

private theorem run_unassigned_credit_exclusions {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) {i : Nat} {v : Validator}
    (found : x.state.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) :
    (∀ electra : .pectra ≤ x.fork,
      ∀ entry ∈ (x.state.pendingConsolidations electra).data.toList,
        entry.targetIndex.toNat ≠ i) ∧
    (∀ fulu : .fusaka ≤ x.fork,
      ∀ proposer ∈ (x.state.proposerLookahead fulu).toList, proposer.toNat ≠ i) := by
  constructor
  · intro electra entry member
    exact unassigned_not_consolidation_target
      (run_assigned_targets run genesis activation compounding early) member found unassigned
  · intro fulu proposer member
    exact unassigned_not_cached_proposer
      (run_assigned_proposers run genesis activation compounding early) member found unassigned

/-- Before Gloas, each validator reached from genesis has an effective balance at most its cap.

The preset caps are assumed in order.

`MAX_EFFECTIVE_BALANCE` is at most `MIN_ACTIVATION_BALANCE`.

`MIN_ACTIVATION_BALANCE` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`.
-/
theorem Run.effectiveBalance_capped {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) :
    ∀ v ∈ x.state.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v :=
  (CapStep.run run activation compounding early).1.capped genesis.effectiveBalance_capped

/-- An existing validator's cap cannot decrease along a pre-Gloas run. -/
theorem Run.validatorCap_mono {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : y.fork < .glamsterdam) (i : Nat) (v : Validator)
    (found : x.state.validators.data[i]? = some v) :
    ∃ w, y.state.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset x.fork v ≤
        withdrawalMaxEffectiveBalance preset y.fork w :=
  (CapStep.run run activation compounding early).1.monotone i v found

/-- New slashings delay withdrawal by the slashings-vector length from the run's start epoch.

Its exit epoch is assigned. -/
theorem Run.newly_slashed_withdrawableEpoch {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (unslashed : v.slashed = false) (slashed : w.slashed = true) :
    w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
      (getCurrentEpoch x.state).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat :=
  ((CapStep.run run activation compounding early).1.withdrawal i v w before after).2
    delay unslashed slashed

/-- The cap at an existing index cannot decrease during an epoch. -/
theorem processEpoch_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.epoch ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a proposer slashing. -/
theorem processProposerSlashing_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.proposerSlashing ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in an attester slashing. -/
theorem processAttesterSlashing_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.attesterSlashing ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a deposit. -/
theorem processDeposit_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.processDeposit ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a voluntary exit. -/
theorem processVoluntaryExit_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.exit (processVoluntaryExit_initiates ok)).1.monotone i v found

/-- The cap at an existing index cannot decrease in a change of BLS credentials. -/
theorem processBlsToExecutionChange_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.blsChange ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a withdrawal request. -/
theorem processWithdrawalRequest_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.withdrawalRequest ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a consolidation request.

This needs `MIN_ACTIVATION_BALANCE` to be at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
theorem processConsolidationRequest_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.consolidationRequest compounding ok).1.monotone i v found

/-- Before the slashings stage, a slashed validator with an assigned exit keeps that exit.

Its withdrawable epoch cannot decrease across the preceding epoch stages. -/
theorem EpochTrace.slashed_withdrawableEpoch_mono
    {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry] s t)
    (i : Nat) (v w : Validator)
    (before : s.validators.data[i]? = some v)
    (after : t.validators.data[i]? = some w)
    (slashed : v.slashed = true) (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    w.slashed = true ∧ w.exitEpoch = v.exitEpoch ∧
      v.withdrawableEpoch ≤ w.withdrawableEpoch := by
  cases trace with | cons justified rest =>
    cases rest with | cons inactivity rest =>
      cases rest with | cons rewarded rest =>
        cases rest with | cons registered rest =>
          cases rest
          have one := (EpochStage.action_cases.mp justified).validators_eq
            ⟨nofun, nofun, nofun⟩
          have two := (EpochStage.action_cases.mp inactivity).validators_eq
            ⟨nofun, nofun, nofun⟩
          have three := (EpochStage.action_cases.mp rewarded).validators_eq
            ⟨nofun, nofun, nofun⟩
          have atRegistry := before
          rw [← one, ← two, ← three] at atRegistry
          have ok := EpochStage.action_cases.mp registered
          have kept := ((CapStep.registry ok).1.withdrawal i v w atRegistry after).1
            slashed assigned
          obtain ⟨last, located, life⟩ :=
            (registryLifecycle_processRegistryUpdates ok).validators i v atRegistry
          obtain rfl : last = w := Option.some.inj (located.symm.trans after)
          exact ⟨kept.1, life.exitEpoch assigned, kept.2.2⟩
/-- One epoch keeps each effective balance at most the largest one of its validator. -/
theorem processEpoch_capped {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.epoch ok).1.capped capped

/-- One slot keeps each effective balance at most the largest one of its validator. -/
theorem advanceSlot_capped {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.slot ok).1.capped capped

/-- A block keeps each effective balance at most the largest one of its validator, at every fork.

The activation balance must be at most the cap of compounding credentials.

Then a switch to compounding credentials never lowers a cap. -/
theorem processBlock_capped {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.block compounding ok).1.capped capped

/-- The upgrade to the next fork keeps each effective balance at most the cap of its validator.

The caps of the preset are assumed in order.

The largest balance before Electra must be at most the least one from Electra.

That one must be at most the largest one for compounding credentials. -/
theorem upgradeNext_capped {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) (capped : EffectiveBalancesCapped s.state) :
    EffectiveBalancesCapped t.val.state :=
  (CapStep.upgrade activation compounding ok).1.capped capped

end EthLib.Consensus
