module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Genesis
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Effective-balance changes from the actual balance path

Loss uses initial slack, balance debits and rounding; gain uses initial excess and credits.

An epoch's effective-balance update reads its intermediate balance, before later upgrades.

For this reason a slot's balance path includes that intermediate state, not just its endpoints.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def actualBalanceAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.balances.data[i]?).map (·.toNat)).getD 0

def effectiveAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0

/-- Include the state before fork upgrades, where the effective balance was last updated. -/
def _root_.EthLib.Consensus.Step.balancePath {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    List (ForkedBeaconState preset) :=
  match step with
  | .block _ _ _ _ => [x, y]
  | .slot _ => match (advanceSlot config checks x.state).toOption with
    | none => [x, y]
    | some s => [x, ⟨x.fork, s⟩, y]

def _root_.EthLib.Consensus.Run.balancePath {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => [x]
  | _, .snoc pre step => pre.balancePath ++ step.balancePath

def pathCredits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (actualBalanceAt y i - actualBalanceAt x i) + pathCredits i (y :: rest)
  | _ => 0

def pathDebits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (actualBalanceAt x i - actualBalanceAt y i) + pathDebits i (y :: rest)
  | _ => 0

structure CapOrder (preset : Preset) : Prop where
  activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE
  compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA

theorem reachable_effective_alignment {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (early : x.fork < .glamsterdam) (v : Validator) (found : v ∈ x.state.validators.data.toList) :
    v.effectiveBalance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have _ := increment
  have _ := early
  have invariant {y : ForkedBeaconState preset} (trace : Run config checks g y) :
      Invariant y.state := by
    induction trace with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      exact (initializeBeaconStateFromEth1_invariant ok).2
    | snoc pre step ih =>
      cases step with
      | slot ok => exact (advanceSlotAcross_invariant ih ok).1
      | block engine signed due ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih
  have whole := (invariant run).aligned aligned v (by simpa using found)
  have numeric := congrArg UInt64.toNat whole
  simpa only [UInt64.toNat_mod, UInt64.reduceToNat] using numeric

theorem effective_loss_from_balance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt x i - effectiveAt y i ≤
      (effectiveAt x i - actualBalanceAt x i) + pathDebits i tail.balancePath +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  sorry

theorem effective_gain_from_balance {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i - effectiveAt x i ≤
      (actualBalanceAt x i - effectiveAt x i) + pathCredits i tail.balancePath := by
  sorry

/-- New keys are bounded from their actual admission balance, not a fictitious zero receipt. -/
theorem joining_growth_from_admission {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (early : y.fork < .glamsterdam)
    (i : Nat) (newKey : x.state.validators.data.size ≤ i)
    (present : i < y.state.validators.data.size) :
    effectiveAt y i ≤ pathCredits i tail.balancePath := by
  sorry

/-- A single hysteresis update loses less than one increment beyond its actual balance gap. -/
theorem hysteresis_loss (largest balance old next : Gwei)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (cap : old ≤ largest)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) :
    old.toNat - next.toNat ≤ old.toNat - balance.toNat +
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · omega
  · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
      UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
    have remainder := Nat.mod_lt balance.toNat increment
    have capped := UInt64.le_iff_toNat_le.mp cap
    rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
    omega

theorem hysteresis_gain (largest balance old next : Gwei)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) :
    next.toNat - old.toNat ≤ balance.toNat - old.toNat := by
  rcases updatedEffectiveBalance_eq_or_le ok with rfl | ⟨below, _⟩
  · omega
  · exact Nat.sub_le_sub_right (UInt64.le_iff_toNat_le.mp below) _

/-- Rounding cannot cross an aligned reference still covered by balance and cap. -/
theorem hysteresis_reference_le (reference largest balance old next : Gwei)
    (aligned : reference.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (previous : reference ≤ old) (funded : reference ≤ balance) (cap : reference ≤ largest)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) : reference ≤ next := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · exact previous
  · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
      UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
    have quotient := Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp funded)
      (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    have product := Nat.mul_le_mul_left preset.EFFECTIVE_BALANCE_INCREMENT.toNat quotient
    have referenceDivision := Nat.mod_add_div reference.toNat
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have balanceDivision := Nat.mod_add_div balance.toNat
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    rw [aligned] at referenceDivision
    rw [UInt64.le_iff_toNat_le, Base.Uint64.toNat_min,
      UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
    have cap := UInt64.le_iff_toNat_le.mp cap
    omega

/-- An effective-balance update cannot increase the funding held at any registry position. -/
theorem updateEffectiveBalance_funding {fork : Fork} {s t : BeaconState preset fork}
    {index : Nat} (ok : updateEffectiveBalance s index = .ok t) (i : Nat) :
    max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, balance, read, effective, updated, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have old : s.validators.data[index]? = some validator := by
    simpa [getValidatorAt, inside] using found
  by_cases same : i = index
  · subst i
    have actual : actualBalanceAt ⟨fork, s⟩ index = balance.toNat := by
      simp [actualBalanceAt, getBalanceAt_eq_ok_iff.mp read]
    have bound := updatedEffectiveBalance_le_max updated
    simpa [effectiveAt, actualBalanceAt, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, old, ← actual] using
      (max_le bound (Nat.le_max_right validator.effectiveBalance.toNat balance.toNat))
  · simp [effectiveAt, actualBalanceAt, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, Ne.symm same]

/-- The full effective-balance pass cannot mint funding, including at inactive positions. -/
theorem processEffectiveBalanceUpdates_funding {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : Nat) :
    max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) := by
  unfold processEffectiveBalanceUpdates at ok
  exact foldlM_ok_invariant
    (fun t => max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i))
    (fun _ _ _ previous step => (updateEffectiveBalance_funding step i).trans previous)
    (Nat.le_refl _) ok

end EthLib.Consensus
