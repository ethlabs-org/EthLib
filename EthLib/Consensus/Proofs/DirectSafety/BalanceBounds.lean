module

public import EthLib.Consensus.Proofs.DirectSafety.Drift
public import EthLib.Consensus.Proofs.Accessors

/-!
# Effective-balance changes from the actual balance path

Loss uses initial slack, balance debits and rounding; gain uses initial excess and credits.

An epoch's effective-balance update reads its intermediate balance, before later upgrades.

For this reason a slot's balance path includes that intermediate state, not just its endpoints.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def balanceAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
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
  | x :: y :: rest => (balanceAt y i - balanceAt x i) + pathCredits i (y :: rest)
  | _ => 0

def pathDebits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (balanceAt x i - balanceAt y i) + pathDebits i (y :: rest)
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
  sorry

theorem effective_loss_from_balance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt x i - effectiveAt y i ≤
      (effectiveAt x i - balanceAt x i) + pathDebits i tail.balancePath +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  sorry

theorem effective_gain_from_balance {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i - effectiveAt x i ≤
      (balanceAt x i - effectiveAt x i) + pathCredits i tail.balancePath := by
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
  sorry

theorem hysteresis_gain (largest balance old next : Gwei)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) :
    next.toNat - old.toNat ≤ balance.toNat - old.toNat := by
  sorry

end EthLib.Consensus.DirectSafety
