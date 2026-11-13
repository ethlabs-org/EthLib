module

public import EthLib.Consensus.Participation
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Monotone.Defs
import EthLib.Base.Proofs.MapM
import EthLib.Base.Proofs.Uint64
import Mathlib.Tactic.Ring

/-!
# A monotone envelope for the issuance of one epoch

From Altair, the base reward of one increment of effective balance is a factor times the increment.

That product is divided by the integer square root of the total active balance, rounding down.

The total base rewards of an epoch are that reward for each whole increment of the total.

They bound what one epoch can issue, but they are not monotone in the total.

On mainnet, a total of 36,066,180 ETH gives 12,154,302,660 Gwei.

One more ETH gives 12,118,236,816 Gwei, since the square root steps up while the increments do not.

This module bounds them by `issuanceEnvelope`, which is monotone in the total.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Uint64

variable {preset : Preset}

/-- The issuance envelope of one epoch, in Gwei, at a total active balance in Gwei.

It is the base reward factor times the integer square root of the total, plus two.

It bounds the total base rewards of an epoch, and it is monotone in the total. -/
def issuanceEnvelope (preset : Preset) (total : Nat) : Nat :=
  preset.BASE_REWARD_FACTOR.toNat * (total.sqrt + 2)

/-- The issuance envelope does not decrease when the total active balance grows. -/
theorem issuanceEnvelope_monotone : Monotone (issuanceEnvelope preset) := fun _ _ le =>
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sqrt_le_sqrt le) 2)

/-- The whole increments of a total, times the scaled factor over its square root, rounding down.

The product is at most the factor times the square root plus two.

Both roundings only lower the product, so it is at most `total * factor / root`.

A total below `(root + 1)^2` is at most `root * (root + 2)`, which gives the bound. -/
private theorem div_mul_div_sqrt_le (total increment factor : Nat) :
    total / increment * (increment * factor / total.sqrt) ≤ factor * (total.sqrt + 2) := by
  have below : total ≤ total.sqrt * (total.sqrt + 2) := by
    have := Nat.lt_succ_sqrt total
    have square : total.sqrt * (total.sqrt + 2) + 1 = total.sqrt.succ * total.sqrt.succ := by
      rw [Nat.succ_eq_add_one]
      ring
    omega
  calc total / increment * (increment * factor / total.sqrt)
      ≤ total / increment * (increment * factor) / total.sqrt :=
        Nat.mul_div_le_mul_div_assoc _ _ _
    _ = total / increment * increment * factor / total.sqrt := by rw [Nat.mul_assoc]
    _ ≤ total * factor / total.sqrt :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _))
    _ ≤ factor * (total.sqrt + 2) := by
        apply Nat.div_le_of_le_mul
        calc total * factor ≤ total.sqrt * (total.sqrt + 2) * factor :=
              Nat.mul_le_mul_right _ below
          _ = total.sqrt * (factor * (total.sqrt + 2)) := by ring

/-- The total base rewards of an epoch are at most the issuance envelope of its total.

They are the whole increments of the total active balance, times the base reward per increment.

The bound needs no premise beyond the success of the reward per increment. -/
theorem totalBaseRewards_le_envelope {total perIncrement : Gwei}
    (computed : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat ≤
      issuanceEnvelope preset total.toNat := by
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at computed
  obtain ⟨scaled, scaledOk, rootOk⟩ := computed
  rw [mulChecked_ok_iff] at scaledOk
  rw [divChecked_ok_iff] at rootOk
  rw [rootOk.2, scaledOk.2, toNat_integerSquareroot]
  exact div_mul_div_sqrt_le _ _ _

end EthLib.Consensus.DirectSafety
