module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Weighted quorum arithmetic

These statements concern finite sets and natural-number weights, not a consensus protocol.

This fork-only statement draft deliberately leaves the proofs for review.
-/

@[expose] public section

namespace EthLib.Base.Quorum

variable {α : Type*} [DecidableEq α]

def weight (w : α → Nat) (s : Finset α) : Nat := ∑ i ∈ s, w i

/-- Outside its own support, a stake measure is zero. -/
def supported (s : Finset α) (w : α → Nat) (key : α) : Nat :=
  if key ∈ s then w key else 0

/-- Two measures use their own weights for totals, minimum for overlap, maximum for union. -/
theorem heterogeneous_intersection (s₁ s₂ q₁ q₂ : Finset α) (w₁ w₂ : α → Nat)
    (inside₁ : q₁ ⊆ s₁) (inside₂ : q₂ ⊆ s₂)
    (t₁ t₂ : Nat) (quorum₁ : 2 * t₁ ≤ 3 * weight w₁ q₁)
    (quorum₂ : 2 * t₂ ≤ 3 * weight w₂ q₂) :
    2 * (t₁ + t₂) ≤
      3 * weight (fun k => min (w₁ k) (w₂ k)) (q₁ ∩ q₂) +
      3 * weight (fun k => max (supported s₁ w₁ k) (supported s₂ w₂ k)) (s₁ ∪ s₂) := by
  sorry

/-- Convert the drift-free bound, not the individual quorums, to a reference measure. -/
theorem core_at_reference (reference s₁ s₂ bad : Finset α) (old w₁ w₂ : α → Nat)
    (t₁ t₂ loss₁ loss₂ gain₁ gain₂ : Nat)
    (badInside : bad ⊆ s₁ ∩ s₂)
    (core : 2 * (t₁ + t₂) ≤
      3 * weight (fun k => min (w₁ k) (w₂ k)) bad +
      3 * weight (fun k => max (supported s₁ w₁ k) (supported s₂ w₂ k)) (s₁ ∪ s₂))
    (lossOne : weight old reference ≤ t₁ + loss₁)
    (lossTwo : weight old reference ≤ t₂ + loss₂)
    (gainOne : (∑ k ∈ s₁, (w₁ k - supported reference old k)) ≤ gain₁)
    (gainTwo : (∑ k ∈ s₂, (w₂ k - supported reference old k)) ≤ gain₂) :
    weight old reference ≤ 3 * weight old (reference ∩ bad) +
      2 * (loss₁ + loss₂) + 3 * (gain₁ + gain₂) := by
  sorry

/-- Transfer both quorums together, retaining the denominator contribution of weight gains.

The supports contain the voters and the active denominators.

Loss excludes accountable keys; gain costs one unit, not three.

Support outside the denominator costs two units separately.

When support equals the denominator, equal branch budgets give four times loss plus twice gain. -/
theorem accountable_at_reference (reference active₁ active₂ s₁ s₂ q₁ q₂ accountable : Finset α)
    (old w₁ w₂ : α → Nat) (loss₁ loss₂ gain₁ gain₂ outside₁ outside₂ : Nat)
    (activeInside₁ : active₁ ⊆ s₁) (activeInside₂ : active₂ ⊆ s₂)
    (votersInside₁ : q₁ ⊆ s₁) (votersInside₂ : q₂ ⊆ s₂)
    (quorum₁ : 2 * weight w₁ active₁ ≤ 3 * weight w₁ q₁)
    (quorum₂ : 2 * weight w₂ active₂ ≤ 3 * weight w₂ q₂)
    (overlap : q₁ ∩ q₂ ⊆ accountable)
    (lossOne : (∑ k ∈ reference \ accountable,
      (old k - supported s₁ w₁ k)) ≤ loss₁)
    (lossTwo : (∑ k ∈ reference \ accountable,
      (old k - supported s₂ w₂ k)) ≤ loss₂)
    (gainOne : (∑ k ∈ s₁, (w₁ k - supported reference old k)) ≤ gain₁)
    (gainTwo : (∑ k ∈ s₂, (w₂ k - supported reference old k)) ≤ gain₂)
    (outsideOne : weight w₁ (s₁ \ active₁) ≤ outside₁)
    (outsideTwo : weight w₂ (s₂ \ active₂) ≤ outside₂) :
    weight old reference ≤ 3 * weight old (reference ∩ accountable) +
      2 * (loss₁ + loss₂) + (gain₁ + gain₂) + 2 * (outside₁ + outside₂) := by
  sorry

end EthLib.Base.Quorum
