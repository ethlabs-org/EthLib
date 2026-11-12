module

public import EthLib.Consensus.Proofs.Models.Stake

/-!
# Proofs: weighted quorums

These names retain the direct safety interface to the shared stake arithmetic.
-/

@[expose] public section

namespace EthLib.Base.Quorum

variable {α : Type*} [DecidableEq α]

/-- The stake of a finite set, used by the direct safety bounds. -/
abbrev weight (w : α → Nat) (s : Finset α) : Nat := Consensus.Models.stake w s

/-- Restrict a stake function to its support for the direct safety drift bounds. -/
abbrev supported (s : Finset α) (w : α → Nat) (key : α) : Nat :=
  Consensus.Models.supported s w key

/-- The heterogeneous overlap bound used by `DirectSafety.accountable_safety_core`. -/
theorem heterogeneous_intersection (s₁ s₂ q₁ q₂ : Finset α) (w₁ w₂ : α → Nat)
    (inside₁ : q₁ ⊆ s₁) (inside₂ : q₂ ⊆ s₂)
    (t₁ t₂ : Nat) (quorum₁ : 2 * t₁ ≤ 3 * weight w₁ q₁)
    (quorum₂ : 2 * t₂ ≤ 3 * weight w₂ q₂) :
    2 * (t₁ + t₂) ≤
      3 * weight (fun k => min (w₁ k) (w₂ k)) (q₁ ∩ q₂) +
      3 * weight (fun k => max (supported s₁ w₁ k) (supported s₂ w₂ k)) (s₁ ∪ s₂) :=
  Consensus.Models.two_mul_stake_add_le_inter_add_union
    s₁ s₂ q₁ q₂ w₁ w₂ inside₁ inside₂ t₁ t₂ quorum₁ quorum₂

/-- The joint transfer used by the realized and terminal accountable pair bounds. -/
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
      2 * (loss₁ + loss₂) + (gain₁ + gain₂) + 2 * (outside₁ + outside₂) :=
  Consensus.Models.stake_le_accountable_add_change
    reference active₁ active₂ s₁ s₂ q₁ q₂ accountable old w₁ w₂
    loss₁ loss₂ gain₁ gain₂ outside₁ outside₂ activeInside₁ activeInside₂
    votersInside₁ votersInside₂ quorum₁ quorum₂ overlap lossOne lossTwo
    gainOne gainTwo outsideOne outsideTwo

end EthLib.Base.Quorum
