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

/-- The allowance for transporting a quorum to a reference set and its weights. -/
def change (reference active voters : Finset α) (old current : α → Nat) : Nat :=
  2 * (weight old (reference \ active) + ∑ i ∈ reference ∩ active, (old i - current i)) +
    3 * (weight current (voters \ reference) +
      ∑ i ∈ reference ∩ voters, (current i - old i))

theorem weight_union_inter (w : α → Nat) (s t : Finset α) :
    weight w s + weight w t = weight w (s ∪ t) + weight w (s ∩ t) := by
  sorry

theorem transfer (reference active voters : Finset α) (old current : α → Nat)
    (quorum : 2 * weight current active ≤ 3 * weight current voters) :
    2 * weight old reference ≤ 3 * weight old (reference ∩ voters) +
      change reference active voters old current := by
  sorry

theorem intersection (reference left right : Finset α) (w : α → Nat) (dLeft dRight : Nat)
    (one : 2 * weight w reference ≤ 3 * weight w (reference ∩ left) + dLeft)
    (two : 2 * weight w reference ≤ 3 * weight w (reference ∩ right) + dRight) :
    weight w reference ≤ 3 * weight w (reference ∩ left ∩ right) + dLeft + dRight := by
  sorry

theorem change_le (reference active voters : Finset α) (old current : α → Nat)
    (leaving lost entering gained : Nat)
    (leave : weight old (reference \ active) ≤ leaving)
    (loss : (∑ i ∈ reference ∩ active, (old i - current i)) ≤ lost)
    (enter : weight current (voters \ reference) ≤ entering)
    (gain : (∑ i ∈ reference ∩ voters, (current i - old i)) ≤ gained) :
    change reference active voters old current ≤ 2 * (leaving + lost) +
      3 * (entering + gained) := by
  sorry

end EthLib.Base.Quorum
