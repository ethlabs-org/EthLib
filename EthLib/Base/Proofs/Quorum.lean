module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Weighted quorum arithmetic

These statements concern finite sets and natural-number weights, not a consensus protocol.
-/

@[expose] public section

namespace EthLib.Base.Quorum

variable {α : Type*} [DecidableEq α]

def weight (w : α → Nat) (s : Finset α) : Nat := ∑ i ∈ s, w i

/-- Outside its own support, a stake measure is zero. -/
def supported (s : Finset α) (w : α → Nat) (key : α) : Nat :=
  if key ∈ s then w key else 0

private theorem sum_supported (s u : Finset α) (w : α → Nat) (h : s ⊆ u) :
    (∑ k ∈ u, supported s w k) = weight w s := by
  unfold weight
  rw [← Finset.sum_subset h]
  · exact Finset.sum_congr rfl (fun k hk => by simp [supported, hk])
  · intro k _ hk
    simp [supported, hk]

/-- Two measures use their own weights for totals, minimum for overlap, maximum for union. -/
theorem heterogeneous_intersection (s₁ s₂ q₁ q₂ : Finset α) (w₁ w₂ : α → Nat)
    (inside₁ : q₁ ⊆ s₁) (inside₂ : q₂ ⊆ s₂)
    (t₁ t₂ : Nat) (quorum₁ : 2 * t₁ ≤ 3 * weight w₁ q₁)
    (quorum₂ : 2 * t₂ ≤ 3 * weight w₂ q₂) :
    2 * (t₁ + t₂) ≤
      3 * weight (fun k => min (w₁ k) (w₂ k)) (q₁ ∩ q₂) +
      3 * weight (fun k => max (supported s₁ w₁ k) (supported s₂ w₂ k)) (s₁ ∪ s₂) := by
  have pointwise : ∀ k,
      supported q₁ w₁ k + supported q₂ w₂ k ≤
      supported (q₁ ∩ q₂) (fun k => min (w₁ k) (w₂ k)) k +
        max (supported s₁ w₁ k) (supported s₂ w₂ k) := by
    intro k
    have h₁ := @inside₁ k
    have h₂ := @inside₂ k
    by_cases hq₁ : k ∈ q₁ <;> by_cases hq₂ : k ∈ q₂ <;>
      by_cases hs₁ : k ∈ s₁ <;> by_cases hs₂ : k ∈ s₂ <;>
      simp_all [supported, Finset.mem_inter]
    all_goals omega
  have total := Finset.sum_le_sum (s := s₁ ∪ s₂) (fun k _ => pointwise k)
  simp only [Finset.sum_add_distrib] at total
  rw [sum_supported q₁ _ w₁ (inside₁.trans Finset.subset_union_left),
    sum_supported q₂ _ w₂ (inside₂.trans Finset.subset_union_right),
    sum_supported (q₁ ∩ q₂) _ _
      (Finset.inter_subset_left.trans (inside₁.trans Finset.subset_union_left))] at total
  unfold weight at *
  dsimp only at *
  omega

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
  let u := reference ∪ s₁ ∪ s₂
  have refU : reference ⊆ u := by intro k hk; simp [u, hk]
  have oneU : s₁ ⊆ u := by intro k hk; simp [u, hk]
  have twoU : s₂ ⊆ u := by intro k hk; simp [u, hk]
  -- Each key contributes its old weight once, or twice when it is accountable.
  have pointwise : ∀ k,
      supported bad (fun k => min (w₁ k) (w₂ k)) k +
        supported (s₁ ∪ s₂)
          (fun k => max (supported s₁ w₁ k) (supported s₂ w₂ k)) k ≤
      supported reference old k + supported (reference ∩ bad) old k +
        supported s₁ (fun k => w₁ k - supported reference old k) k +
        supported s₂ (fun k => w₂ k - supported reference old k) k := by
    intro k
    have hb : k ∈ bad → k ∈ s₁ ∧ k ∈ s₂ :=
      fun hk => Finset.mem_inter.mp (badInside hk)
    by_cases hr : k ∈ reference <;> by_cases hb' : k ∈ bad <;>
      by_cases hs₁ : k ∈ s₁ <;> by_cases hs₂ : k ∈ s₂ <;>
      simp_all [supported, Finset.mem_inter, Finset.mem_union] <;> omega
  have total := Finset.sum_le_sum (s := u) (fun k _ => pointwise k)
  simp only [Finset.sum_add_distrib] at total
  rw [sum_supported bad u _
      (badInside.trans (Finset.inter_subset_left.trans oneU)),
    sum_supported (s₁ ∪ s₂) u _ (Finset.union_subset oneU twoU),
    sum_supported reference u old refU,
    sum_supported (reference ∩ bad) u old (Finset.inter_subset_left.trans refU),
    sum_supported s₁ u _ oneU, sum_supported s₂ u _ twoU] at total
  unfold weight at *
  dsimp only at *
  omega

set_option maxHeartbeats 4000000 in
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
  let u := reference ∪ s₁ ∪ s₂
  have refU : reference ⊆ u := by intro k hk; simp [u, hk]
  have oneU : s₁ ⊆ u := by intro k hk; simp [u, hk]
  have twoU : s₂ ⊆ u := by intro k hk; simp [u, hk]
  -- Sum the local inequality before using the two quorum bounds.
  have localBound : ∀ k,
      supported reference old k +
        3 * supported q₁ w₁ k + 3 * supported q₂ w₂ k ≤
      3 * supported (reference ∩ accountable) old k +
        2 * supported (reference \ accountable)
          (fun k => old k - supported s₁ w₁ k) k +
        2 * supported (reference \ accountable)
          (fun k => old k - supported s₂ w₂ k) k +
        supported s₁ (fun k => w₁ k - supported reference old k) k +
        supported s₂ (fun k => w₂ k - supported reference old k) k +
        2 * supported active₁ w₁ k + 2 * supported active₂ w₂ k +
        2 * supported (s₁ \ active₁) w₁ k +
        2 * supported (s₂ \ active₂) w₂ k := by
    intro k
    have hv₁ := @votersInside₁ k
    have hv₂ := @votersInside₂ k
    have ha₁ := @activeInside₁ k
    have ha₂ := @activeInside₂ k
    have ho : k ∈ q₁ → k ∈ q₂ → k ∈ accountable :=
      fun h₁ h₂ => overlap (Finset.mem_inter.mpr ⟨h₁, h₂⟩)
    by_cases hr : k ∈ reference <;> by_cases hb : k ∈ accountable <;>
      by_cases hs₁ : k ∈ s₁ <;> by_cases hs₂ : k ∈ s₂ <;>
      by_cases hq₁ : k ∈ q₁ <;> by_cases hq₂ : k ∈ q₂ <;>
      by_cases ha₁' : k ∈ active₁ <;> by_cases ha₂' : k ∈ active₂ <;>
      simp_all [supported, Finset.mem_inter, Finset.mem_sdiff] <;> omega
  have total := Finset.sum_le_sum (s := u) (fun k _ => localBound k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  rw [sum_supported reference u old refU,
    sum_supported q₁ u w₁ (votersInside₁.trans oneU),
    sum_supported q₂ u w₂ (votersInside₂.trans twoU),
    sum_supported (reference ∩ accountable) u old
      (Finset.inter_subset_left.trans refU),
    sum_supported (reference \ accountable) u _ (Finset.sdiff_subset.trans refU),
    sum_supported (reference \ accountable) u _ (Finset.sdiff_subset.trans refU),
    sum_supported s₁ u _ oneU, sum_supported s₂ u _ twoU,
    sum_supported active₁ u w₁ (activeInside₁.trans oneU),
    sum_supported active₂ u w₂ (activeInside₂.trans twoU),
    sum_supported (s₁ \ active₁) u w₁ (Finset.sdiff_subset.trans oneU),
    sum_supported (s₂ \ active₂) u w₂ (Finset.sdiff_subset.trans twoU)] at total
  unfold weight at *
  dsimp only at *
  omega

end EthLib.Base.Quorum
