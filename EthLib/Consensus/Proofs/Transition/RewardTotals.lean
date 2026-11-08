module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import EthLib.Consensus.Proofs.Transition.RewardDeltas

/-!
# Proofs: the total that the rewards of an epoch pay

From Altair, each flag pays its participants a share of their base rewards.

A participant earns its base reward times the weight of the flag and the participating increments.

That product is divided by the active increments times the weight denominator.

Its base reward is its effective balance in increments times the base reward per increment.

The participants' increments sum to at most the participating increments.

So the rewards of a flag sum to at most a cap of the state.

The cap is the base reward per increment times the weight and the participating increments squared.

That product is divided by the active increments times the weight denominator.

The participants are validators active in the previous epoch.

The active increments are those of the current epoch.

So the participating increments may exceed the active increments, and the bound keeps both.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-! ## Marked sums -/

/-- A fold over two lists of the same length adds the marked values to its start. -/
private theorem foldl_zip_marked {α : Type} (value : α → Nat) :
    ∀ (xs : List α) (marks : List Bool) (start : Nat), xs.length = marks.length →
      (xs.zip marks).foldl (fun sum (x, mark) => if mark then sum + value x else sum) start =
        start + ∑ j ∈ Finset.range xs.length,
          if marks.getD j false then ((xs[j]?).map value).getD 0 else 0
  | [], _, start, _ => by simp
  | x :: xs, [], _, same => by simp at same
  | x :: xs, mark :: marks, start, same => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at same
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_marked value xs marks _ same,
      List.length_cons, Finset.sum_range_succ']
    cases mark
    · simp
    · simp
      omega

/-- The effective balance at a position, on natural numbers, or zero past the end. -/
def effectiveNat (state : BeaconState preset fork) (j : Nat) : Nat :=
  ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0

/-- The sum of the marked effective balances is the sum over the positions that are marked. -/
theorem sumMarked_markIndices (indices : List ValidatorIndex) :
    sumMarked state.validators.data (markIndices state.validators.data.size indices) =
      ∑ j ∈ Finset.range state.validators.data.size,
        if ∃ index ∈ indices, index.toNat = j then effectiveNat state j else 0 := by
  have size : (markIndices state.validators.data.size indices).size =
      state.validators.data.size := by
    have := Array.size_eq_length_toList (xs := markIndices state.validators.data.size indices)
    apply Nat.le_antisymm
    · by_contra big
      have h := getElem?_markIndices state.validators.data.size indices
        state.validators.data.size
      simp only [Nat.lt_irrefl, ↓reduceIte] at h
      rw [Array.getElem?_eq_getElem (by omega)] at h
      cases h
    · by_contra small
      have h := getElem?_markIndices state.validators.data.size indices
        (markIndices state.validators.data.size indices).size
      rw [Array.getElem?_eq_none (Nat.le_refl _)] at h
      simp only [show (markIndices state.validators.data.size indices).size <
        state.validators.data.size by omega, ↓reduceIte] at h
      cases h
  unfold sumMarked
  rw [← Array.foldl_toList, Array.toList_zip,
    foldl_zip_marked (fun validator : Validator => validator.effectiveBalance.toNat) _ _ _
      (by simp [size]),
    Nat.zero_add, Array.length_toList]
  refine Finset.sum_congr rfl fun j member => ?_
  have inside := Finset.mem_range.mp member
  have marked : (markIndices state.validators.data.size indices).toList.getD j false =
      indices.any (·.toNat == j) := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem?_markIndices]
    simp [inside]
  rw [marked]
  simp [effectiveNat, List.any_eq_true]

/-! ## The flag rewards -/

/-- From Altair, a base reward is the effective increments times the base reward per increment. -/
theorem getBaseReward_of_altair (altair : .altair ≤ fork) {total base : Gwei}
    {index : ValidatorIndex} (computed : getBaseReward state total index = .ok base) :
    ∃ perIncrement, getBaseRewardPerIncrement preset total = .ok perIncrement ∧
      base.toNat = effectiveNat state index.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        perIncrement.toNat := by
  unfold getBaseReward at computed
  simp only [bind_ok_iff, altair, ↓reduceIte, liftArith, mapError_ok_iff] at computed
  obtain ⟨validator, found, perIncrement, perOk, product⟩ := computed
  refine ⟨perIncrement, perOk, ?_⟩
  have read : state.validators.data[index.toNat]? = some validator := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  rw [(mulChecked_ok_iff.mp product).2, UInt64.toNat_div]
  simp [effectiveNat, read]

private theorem add_div_le (a b c : Nat) : a / c + b / c ≤ (a + b) / c := by
  rcases Nat.eq_zero_or_pos c with rfl | positive
  · simp
  · rw [Nat.le_div_iff_mul_le positive, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a c) (Nat.div_mul_le_self b c)

/-- Rounded shares of one numerator sum to at most the rounded share of their sum. -/
theorem sum_div_le {ι : Type} (S : Finset ι) (f : ι → Nat) (d : Nat) :
    ∑ i ∈ S, f i / d ≤ (∑ i ∈ S, f i) / d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S absent step =>
    rw [Finset.sum_insert absent, Finset.sum_insert absent]
    exact Nat.le_trans (Nat.add_le_add_left step _) (add_div_le _ _ _)

/-- The base reward per increment for a total, on natural numbers, or zero on an error. -/
def rewardPerIncrement (preset : Preset) (total : Gwei) : Nat :=
  match getBaseRewardPerIncrement preset total with
  | .ok perIncrement => perIncrement.toNat
  | .error _ => 0

/-- The marked effective balances in increments sum to at most the increments of their total. -/
theorem sum_marked_increments_le {indices : List ValidatorIndex} {balance : Gwei}
    (weighed : getTotalBalance state indices = .ok balance) :
    ∑ j ∈ Finset.range state.validators.data.size,
        (if ∃ index ∈ indices, index.toNat = j then
          effectiveNat state j / preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) ≤
      balance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  obtain ⟨-, small, rfl⟩ := getTotalBalance_ok_iff.mp weighed
  have shares := sum_div_le (Finset.range state.validators.data.size)
    (fun j => if ∃ index ∈ indices, index.toNat = j then effectiveNat state j else 0)
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  rw [← sumMarked_markIndices] at shares
  refine Nat.le_trans (Nat.le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    (Nat.le_trans shares (Nat.div_le_div_right ?_))
  · split <;> simp
  · have exact : (sumMarked state.validators.data
        (markIndices state.validators.data.size indices)).toUInt64.toNat =
        sumMarked state.validators.data (markIndices state.validators.data.size indices) := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
    rw [UInt64.max_def]
    split
    · rw [exact]
    · rename_i above
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp above)
      omega

/-- From Altair, the rewards of one flag sum to at most a cap that the state gives.

The cap is the base reward per increment times the weight and the participating increments squared.

That product is divided by the active increments times the weight denominator.

The participating increments are those of the unslashed validators that set the flag.

The active increments are those of the current epoch.

That needs a registry within its limit. -/
theorem getFlagIndexDeltas_rewards_sum {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (within : state.RegistryWithinLimit)
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties)) :
    ∃ participating participatingBalance total,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
        (getPreviousEpoch state) = .ok participating ∧
      getTotalBalance state participating = .ok participatingBalance ∧
      getTotalActiveBalance state = .ok total ∧
      ∑ j ∈ Finset.range state.validators.data.size, (rewards.getD j 0).toNat ≤
        rewardPerIncrement preset total * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
          (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
          (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
          (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) := by
  obtain ⟨participating, participatingBalance, total, participatingOk, weighed, totalOk, each⟩ :=
    getFlagIndexDeltas_getD within computed
  refine ⟨participating, participatingBalance, total, participatingOk, weighed, totalOk, ?_⟩
  -- Name the parts of the bound.
  generalize hInc : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = inc
  generalize hP : participatingBalance.toNat / inc = pInc
  generalize hD : total.toNat / inc * WEIGHT_DENOMINATOR.toNat = denominator
  generalize hW : PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat = weight
  generalize hR : rewardPerIncrement preset total = perIncrement
  have marked := sum_marked_increments_le weighed
  rw [hInc, hP] at marked
  -- Each reward is at most the marked increments of its validator times a common factor.
  have bound : ∀ j ∈ Finset.range state.validators.data.size, (rewards.getD j 0).toNat ≤
      (if ∃ index ∈ participating, index.toNat = j then effectiveNat state j / inc else 0) *
        (perIncrement * weight * pInc) / denominator := by
    intro j member
    have inside := Finset.mem_range.mp member
    have small := toNat_toUInt64_of_lt within inside
    obtain ⟨eligible, -, no, yes⟩ := each j inside
    cases eligible with
    | false => simp [(no rfl).1]
    | true =>
      obtain ⟨base, baseOk, present, absent⟩ := yes rfl
      by_cases member : j.toUInt64 ∈ participating
      · obtain ⟨leak, -, reward, -⟩ := present member
        have named : ∃ index ∈ participating, index.toNat = j := ⟨_, member, small⟩
        obtain ⟨perIncrement', perOk, baseValue⟩ := getBaseReward_of_altair altair baseOk
        have same : perIncrement = perIncrement'.toNat := by
          rw [← hR, rewardPerIncrement, perOk]
        rw [reward, ite_eq_left_iff.mpr (fun h => absurd named h)]
        split
        · exact Nat.zero_le _
        · rw [baseValue, small, ← hP, ← hD, ← hW, ← hInc, same]
          apply Nat.le_of_eq
          congr 1
          ac_rfl
      · rw [(absent member).1]
        exact Nat.zero_le _
  calc ∑ j ∈ Finset.range state.validators.data.size, (rewards.getD j 0).toNat
      ≤ ∑ j ∈ Finset.range state.validators.data.size,
          (if ∃ index ∈ participating, index.toNat = j then effectiveNat state j / inc else 0) *
            (perIncrement * weight * pInc) / denominator := Finset.sum_le_sum bound
    _ ≤ (∑ j ∈ Finset.range state.validators.data.size,
          (if ∃ index ∈ participating, index.toNat = j then effectiveNat state j / inc else 0) *
            (perIncrement * weight * pInc)) / denominator := sum_div_le _ _ _
    _ = (∑ j ∈ Finset.range state.validators.data.size,
          (if ∃ index ∈ participating, index.toNat = j then effectiveNat state j / inc else 0)) *
            (perIncrement * weight * pInc) / denominator := by rw [Finset.sum_mul]
    _ ≤ pInc * (perIncrement * weight * pInc) / denominator :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ marked)
    _ = perIncrement * weight * pInc * pInc / denominator := by
          congr 1
          ac_rfl

end EthLib.Consensus
