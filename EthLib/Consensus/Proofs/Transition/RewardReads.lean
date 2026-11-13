module

public import EthLib.Consensus.Proofs.Participation
public import EthLib.Consensus.Proofs.Transition.BlockRewards
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Proofs: the reads behind the rewards, as formulas on natural numbers

The total active balance is the sum of the effective balances of the active validators.

A sync participant reward is then a formula of that total.

Each statement holds when the executable read succeeds, and says nothing otherwise.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- A successful active-balance read is the sum of the effective balances of the active validators.

A total below one increment is read as one increment.

The sum runs over the positions of the registry that are active in the current epoch.

An unsuccessful read has no value, so the statement holds only when the read succeeds. -/
theorem getTotalActiveBalance_toNat {state : BeaconState preset fork} {total : Gwei}
    (computed : getTotalActiveBalance state = .ok total) :
    total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (Finset.range state.validators.data.size).filter
          (fun i => isActiveAt state (getCurrentEpoch state) i = true),
        ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) := by
  obtain ⟨indices, checked, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨-, lt, rfl⟩ := getTotalBalance_ok_iff.mp computed
  have sum : sumMarked state.validators.data (markIndices state.validators.data.size indices) =
      ∑ i ∈ (Finset.range state.validators.data.size).filter
          (fun i => isActiveAt state (getCurrentEpoch state) i = true),
        ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
    rw [sumMarked_eq_sum, Finset.sum_filter, Finset.sum_eq_multiset_sum, Finset.range_val,
      ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]
    congr 1
    refine List.map_congr_left fun j member => ?_
    have inside := List.mem_range.mp member
    -- The mark of a position is set exactly when the position is active.
    have marked : (indices.any (·.toNat == j)) = isActiveAt state (getCurrentEpoch state) j := by
      rw [Bool.eq_iff_iff, List.any_eq_true, isActiveAt_eq_true_iff]
      constructor
      · rintro ⟨x, member, equal⟩
        have := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp member
        rw [beq_iff_eq] at equal
        rwa [equal] at this
      · rintro ⟨validator, found, active⟩
        have fits := lt_of_getActiveValidatorIndicesChecked_ok checked found active
        have same : j.toUInt64.toNat = j := by
          rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
        refine ⟨j.toUInt64, (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mpr
          ⟨validator, by rw [same]; exact found, active⟩, ?_⟩
        rw [beq_iff_eq, same]
    rw [getElem?_markIndices]
    simp only [inside, ↓reduceIte, Option.getD_some, marked]
  rw [← sum, toNat_max, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' lt]

/-- A successful sync participant reward is a formula of the total active balance.

It is the base reward per increment times the active increments, weighted by the sync weight.

That product is divided by the weight denominator, the slots of an epoch and the committee size.

Each division rounds down, and the base reward per increment rounds down too. -/
theorem syncParticipantReward_toNat
    {state : BeaconState preset fork} {total reward : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (computed : syncParticipantReward state = .ok reward) :
    reward.toNat = total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        (integerSquareroot (UInt64.ofNat total.toNat)).toNat) * SYNC_REWARD_WEIGHT.toNat /
      WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat := by
  obtain ⟨read, perIncrement, readOk, perOk, -, value⟩ := syncParticipantReward_ok computed
  obtain rfl : total = read := by simpa [totalOk] using readOk
  rw [value, getBaseRewardPerIncrement_toNat perOk, Nat.mul_comm (_ * _ / _)]

end EthLib.Consensus
