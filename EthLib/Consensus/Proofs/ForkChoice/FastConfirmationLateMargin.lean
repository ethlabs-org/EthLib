module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety

/-!
# Static honest duties and the late margin

The paper's Assumption 1 excludes honest exits; its epoch committees partition the active set.
Here that consequence is explicit: each honest member of the receiver's tally has an epoch duty.
The whole-tally Byzantine bound is the full-registry instance of Assumption 2.
These are inputs, not a derivation of registry stability from executable transitions.

The proposer boost is bounded by its specified fraction of an average slot committee.
We assume at least two slots, at most 40 percent boost and at most 25 percent Byzantine stake.
Then the boost is strictly below the remaining majority margin when the tally has positive stake.

Source: arXiv 2405.00549v4, Section 2.1 and Assumptions 1 and 2 in Section 3.2.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Network

/-- Above the accessor's minimum, the executable proposer score is the rounded tally fraction. -/
theorem computeProposerScore_eq_tally_fraction
    {preset : Preset} {fork : Fork} {config : Config} {state : BeaconState preset fork}
    {score : Gwei}
    (floor : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun v => balanceAt state v.toNat)
        ((unslashedActiveBalances state).map (·.1)).toFinset)
    (read : computeProposerScore config state = .ok score) :
    score.toNat = (stake (fun v => balanceAt state v.toNat)
      ((unslashedActiveBalances state).map (·.1)).toFinset /
        preset.SLOTS_PER_EPOCH.toNat * config.PROPOSER_SCORE_BOOST.toNat) / 100 := by
  unfold computeProposerScore calculateCommitteeFraction at read
  simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨total, totalOk, committee, committeeOk, product, productOk, result⟩ := read
  have totalEq := (getTotalBalance_ok_iff_stake.mp totalOk).2.2
  have committeeEq := (divChecked_ok_iff.mp committeeOk).2
  have productEq := (mulChecked_ok_iff.mp productOk).2
  cases result
  rw [UInt64.toNat_div, productEq, committeeEq, totalEq, max_eq_right floor]
  rfl

/-- The specified average-committee boost fits the majority margin at the mainnet thresholds.

The inequality also covers smaller boosts and any epoch with at least two slots. -/
theorem lateMargin_boost_bound {total boost slots percent beta : ℕ}
    (positive : 0 < total) (long : 2 ≤ slots) (smallBoost : percent ≤ 40)
    (byzantine : beta ≤ 25)
    (boostBound : boost ≤ (total / slots * percent) / 100) :
    100 * boost < (100 - 2 * beta) * total := by
  -- Integer rounding only decreases the boost.
  have rounded := Nat.div_mul_le_self (total / slots * percent) 100
  have committee := Nat.div_mul_le_self total slots
  have scaled := Nat.mul_le_mul_right 100 boostBound
  have fraction := Nat.mul_le_mul_left (total / slots) smallBoost
  have twice : 2 * (total / slots) ≤ total := by nlinarith
  have remaining : 50 ≤ 100 - 2 * beta := by omega
  nlinarith

/-- Complete honest duty coverage makes the late margin follow from the tally bound.

Coverage is the part of the paper's static setting needed here; Byzantine duties may change.
The bound on the boost uses the formula of `calculateCommitteeFraction`, including rounding.
No premise bounds missing stake: coverage makes that set empty. -/
theorem lateMargin_of_static_honest_duties
    {preset : Preset} {fork : Fork} {config : Config} {genesisTimeMs : UInt64}
    {assignment : Assignment preset} {J : Set ValidatorIndex} [DecidablePred (· ∈ J)]
    {first time : ℕ} {state : BeaconState preset fork} {boost : ℕ}
    (complete : CompleteEpochWithin preset config genesisTimeMs first time)
    (coverage : ∀ epoch begin next,
      computeStartSlotAtEpoch preset epoch = .ok begin →
      addChecked begin preset.SLOTS_PER_EPOCH = .ok next →
      ∀ v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset, v ∈ J →
        ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
          assignment.committee v slot = some committeeIndex)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      ((unslashedActiveBalances state).map (·.1)).toFinset J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (positive : 0 < stake (fun v => balanceAt state v.toNat)
      ((unslashedActiveBalances state).map (·.1)).toFinset)
    (long : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (smallBoost : config.PROPOSER_SCORE_BOOST.toNat ≤ 40)
    (threshold : config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 25)
    (boostBound : boost ≤ (stake (fun v => balanceAt state v.toNat)
      ((unslashedActiveBalances state).map (·.1)).toFinset /
        preset.SLOTS_PER_EPOCH.toNat * config.PROPOSER_SCORE_BOOST.toNat) / 100) :
    LateMargin config genesisTimeMs assignment J first time state boost := by
  classical
  obtain ⟨epoch, begin, next, beginTime, endTime, beginOk, nextOk, beginTimeOk,
    endTimeOk, firstLe, endLe⟩ := complete
  refine ⟨epoch, begin, next, beginTime, endTime, beginOk, nextOk, beginTimeOk,
    endTimeOk, firstLe, endLe, ?_⟩
  -- Every member of the missing set contradicts the supplied epoch coverage.
  have empty : {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧
      ¬∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
        assignment.committee v slot = some committeeIndex} = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro v member missing
    exact missing.2 (coverage epoch begin next beginOk nextOk v member missing.1)
  -- With no missing duty, the boost alone must fit the margin that the Byzantine bound leaves.
  apply late_majority_of_missing_duties _ byzantine (by omega)
  simpa only [empty, stake, Finset.sum_empty, Nat.mul_zero, Nat.zero_add] using
    lateMargin_boost_bound positive long smallBoost threshold boostBound

/-- Direct honest-duty majority suffices, without estimating the Byzantine fraction.

`D` contains the members with an epoch duty and `S` the actual supporters.
The late-duty proof supplies `supported`; the store majority theorem consumes the conclusion. -/
theorem majority_of_honest_duties {ν : Type*} [DecidableEq ν]
    (w : ν → ℕ) (V D S : Finset ν) (J : Set ν) [DecidablePred (· ∈ J)] {boost : ℕ}
    (supported : ∀ v ∈ V, v ∈ J → v ∈ D → v ∈ S)
    (margin : stake w V + boost < 2 * stake w {v ∈ V | v ∈ J ∧ v ∈ D}) :
    stake w V + boost < 2 * stake w S := by
  -- Duty support is a subset of actual support, with the same nonnegative weights.
  have subset : {v ∈ V | v ∈ J ∧ v ∈ D} ⊆ S := by
    intro v member
    obtain ⟨inside, honest, duty⟩ := Finset.mem_filter.mp member
    exact supported v inside honest duty
  exact margin.trans_le (Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset subset))

end EthLib.Consensus
