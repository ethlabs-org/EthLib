module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Monotone.Defs
import EthLib.Base.Proofs.MapM
import EthLib.Base.Proofs.Uint64
import EthLib.Consensus.Proofs.Participation
import EthLib.Consensus.Proofs.Transition.EpochParticipation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# A priori bounds on the balance changes of one epoch

From Altair, the base reward of one increment of effective balance is a factor times the increment.

That product is divided by the integer square root of the total active balance, rounding down.

The total base rewards of an epoch are that reward for each whole increment of the total.

They bound what one epoch can issue, but they are not monotone in the total.

On mainnet, a total of 36,066,180 ETH gives 12,154,302,660 Gwei.

One more ETH gives 12,118,236,816 Gwei, since the square root steps up while the increments do not.

This module bounds them by `issuanceEnvelope`, which is monotone in the total.

It also bounds what the rewards pass of an epoch takes from the balances, inside a leak or not.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Uint64

variable {preset : Preset}

/-- The issuance envelope of one epoch, in Gwei, at a total active balance in Gwei.

It is the base reward factor times the integer square root of the total, plus two.

It bounds the total base rewards of an epoch, and it is monotone in the total. -/
private def issuanceEnvelope (preset : Preset) (total : Nat) : Nat :=
  preset.BASE_REWARD_FACTOR.toNat * (total.sqrt + 2)

/-- The issuance envelope does not decrease when the total active balance grows. -/
private theorem issuanceEnvelope_monotone : Monotone (issuanceEnvelope preset) := fun _ _ le =>
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

/-- A successful base reward per increment is the scaled factor over the integer square root. -/
private theorem toNat_getBaseRewardPerIncrement {total perIncrement : Gwei}
    (computed : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    perIncrement.toNat = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat / total.toNat.sqrt := by
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at computed
  obtain ⟨scaled, scaledOk, rootOk⟩ := computed
  rw [mulChecked_ok_iff] at scaledOk
  rw [divChecked_ok_iff] at rootOk
  rw [rootOk.2, scaledOk.2, toNat_integerSquareroot]

/-- The total base rewards of an epoch are at most the issuance envelope of its total.

They are the whole increments of the total active balance, times the base reward per increment.

The bound needs no premise beyond the success of the reward per increment. -/
private theorem totalBaseRewards_le_envelope {total perIncrement : Gwei}
    (computed : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat ≤
      issuanceEnvelope preset total.toNat := by
  rw [toNat_getBaseRewardPerIncrement computed]
  exact div_mul_div_sqrt_le _ _ _

/-! ## The penalties of one rewards pass

From Altair, the rewards pass charges an eligible validator three penalties at most.

It pays the weight of the source flag and of the target flag, each when that flag is missing.

The base reward times the weight is divided by the weight denominator, rounding down.

It also pays the inactivity penalty when the target flag is missing.

That penalty is the effective balance times the new score, over the score bias times the quotient.

A missing head flag costs nothing, and the rewards only raise the balance.

The sync committee penalties are not part of this pass.

`processSyncAggregate` applies them in each block.
-/

variable {config : Config} {fork : Fork} {state scored after : BeaconState preset fork}
  {total : Gwei}

/-- A sum of quotients is at most the quotient of the sum. -/
private theorem sum_div_le (s : Finset Nat) (f : Nat → Nat) (d : Nat) :
    ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | positive
  · simp
  · rw [Nat.le_div_iff_mul_le positive, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self _ _

/-- A balance loses at most the sum of the penalties of a list of deltas.

Each delta adds its reward without overflow, then subtracts its penalty, stopping at zero. -/
private theorem sub_foldl_le (j : Nat) :
    ∀ (deltas : List (Array Gwei × Array Gwei)) (balance : Gwei),
      deltas.foldlM (fun balance delta => (addChecked balance (delta.1.getD j 0)).map
          fun raised => saturatingSub raised (delta.2.getD j 0)) balance =
        .ok (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD j 0) (delta.2.getD j 0)) balance) →
      balance.toNat - (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD j 0) (delta.2.getD j 0)) balance).toNat ≤
        (deltas.map fun delta => (delta.2.getD j 0).toNat).sum
  | [], _, _ => by simp
  | delta :: rest, balance, folded => by
    rw [List.foldlM_cons, bind_ok_iff] at folded
    obtain ⟨next, stepped, restOk⟩ := folded
    cases added : addChecked balance (delta.1.getD j 0) with
    | error failure =>
      rw [added] at stepped
      cases stepped
    | ok raised =>
      rw [added] at stepped
      simp only [Except.map, Except.ok.injEq] at stepped
      obtain ⟨fits, value⟩ := addChecked_ok_iff.mp added
      have same : raised = balance + delta.1.getD j 0 :=
        UInt64.toNat_inj.mp (by rw [value, toNat_add_of_lt fits])
      subst same stepped
      have later := sub_foldl_le j rest _ restOk
      have step := toNat_saturatingSub (balance + delta.1.getD j 0) (delta.2.getD j 0)
      rw [toNat_add_of_lt fits] at step
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      omega

/-- The base reward of a validator, from Altair, is its whole increments times the scaled factor.

The factor times the increment is divided by the integer square root of the total. -/
private theorem toNat_getBaseReward_le (altair : .altair ≤ fork) {base : Gwei}
    {index : ValidatorIndex} (computed : getBaseReward state total index = .ok base)
    {validator : Validator} (found : state.validators.data[index.toNat]? = some validator) :
    base.toNat ≤ validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        total.toNat.sqrt) := by
  have copy := computed
  simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff] at copy
  obtain ⟨_, _, perIncrement, perOk, _⟩ := copy
  obtain ⟨validator', found', value⟩ := getBaseReward_eq_mul_of_altair altair perOk computed
  obtain rfl : validator' = validator := Option.some.inj (found'.symm.trans found)
  rw [value, toNat_getBaseRewardPerIncrement perOk]

/-- The loss of one balance in the rewards pass, from Altair, with the zero beyond the registry. -/
private theorem rewardsDebit_cases (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (active : getTotalActiveBalance state = .ok total) (j : Nat) :
    (state.validators.data.size ≤ j →
      actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j = 0) ∧
    ∀ inside : j < state.validators.data.size,
      actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j = 0 ∨
      ∃ base, isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true ∧
        getBaseReward state total j.toUInt64 = .ok base ∧
        actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤
          base.toNat * (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) /
              WEIGHT_DENOMINATOR.toNat +
            state.validators.data[j].effectiveBalance.toNat *
              (((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  have keptScores := congrFun (congrArg (fun s => s.inactivityScores)
    (processRewardsAndPenalties_frame computed)) altair
  -- The score update changes only the scores.
  obtain ⟨scores, rfl⟩ : ∃ scores, scored = { state with inactivityScores := scores } :=
    ⟨_, processInactivityUpdates_frame updated⟩
  have scoresAfter : after.inactivityScores altair = scores altair := keptScores
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · -- In the first epoch the pass changes nothing.
    obtain rfl : { state with inactivityScores := scores } = after := Except.ok.inj
      ((processRewardsAndPenalties_genesis config (by exact genesis)).symm.trans computed)
    have zero : actualBalanceAt ⟨fork, state⟩ j -
        actualBalanceAt ⟨fork, { state with inactivityScores := scores }⟩ j = 0 :=
      Nat.sub_self _
    exact ⟨fun _ => zero, fun _ => .inl zero⟩
  obtain ⟨flagDeltas, inactivityDeltas, flagged, penalized, balances⟩ :=
    processRewardsAndPenalties_balances_of_altair altair (by exact genesis) computed
  refine ⟨fun outside => ?_, fun inside => ?_⟩
  · have kept : after.balances.data[j]? = state.balances.data[j]? :=
      (balances j).2.2 outside
    simp only [actualBalanceAt, kept, Nat.sub_self]
  have finRange : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl
  rw [finRange] at flagged
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at flagged
  obtain ⟨⟨sourceRewards, sourcePenalties⟩, sourceOk, _, ⟨⟨targetRewards, targetPenalties⟩,
    targetOk, _, ⟨⟨headRewards, headPenalties⟩, headOk, _, rfl, rfl⟩, rfl⟩, rfl⟩ := flagged
  obtain ⟨inactivityRewards, inactivityPenalties⟩ := inactivityDeltas
  obtain ⟨source, _, total', -, -, totalOk, sourceFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) sourceOk
  obtain ⟨target, _, total'', -, -, totalOk', targetFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) targetOk
  obtain ⟨head, _, total''', -, -, totalOk'', headFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) headOk
  obtain rfl : total' = total := Except.ok.inj (totalOk.symm.trans active)
  obtain rfl : total'' = total' := Except.ok.inj (totalOk'.symm.trans active)
  obtain rfl : total''' = total'' := Except.ok.inj (totalOk''.symm.trans active)
  obtain ⟨matching, matchingOk, inactivityFacts⟩ :=
    getInactivityPenaltyDeltas_getD_of_altair altair (by exact within) penalized
  obtain ⟨eligible, eligibleOk, sourceNo, sourceYes⟩ := sourceFacts j inside
  obtain ⟨eligible₂, eligibleOk₂, targetNo, targetYes⟩ := targetFacts j inside
  obtain ⟨eligible₃, eligibleOk₃, headNo, headYes⟩ := headFacts j inside
  obtain ⟨eligible₄, eligibleOk₄, -, inactivityExempt, inactivityPaid⟩ :=
    inactivityFacts j inside
  obtain rfl : eligible = eligible₂ := Except.ok.inj (eligibleOk.symm.trans eligibleOk₂)
  obtain rfl : eligible = eligible₃ := Except.ok.inj (eligibleOk.symm.trans eligibleOk₃)
  obtain rfl : eligible = eligible₄ := Except.ok.inj (eligibleOk.symm.trans eligibleOk₄)
  -- The loss of the balance is at most the sum of the four penalties.
  have loss : actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤
      (sourcePenalties.getD j 0).toNat + (targetPenalties.getD j 0).toNat +
        (headPenalties.getD j 0).toNat + (inactivityPenalties.getD j 0).toNat := by
    have after_j := (balances j).1 inside
    rcases found : state.balances.data[j]? with _ | balance
    · simp [actualBalanceAt, found]
    · have folded := sub_foldl_le j _ balance ((balances j).2.1 inside balance found)
      simp only [actualBalanceAt, after_j, found, Option.map_some, Option.getD_some]
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil] at folded ⊢
      omega
  cases eligible with
  | false =>
    -- A validator that is not eligible pays nothing.
    left
    have sourceZero := (sourceNo rfl).2
    have targetZero := (targetNo rfl).2
    have headZero := (headNo rfl).2
    have inactivityZero := inactivityExempt (.inl rfl)
    rw [sourceZero, targetZero, headZero, inactivityZero] at loss
    simpa using loss
  | true =>
    right
    obtain ⟨base, baseOk, sourceIn, sourceOut⟩ := sourceYes rfl
    obtain ⟨base₂, baseOk₂, targetIn, targetOut⟩ := targetYes rfl
    obtain ⟨base₃, baseOk₃, headIn, headOut⟩ := headYes rfl
    obtain rfl : base = base₂ := Except.ok.inj (baseOk.symm.trans baseOk₂)
    obtain rfl : base = base₃ := Except.ok.inj (baseOk.symm.trans baseOk₃)
    -- A missed source or target costs its weight, and a missed head costs nothing.
    have sourceLe : (sourcePenalties.getD j 0).toNat ≤
        base.toNat * TIMELY_SOURCE_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat := by
      by_cases mem : j.toUInt64 ∈ source
      · obtain ⟨_, _, _, penalty⟩ := sourceIn mem
        rw [penalty]
        exact Nat.zero_le _
      · exact Nat.le_of_eq (by rw [(sourceOut mem).2]; rfl)
    have targetLe : (targetPenalties.getD j 0).toNat ≤
        base.toNat * TIMELY_TARGET_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat := by
      by_cases mem : j.toUInt64 ∈ target
      · obtain ⟨_, _, _, penalty⟩ := targetIn mem
        rw [penalty]
        exact Nat.zero_le _
      · exact Nat.le_of_eq (by rw [(targetOut mem).2]; rfl)
    have headZero : (headPenalties.getD j 0).toNat = 0 := by
      by_cases mem : j.toUInt64 ∈ head
      · obtain ⟨_, _, _, penalty⟩ := headIn mem
        rw [penalty]
        rfl
      · rw [(headOut mem).2]
        rfl
    -- A missed target also costs the inactivity penalty of the new score.
    have inactivityLe : (inactivityPenalties.getD j 0).toNat ≤
        state.validators.data[j].effectiveBalance.toNat *
          (((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
      by_cases mem : j.toUInt64 ∈ matching
      · rw [inactivityExempt (.inr mem)]
        exact Nat.zero_le _
      · obtain ⟨score, found, penalty⟩ := inactivityPaid rfl mem
        have scoreAfter : (after.inactivityScores altair).data[j]? = some score := by
          rw [scoresAfter]
          exact found
        rw [penalty, scoreAfter]
        exact Nat.le_refl _
    refine ⟨base, by exact eligibleOk, by exact baseOk, ?_⟩
    have split := Nat.div_add_div_le_add_div (x := base.toNat * TIMELY_SOURCE_WEIGHT.toNat)
      (y := base.toNat * TIMELY_TARGET_WEIGHT.toNat) (z := WEIGHT_DENOMINATOR.toNat)
    rw [← Nat.mul_add] at split
    omega

/-- The loss of one balance in the rewards pass, from Altair, inside or outside a leak.

The state is the one before the update of the inactivity scores, with its total active balance.

Either the balance does not fall, or the validator is eligible and has a base reward at that total.

Its loss is then at most the weights of the source and target flags in that base reward.

The inactivity penalty of its new score, or of a zero score when it has none, adds to that loss.

The two weights are applied together, which rounds down once and so can only raise the bound. -/
private theorem balance_sub_le_of_processRewardsAndPenalties (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (active : getTotalActiveBalance state = .ok total) {j : Nat}
    (inside : j < state.validators.data.size) :
    actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j = 0 ∨
      ∃ base, isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true ∧
        getBaseReward state total j.toUInt64 = .ok base ∧
        actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤
          base.toNat * (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) /
              WEIGHT_DENOMINATOR.toNat +
            state.validators.data[j].effectiveBalance.toNat *
              (((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
  (rewardsDebit_cases altair within updated computed active j).2 inside

/-- The total effective balance of the validators eligible for the rewards of the previous epoch.

A validator whose eligibility cannot be decided counts nothing. -/
private def eligibleBalance (state : BeaconState preset fork) : Nat :=
  ∑ j ∈ Finset.range state.validators.data.size,
    match state.validators.data[j]? with
    | some validator =>
      match isEligibleValidator (getPreviousEpoch state) validator with
      | .ok true => validator.effectiveBalance.toNat
      | _ => 0
    | none => 0

/-- The debits of one rewards pass, from Altair, inside or outside a leak.

The eligible balance `E` is that of the state before the update of the inactivity scores.

Each new score must be at most `maxScore`, and `T` is the total active balance of the state.

```text
debits <= (W_source + W_target) * BASE_REWARD_FACTOR * E / (WEIGHT_DENOMINATOR * isqrt T)
          + E * maxScore / (INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT)
```

Each key rounds down on its own, and the sum of those quotients is at most the quotient of the sum.
-/
private theorem balanceDebits_le_of_processRewardsAndPenalties (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (active : getTotalActiveBalance state = .ok total) {maxScore : Nat}
    (capped : ∀ (j : Nat) (score : UInt64),
      (after.inactivityScores altair).data[j]? = some score → score.toNat ≤ maxScore) :
    balanceDebits state after ≤
      (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) *
          preset.BASE_REWARD_FACTOR.toNat * eligibleBalance state /
          (WEIGHT_DENOMINATOR.toNat * total.toNat.sqrt) +
        eligibleBalance state * maxScore /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  -- Short names for the constants of the bound.
  generalize hweights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = weights
  generalize hdenominator : WEIGHT_DENOMINATOR.toNat = denominator
  generalize hquotient : config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = quotient
  generalize hincrement : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = increment
  generalize hfactor : preset.BASE_REWARD_FACTOR.toNat = factor
  generalize hroot : total.toNat.sqrt = root
  obtain ⟨weight, hbalance, heligible⟩ : ∃ weight : Nat → Nat,
      eligibleBalance state = ∑ j ∈ Finset.range state.validators.data.size, weight j ∧
      ∀ j (inside : j < state.validators.data.size),
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true →
          weight j = state.validators.data[j].effectiveBalance.toNat :=
    ⟨_, rfl, fun j inside eligible => by
      simp only [Array.getElem?_eq_getElem inside, eligible]⟩
  rw [hbalance]
  let debit (j : Nat) := actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j
  -- Each loss is at most the bound of its own weight.
  have point : ∀ j ∈ Finset.range state.validators.data.size, debit j ≤
      weight j / increment * (increment * factor / root) * weights / denominator +
        weight j * maxScore / quotient := by
    intro j member
    have inside := Finset.mem_range.mp member
    rcases (rewardsDebit_cases altair within updated computed active j).2 inside with
      zero | ⟨base, eligible, baseOk, bound⟩
    · change actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤ _
      rw [zero]
      exact Nat.zero_le _
    · have baseLe := toNat_getBaseReward_le altair baseOk
        (by rw [toNat_toUInt64_of_lt within inside]; exact Array.getElem?_eq_getElem inside)
      have scoreLe : ((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0 ≤
          maxScore := by
        rcases found : (after.inactivityScores altair).data[j]? with _ | score
        · exact Nat.zero_le _
        · exact capped j score found
      rw [heligible j inside eligible]
      rw [hweights, hdenominator, hquotient] at bound
      rw [hincrement, hfactor, hroot] at baseLe
      refine Nat.le_trans bound (Nat.add_le_add ?_ ?_)
      · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ baseLe)
      · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ scoreLe)
  -- Positions past the registry lose nothing.
  have outside : ∀ j ∈ Finset.range state.balances.data.size, debit j ≠ 0 →
      j < state.validators.data.size := fun j _ nonzero => by
    by_contra past
    exact nonzero
      ((rewardsDebit_cases altair within updated computed active j).1 (Nat.le_of_not_lt past))
  -- The whole increments of the eligible balance bound those of each key.
  have increments : ∑ j ∈ Finset.range state.validators.data.size, weight j / increment ≤
      (∑ j ∈ Finset.range state.validators.data.size, weight j) / increment :=
    sum_div_le _ _ _
  generalize hsum : ∑ j ∈ Finset.range state.validators.data.size, weight j = eligible
    at increments
  have rewardsPart : ∑ j ∈ Finset.range state.validators.data.size,
      weight j / increment * (increment * factor / root) * weights / denominator ≤
        weights * factor * eligible / (denominator * root) := by
    -- Both roundings only lower the product.
    have scaled : eligible / increment * (increment * factor / root) ≤ eligible * factor / root :=
      calc eligible / increment * (increment * factor / root)
          ≤ eligible / increment * (increment * factor) / root :=
            Nat.mul_div_le_mul_div_assoc _ _ _
        _ = eligible / increment * increment * factor / root := by rw [Nat.mul_assoc]
        _ ≤ eligible * factor / root :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _))
    calc ∑ j ∈ Finset.range state.validators.data.size,
          weight j / increment * (increment * factor / root) * weights / denominator
        ≤ (∑ j ∈ Finset.range state.validators.data.size,
            weight j / increment * (increment * factor / root) * weights) / denominator :=
          sum_div_le _ _ _
      _ ≤ eligible / increment * (increment * factor / root) * weights / denominator := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          exact Nat.div_le_div_right
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ increments))
      _ ≤ eligible * factor / root * weights / denominator :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ scaled)
      _ ≤ weights * (eligible * factor) / root / denominator := by
          rw [Nat.mul_comm _ weights]
          exact Nat.div_le_div_right (Nat.mul_div_le_mul_div_assoc _ _ _)
      _ = weights * factor * eligible / (denominator * root) := by
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm root, Nat.mul_assoc, Nat.mul_comm eligible]
  have scorePart : ∑ j ∈ Finset.range state.validators.data.size,
      weight j * maxScore / quotient ≤ eligible * maxScore / quotient := by
    refine Nat.le_trans (sum_div_le _ _ _) (Nat.le_of_eq ?_)
    rw [← Finset.sum_mul, hsum]
  calc balanceDebits state after
      = ∑ j ∈ Finset.range state.balances.data.size, debit j := rfl
    _ = ∑ j ∈ (Finset.range state.balances.data.size).filter
          (· < state.validators.data.size), debit j := (Finset.sum_filter_of_ne outside).symm
    _ ≤ ∑ j ∈ Finset.range state.validators.data.size, debit j :=
        Finset.sum_le_sum_of_subset fun j member => by
          simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
          exact member.2
    _ ≤ ∑ j ∈ Finset.range state.validators.data.size,
          (weight j / increment * (increment * factor / root) * weights / denominator +
            weight j * maxScore / quotient) := Finset.sum_le_sum point
    _ ≤ weights * factor * eligible / (denominator * root) + eligible * maxScore / quotient := by
        rw [Finset.sum_add_distrib]
        exact Nat.add_le_add rewardsPart scorePart

/-! ## No deposit credit to a withdrawable consolidation source

`withdrawnConsolidationCredit` is what a deposit event credits to pending consolidation sources.

It counts only the sources that can already withdraw at the current epoch.

On a run from genesis it is zero at every deposit event.

From Electra, a block deposit only queues a pending deposit, so its event credits nothing.

The pass of the pending deposits starts at a state of the epoch replay.

The stages before it keep `PendingConsolidationsOrdered` at the current epoch.

So every pending source there withdraws after the current epoch, slashed or not.
-/

/-- The credit to withdrawable pending sources is part of the credits of the event. -/
private theorem withdrawnConsolidationCredit_le_credits (event : BalanceEvent preset) :
    withdrawnConsolidationCredit event ≤ event.credits := by
  unfold withdrawnConsolidationCredit BalanceEvent.credits
  split
  · rename_i electra
    rw [funding_sum_zipIdx event.before.state.validators.data.toList (fun v i =>
      if decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch event.before.state).toNat) &&
          (event.before.state.pendingConsolidations electra).data.any
            (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt event.after i - actualBalanceAt event.before i else 0)]
    let credit := fun i => actualBalanceAt event.after i - actualBalanceAt event.before i
    -- A position past the balances after the event credits nothing.
    have outside : ∀ i ∈ Finset.range event.before.state.validators.data.toList.length,
        credit i ≠ 0 → i < event.after.state.balances.data.size := by
      intro i _ positive
      by_contra past
      apply positive
      simp [credit, actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt past)]
    calc _ ≤ ∑ i ∈ Finset.range event.before.state.validators.data.toList.length, credit i :=
          Finset.sum_le_sum fun i _ => by
            cases event.before.state.validators.data.toList[i]? with
            | none => exact Nat.zero_le _
            | some v =>
              simp only [Option.map_some, Option.getD_some]
              split
              · exact Nat.le_refl _
              · exact Nat.zero_le _
      _ = ∑ i ∈ (Finset.range event.before.state.validators.data.toList.length).filter
            (· < event.after.state.balances.data.size), credit i :=
          (Finset.sum_filter_of_ne outside).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset fun i member => by
          simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
          exact member.2
  · exact Nat.zero_le _

/-- An event that starts at an ordered state credits no withdrawable pending source.

Every pending source there withdraws after the current epoch. -/
private theorem withdrawnConsolidationCredit_eq_zero_of_ordered {s t : BeaconState preset fork}
    {source : BalanceSource} {credit debit : Nat}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s) :
    withdrawnConsolidationCredit ⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ = 0 := by
  unfold withdrawnConsolidationCredit
  split
  · rename_i electra
    obtain ⟨-, sources⟩ := holds.2 electra
    refine List.sum_eq_zero fun x mem => ?_
    obtain ⟨⟨v, i⟩, member, rfl⟩ := List.mem_map.mp mem
    have read : s.validators.data[i]? = some v := by
      simpa using List.mem_zipIdx_iff_getElem?.mp member
    dsimp only
    split
    · rename_i due
      simp only [Bool.and_eq_true, decide_eq_true_eq, ← Array.any_toList, List.any_eq_true,
        beq_iff_eq] at due
      obtain ⟨withdrawable, c, mem, index⟩ := due
      obtain ⟨-, -, late⟩ := sources c mem v (by rw [index]; exact read)
      omega
    · rfl
  · rfl

/-- The epoch replay of an ordered state credits no withdrawable pending source.

Each stage keeps the order at the current epoch, so the deposit event starts at an ordered state. -/
private theorem epochBalanceReplay_withdrawnConsolidationCredit {checks : SignatureChecks}
    {s : BeaconState preset fork} {post : BalanceReplay preset fork}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
  let Settled (pre : BalanceReplay preset fork) : Prop :=
    PendingConsolidationsOrdered config (getCurrentEpoch pre.1).toNat pre.1 ∧
      ∀ e ∈ pre.2, e.source = .deposits → withdrawnConsolidationCredit e = 0
  -- A stage moves the state along its edge and records events that are not deposits.
  have moved {k : EpochStage} {pre : BalanceReplay preset fork} {u : BeaconState preset fork}
      (added : List (BalanceEvent preset)) (held : Settled pre)
      (edge : EpochStage.Edge config checks k pre.1 u)
      (quiet : ∀ e ∈ added, e.source ≠ .deposits) : Settled (u, pre.2 ++ added) := by
    refine ⟨edge.pendingConsolidationsOrdered held.1, fun e mem deposit => ?_⟩
    rcases List.mem_append.mp mem with mem | mem
    · exact held.2 e mem deposit
    · exact absurd deposit (quiet e mem)
  -- A carried stage moves the state along its edge and records nothing.
  have carried {k : EpochStage} {action : BeaconState preset fork → Except TransitionError _}
      {pre next : BalanceReplay preset fork} (held : Settled pre)
      (edge : ∀ {u}, action pre.1 = .ok u → EpochStage.Edge config checks k pre.1 u)
      (step : carryBalance action pre = .ok next) : Settled next := by
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨u, computed, rfl⟩ := step
    have settled := moved [] held (edge computed) (fun _ mem => by cases mem)
    rwa [List.append_nil] at settled
  have done : Settled post := by
    refine (epochBalanceReplay_trace ok).transport (fun a b => Settled a → Settled b)
      (fun _ => id) (fun one two => two ∘ one) ?_ ⟨holds, fun _ mem => by cases mem⟩
    intro k member pre next step held
    cases k <;> simp only [epochReplayAction] at step
    case justification => exact carried (k := .justification) held id step
    case registry => exact carried (k := .registry) held id step
    case inactivity =>
      split at step
      · rename_i present
        exact carried (k := .inactivity) held (fun computed => by
          simp only [EpochStage.Edge, present, ↓reduceDIte]
          exact computed) step
      · cases step
        exact held
    case eth1Reset =>
      split at step
      · rename_i present
        exact carried (k := .eth1Reset) held (fun computed => by
          simp only [EpochStage.Edge, present, ↓reduceDIte]
          exact computed) step
      · cases step
        exact held
    case rewards =>
      refine replayRewards_induction Settled (fun held ok => ?_) (fun penalty held ok => ?_)
        held step
      · simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at ok
        obtain ⟨_, _, u, raised, rfl⟩ := ok
        obtain ⟨_, set⟩ := increaseBalance_ok raised
        obtain ⟨_, rfl⟩ := setBalance_ok set
        refine ⟨held.1, fun e mem deposit => ?_⟩
        rcases List.mem_append.mp mem with mem | mem
        · exact held.2 e mem deposit
        · rw [List.mem_singleton.mp mem] at deposit
          cases deposit
      · simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at ok
        obtain ⟨_, _, u, lowered, rfl⟩ := ok
        obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp lowered
        refine ⟨held.1, fun e mem deposit => ?_⟩
        rcases List.mem_append.mp mem with mem | mem
        · exact held.2 e mem deposit
        · rw [List.mem_singleton.mp mem] at deposit
          rcases penalty with rfl | rfl <;> cases deposit
    case slashings =>
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, _, u, slashed, rfl⟩ := step
      exact moved (k := .slashings) _ held slashed (by simp)
    case pendingDeposits =>
      split at step
      · rename_i electra
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨u, deposited, rfl⟩ := step
        have edge : EpochStage.Edge config checks .pendingDeposits pre.1 u := by
          simp only [EpochStage.Edge, electra, ↓reduceDIte]
          exact deposited
        refine ⟨edge.pendingConsolidationsOrdered held.1, fun e mem deposit => ?_⟩
        rcases List.mem_append.mp mem with mem | mem
        · exact held.2 e mem deposit
        · rw [List.mem_singleton.mp mem]
          exact withdrawnConsolidationCredit_eq_zero_of_ordered held.1
      · cases step
        exact held
    case pendingConsolidations =>
      split at step
      · rename_i electra
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨u, consolidated, rfl⟩ := step
        exact moved (k := .pendingConsolidations) _ held
          (by simp only [EpochStage.Edge, electra, ↓reduceDIte]; exact consolidated) (by simp)
      · cases step
        exact held
    all_goals simp [EpochStage.prefixStages] at member
  exact done.2

/-- The deposit events of one step before Gloas credit no withdrawable pending source.

A block deposit has no credit limit from Electra, and its credits are within that limit.

A slot runs the epoch replay from an ordered state, and its upgrades record no deposit. -/
private theorem stepBalanceEvents_withdrawnConsolidationCredit {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (step : Step config checks x y)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events)
    (bounded : EventsBounded events) :
    ∀ e ∈ events, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
  have sourceEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due blockOk =>
    have quiet := funding_block_events sourceEarly engine signed.message
      (Step.balanceEvents_block sourceEarly ok)
    intro e mem deposit
    by_cases electra : .pectra ≤ e.before.fork
    · have zero := quiet e mem deposit electra
      have within := (bounded e mem).1
      have part := withdrawnConsolidationCredit_le_credits e
      omega
    · rw [withdrawnConsolidationCredit, dite_eq_right electra]
  | slot across =>
    -- The slot replays the epoch only at its last slot, then records the upgrade crossings.
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp across
    have steps := advanceOk
    simp only [advanceSlot, bind_ok_iff] at steps
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochedOk, -⟩ := steps
    obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
    have crossed : ∀ e ∈ crossings, e.source = .deposits →
        withdrawnConsolidationCredit e = 0 := fun e mem deposit =>
      absurd ((upgradeBalanceReplay_crossing crossingOk e mem).symm.trans deposit) (by decide)
    unfold epochIfLast at epochedOk
    split at epochedOk
    · rename_i last
      obtain ⟨_, _, epochEvents, replayOk, -⟩ :=
        epochBalanceReplay_result cached epoched sourceEarly epochedOk
      rw [Step.balanceEvents_epoch_slot across cachedOk nextOk last replayOk advanceOk
        crossingOk] at ok
      cases ok
      intro e mem
      rcases List.mem_append.mp mem with mem | mem
      · have ordered : PendingConsolidationsOrdered config (getCurrentEpoch cached).toNat
            cached := by
          obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
          exact shared.pendingConsolidationsOrdered genesis sourceEarly delay
        exact epochBalanceReplay_withdrawnConsolidationCredit ordered replayOk e mem
      · exact crossed e mem
    · rename_i last
      have replayed : (Step.slot across).balanceEvents = .ok ([] ++ crossings) := by
        simp only [Step.balanceEvents, cachedOk, nextOk, last, ↓reduceIte, advanceOk,
          crossingOk, bind, Except.bind, pure, Except.pure]
      rw [replayed] at ok
      cases ok
      simpa using crossed

/-- Lemma WC: on a run from genesis, no deposit event credits a withdrawable pending source.

Every pending consolidation source of a reachable state withdraws after the current epoch.

The epoch pass of the pending deposits starts at such a state, and block deposits credit nothing.

It covers the deposit events, the only ones whose `fundingCredit` reads this credit. -/
private theorem _root_.EthLib.Consensus.Run.withdrawnConsolidationCredit_eq_zero
    {checks : SignatureChecks} {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {high : Nat} {events : List (BalanceEvent preset)}
    (ok : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
  -- Every event of the run is within its own limits.
  obtain ⟨recorded, recordedOk, bounded⟩ :=
    Run.balanceEvents_bounded shared tail genesis early high
  rw [ok] at recordedOk
  cases recordedOk
  have key : ∀ {z : ForkedBeaconState preset} (part : Run config checks x z),
      z.fork < .glamsterdam → ∀ {found : List (BalanceEvent preset)},
        part.balanceEvents high = .ok found → EventsBounded found →
          ∀ e ∈ found, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
    intro z part
    induction part with
    | nil =>
      intro _ found ok _
      simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact fun _ mem => by cases mem
    | snoc pre step ih =>
      intro early found ok bounded
      simp only [Run.balanceEvents, bind_ok_iff] at ok
      obtain ⟨prior, priorOk, rest⟩ := ok
      have before := Nat.lt_of_le_of_lt step.chainStep.fork_le early
      split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        intro e mem
        rcases List.mem_append.mp mem with mem | mem
        · exact ih before priorOk (fun e member => bounded e (List.mem_append_left _ member))
            e mem
        · exact stepBalanceEvents_withdrawnConsolidationCredit (shared.append pre) genesis step
            early delay addedOk (fun e member => bounded e (List.mem_append_right _ member)) e mem
      · cases rest
        exact ih before priorOk bounded
  exact key tail early ok bounded

/-! ## The a priori branch drift

The drift `f` of a branch is a function of numbers read at its reference state `x`.

These numbers are the observables below, and the window `H` with the epochs `H₁` before Electra.

`f` itself reads only those numbers and the constants of the preset and the configuration.

Its index `t` runs over the epochs `0` to `H + 1` of the window.

"Before the fork" means `t < H₁`.
-/

/-- The active-count path before the fork: `A_0` is given, and `A_{t+1} = A_t + cc(A_t)`. -/
private def countPath (config : Config) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 => countPath config start t + cohortCap config (countPath config start t)

/-- The balance churn `δ(T)` from Electra, in Gwei, at a total active stake `T`.

It is the stake over the churn quotient, rounded down to an increment, and at least the minimum. -/
private def balanceChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (total / config.CHURN_LIMIT_QUOTIENT.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)

/-- The activation and exit part `A_E(T)` of the balance churn. -/
private def exitChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (balanceChurn preset config total)

/-- The consolidation part `C(T)` of the balance churn. -/
private def consolidationChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  balanceChurn preset config total - exitChurn preset config total

/-- The whistleblower quotient `WQ` of the window.

A window before the fork takes the smaller of the two quotients. -/
private def whistleblowerQuotient (preset : Preset) (forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then
    min preset.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
      preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat
  else preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat

/-- The minimum slashing penalty quotient `MSPQ` of the window.

A window before the fork takes the least quotient of Phase 0, Altair and Bellatrix. -/
private def slashingQuotient (preset : Preset) (forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then
    min (min preset.MIN_SLASHING_PENALTY_QUOTIENT.toNat
      preset.MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR.toNat)
      preset.MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX.toNat
  else preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat

/-- The divisor of the leak penalty: the score bias times the least inactivity penalty quotient. -/
private def leakDivisor (preset : Preset) (config : Config) : Nat :=
  config.INACTIVITY_SCORE_BIAS.toNat *
    min (min preset.INACTIVITY_PENALTY_QUOTIENT.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat)
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat

/-- The activations of the window, `nAct`.

Before the fork they are the growth of the active-count path.

From Electra each needs `MIN_ACTIVATION_BALANCE` of funding.

That funding comes from `Pre`, from `K`, or from the deposit churn of each epoch. -/
private def windowActivations (preset : Preset) (config : Config)
    (count scheduled pending carry horizon forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then countPath config (count + scheduled) (horizon + 1) - count
  else (pending + carry + config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat * (horizon + 2)) /
    preset.MIN_ACTIVATION_BALANCE.toNat

/-- The fixed whistleblower allowance `Ω` of the window.

Every key that is slashable in the window pays it at most its cap over `WQ`, once.

Those keys are active at `x`, activate in the window, or are exited but not yet withdrawable.

Before the fork every cap of an active key is `MIN_ACTIVATION_BALANCE`.

After it an active key may switch to compounding, so its cap is `MAX_EFFECTIVE_BALANCE_ELECTRA`.

An exited key cannot switch, so `inactive` counts it at its cap at `x`. -/
private def whistleblowerAllowance (preset : Preset) (config : Config)
    (count scheduled pending carry inactive horizon forkEpochs : Nat) : Nat :=
  ((count + windowActivations preset config count scheduled pending carry horizon forkEpochs) *
      (if 0 < forkEpochs then preset.MIN_ACTIVATION_BALANCE.toNat
        else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) + inactive) /
    whistleblowerQuotient preset forkEpochs

/-- The ceiling `T⁺_t` on the total active stake.

Before the fork it is `MIN_ACTIVATION_BALANCE` times the active-count path.

From Electra it starts at the funded stake plus `K` plus `Ω`.

Each epoch then adds twice the issuance envelope and `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.

The factor two covers one epoch's rewards, proposer rewards for two epochs of flags, and sync. -/
private def stakeCeiling (preset : Preset) (config : Config)
    (count scheduled pending carry inactive funded horizon forkEpochs : Nat) : Nat → Nat
  | 0 =>
    if 0 < forkEpochs then preset.MIN_ACTIVATION_BALANCE.toNat * (count + scheduled)
    else funded + carry +
      whistleblowerAllowance preset config count scheduled pending carry inactive horizon forkEpochs
  | t + 1 =>
    if 0 < forkEpochs ∧ t + 1 ≤ forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat * countPath config (count + scheduled) (t + 1)
    else
      let previous := stakeCeiling preset config count scheduled pending carry inactive funded
        horizon forkEpochs t
      previous + 2 * issuanceEnvelope preset previous +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- The exits `nX_t` of epoch `t`.

Before the fork they are the count churn at the end of the path, in `MIN_ACTIVATION_BALANCE`.

From Electra they are `A_E` of the ceiling. -/
private def exitFlow (preset : Preset) (config : Config) (count scheduled horizon forkEpochs : Nat)
    (ceiling : Nat → Nat) (t : Nat) : Nat :=
  if t < forkEpochs then
    preset.MIN_ACTIVATION_BALANCE.toNat *
      cohortCap config (countPath config (count + scheduled) (horizon + 1))
  else exitChurn preset config (ceiling t)

/-- The consolidations `nC_t` of epoch `t`: none before the fork, the constant cap `Cc` after.

`Cc` is the consolidation churn at the last ceiling `T⁺_{H+1}`. -/
private def consolidationFlow (preset : Preset) (config : Config) (horizon forkEpochs : Nat)
    (ceiling : Nat → Nat) (t : Nat) : Nat :=
  if t < forkEpochs then 0 else consolidationChurn preset config (ceiling (horizon + 1))

/-- The non-slashing penalty `λ_t` of epoch `t` over a stake `weight`, at a floor `lower`.

The first part is `ω · BRF · weight / sqrt(lower)`, with `ω = (3 + BRPE) / BRPE`.

The second part is the leak penalty at the score `σ + bias · (t + 1)`. -/
private def epochPenalty (preset : Preset) (config : Config) (score weight lower t : Nat) : Nat :=
  (3 + BASE_REWARDS_PER_EPOCH.toNat) * preset.BASE_REWARD_FACTOR.toNat * weight /
      (BASE_REWARDS_PER_EPOCH.toNat * lower.sqrt) +
    weight * (score + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) / leakDivisor preset config

/-- The floor `T⁻_t` on the total active stake.

Each epoch takes its exits, its consolidations and its penalty from it. -/
private def floorPath (preset : Preset) (config : Config) (score : Nat)
    (weight outflow : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 =>
    let lower := floorPath preset config score weight outflow start t
    lower - outflow t - epochPenalty preset config score (weight t) lower t

/-- The keys that a branch may hold at the end of the window, `N⁺`.

Growth of the ceiling above `W` adds at most one key per `MIN_ACTIVATION_BALANCE`, rounded up. -/
private def finalCount (preset : Preset) (stake count last : Nat) : Nat :=
  count + (last - stake + preset.MIN_ACTIVATION_BALANCE.toNat - 1) /
    preset.MIN_ACTIVATION_BALANCE.toNat

/-- The start `T⁻_0` of the floor.

It is `W` less the slashed stake, the slack and one increment per key of `N⁺`.

It also loses the slashing penalties of the ceiling, the due partials and the departures. -/
private def floorStart (preset : Preset)
    (stake slashed count slack departures partials last forkEpochs : Nat) : Nat :=
  stake - slashed - slack -
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat * finalCount preset stake count last -
    last / slashingQuotient preset forkEpochs - partials - departures

/-- The floor path of a window, with every input read from the observables. -/
private def windowFloor (preset : Preset) (config : Config)
    (stake slashed penalised count score slack carry pending scheduled departures partials
      inactive funded horizon forkEpochs : Nat) : Nat → Nat :=
  let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded horizon
    forkEpochs
  floorPath preset config score (fun t => ceiling t + penalised)
    (fun t => exitFlow preset config count scheduled horizon forkEpochs ceiling t +
      consolidationFlow preset config horizon forkEpochs ceiling t)
    (floorStart preset stake slashed count slack departures partials (ceiling (horizon + 1))
      forkEpochs)

/-- The conditions under which `aprioriDrift` uses its formula.

The divisors are positive, and the whistleblower quotient exceeds one.

The minimum churn per epoch is positive.

With a zero minimum, a queue still lets one validator exit per epoch.

The formula does not charge that exit.

The withdrawal delay is at least two epochs.

The window ends before half the slashings vector, and the floor stays positive through it.

The last condition is temporary.

A window from a state before Electra must end before the fork. -/
private abbrev aprioriGuard (preset : Preset) (config : Config)
    (stake slashed penalised count score slack carry pending scheduled departures partials
      inactive funded horizon forkEpochs : Nat) : Prop :=
  0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧ 0 < config.CHURN_LIMIT_QUOTIENT.toNat ∧
    0 < config.MIN_PER_EPOCH_CHURN_LIMIT.toNat ∧
    0 < preset.MIN_ACTIVATION_BALANCE.toNat ∧ 0 < preset.downwardBand ∧
    0 < leakDivisor preset config ∧ 0 < slashingQuotient preset forkEpochs ∧
    1 < whistleblowerQuotient preset forkEpochs ∧
    2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ∧
    horizon + 2 < preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 ∧
    (∀ t < horizon + 2, 0 < windowFloor preset config stake slashed penalised count score slack
      carry pending scheduled departures partials inactive funded horizon forkEpochs t) ∧
    (forkEpochs = 0 ∨ horizon + 2 ≤ forkEpochs)

/-- The departures `Dnew` that the queues admit in the window, from their ends at `x`.

It is the carry of the queues, and the churn of each epoch from the end of each queue on.

Before the fork the exit churn is the count churn at the end of the active-count path.

From Electra it is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`, and consolidations add `Cc`.

Two `MAX_EFFECTIVE_BALANCE_ELECTRA` cover one departure at each end of the window. -/
private def departureBudget (preset : Preset) (config : Config)
    (count scheduled pending carry inactive funded queued exitEnd consolidationEnd horizon
      forkEpochs : Nat) : Nat :=
  let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded
    horizon forkEpochs
  let exitRate := if 0 < forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat *
        cohortCap config (countPath config (count + scheduled) (horizon + 1))
    else config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let consolidationRate := if 0 < forkEpochs then 0
    else consolidationChurn preset config (ceiling (horizon + 1))
  queued + (horizon + 2 - exitEnd) * exitRate +
    (horizon + 2 - consolidationEnd) * consolidationRate +
    2 * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- The a priori drift `f` of a branch, from the observables of its reference state.

```text
f = 2 (dep + D + Λ + ρ) + act + cred + 2 B
```

`dep` is every departure of the window, `D` the non-slashing penalties and `Λ` the slack.

`ρ` is one increment for each key whose effective balance may fall.

`act` is the stake that may activate, `cred` the credits and `B` the boundary stake.

Without the guard, `f` is the unslashed stake `W - Z`, which makes the bound trivial. -/
private def aprioriDrift (preset : Preset) (config : Config)
    (stake slashed penalised count high score slack excess carry pending scheduled departures
      partials credits exitEnd consolidationEnd queued boundary inactive funded
      horizon forkEpochs : Nat) : Nat :=
  if aprioriGuard preset config stake slashed penalised count score slack carry pending scheduled
      departures partials inactive funded horizon forkEpochs then
    let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let down := preset.downwardBand
    let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded
      horizon forkEpochs
    let last := ceiling (horizon + 1)
    let exits := exitFlow preset config count scheduled horizon forkEpochs ceiling
    let consolidations := consolidationFlow preset config horizon forkEpochs ceiling
    let floor := windowFloor preset config stake slashed penalised count score slack carry pending
      scheduled departures partials inactive funded horizon forkEpochs
    let allowance := whistleblowerAllowance preset config count scheduled pending carry inactive
      horizon forkEpochs
    -- Dnew: the queue carry and the churn of each epoch from the ends of the queues.
    let queues := departureBudget preset config count scheduled pending carry inactive funded
      queued exitEnd consolidationEnd horizon forkEpochs
    let dep := queues + partials + departures
    -- D: the non-slashing penalties of the epochs `0` to `H`.
    let penalties := ((List.range (horizon + 1)).map fun t =>
      epochPenalty preset config score (ceiling t + penalised) (floor t) t).sum
    -- ρ: one increment per key whose effective balance may fall below its value at `x`.
    let paid := partials +
      (((List.range (horizon + 2)).filter (max exitEnd forkEpochs ≤ ·)).map exits).sum
    let grown := (last - stake + increment - 1) / increment
    let falling := min (finalCount preset stake count last)
      ((slack + penalties) / down + min (paid / down) (high + grown))
    let rounding := increment * falling
    -- act: activations, including the headroom of each key below the cap before the fork.
    let headroom := if 0 < forkEpochs then
      preset.MAX_EFFECTIVE_BALANCE.toNat * count - stake else 0
    let act := pending + carry + ((List.range (horizon + 1)).map exits).sum + headroom
    -- cred: excess, due consolidation credits, Ω, issuance and new consolidation credits.
    let issuance := (((List.range (horizon + 1)).filter (forkEpochs ≤ ·)).map
      fun t => 2 * issuanceEnvelope preset (ceiling t)).sum
    let moved := (((List.range
      (horizon + 2 - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)).filter
        (max consolidationEnd forkEpochs ≤ ·)).map consolidations).sum
    let cred := excess + credits + allowance + issuance + moved
    -- B: the boundary stake at the end of the window.
    let edge := boundary + 2 * max (exits horizon + consolidations horizon)
      (exits (horizon + 1) + consolidations (horizon + 1)) +
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    2 * (dep + penalties + slack + rounding) + act + cred + 2 * edge
  else stake - slashed

/-! ## The observables of a reference state

Each observable is a number read at the reference state `x` of a branch.

It is a parameter of `aprioriDrift`, not a premise.
-/

/-- `W`: the active effective stake at `x`, slashed keys included. -/
private noncomputable def refStake (x : ForkedBeaconState preset) : Nat :=
  Models.stake (effectiveWeight x.state) (activeKeys x.state)

/-- `Z`: the active effective stake at `x` of the slashed keys. -/
private noncomputable def slashedActiveStake (x : ForkedBeaconState preset) : Nat :=
  refStake x - Models.stake (effectiveWeight x.state) (unslashedKeys x.state)

/-- `Y`: the effective stake of slashed, inactive keys that are not yet withdrawable. -/
private def slashedPenalisedStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if v.slashed && !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.withdrawableEpoch) then
      v.effectiveBalance.toNat else 0).sum

/-- `N`: the number of active keys at `x`. -/
private noncomputable def refCount (x : ForkedBeaconState preset) : Nat :=
  (activeKeys x.state).card

/-- `Nhi`: the number of active keys at `x` with more than `MIN_ACTIVATION_BALANCE` effective. -/
private noncomputable def highKeys (x : ForkedBeaconState preset) : Nat := by
  classical
  exact ((activeKeys x.state).filter fun key =>
    preset.MIN_ACTIVATION_BALANCE.toNat < effectiveWeight x.state key).card

/-- `σ`: the larger of the largest inactivity score and the bias times the finality delay.

Before Altair there is no score. -/
private def startScore (config : Config) (x : ForkedBeaconState preset) : Nat :=
  max (if altair : .altair ≤ x.fork then
      ((x.state.inactivityScores altair).data.toList.map (·.toNat)).foldr max 0 else 0)
    (config.INACTIVITY_SCORE_BIAS.toNat *
      ((getPreviousEpoch x.state).toNat - x.state.finalizedCheckpoint.epoch.toNat))

/-- `Λ`: the effective balance above the balance, summed over the active validators at `x`. -/
private def startSlack (x : ForkedBeaconState preset) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    effectiveAt x i.toNat - actualBalanceAt x i.toNat).sum

/-- `Pre`: the stake of validators that are neither active nor exited at `x`.

Each counts the larger of its effective balance and its balance up to its cap. -/
private def preActiveStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.exitEpoch) then
      max (effectiveAt x i)
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    else 0).sum

/-- `Sx`: the number of validators whose activation epoch is set and after `x`. -/
private def scheduledCount (x : ForkedBeaconState preset) : Nat :=
  x.state.validators.data.toList.countP fun v =>
    decide (getCurrentEpoch x.state < v.activationEpoch) && v.activationEpoch != FAR_FUTURE_EPOCH

/-- `Sch`: the effective balance of active validators whose exit epoch is within the window. -/
private def scheduledDepartures (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if isActiveValidator v (getCurrentEpoch x.state) &&
        decide (v.exitEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1) then
      v.effectiveBalance.toNat else 0).sum

/-- `Πp`: the pending partial withdrawals that are withdrawable within the window.

Overdue entries count too, and there are none before Electra. -/
private def duePartials (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    ((x.state.pendingPartialWithdrawals electra).data.toList.map fun w =>
      if w.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1 then
        w.amount.toNat else 0).sum
  else 0

/-- `Πc`: the credits of pending consolidations whose source is withdrawable within the window.

Each credit is the smaller of the balance and the effective balance of its source. -/
private def dueCredits (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    ((x.state.pendingConsolidations electra).data.toList.map fun c =>
      match x.state.validators.data[c.sourceIndex.toNat]? with
      | some v =>
        if v.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1 then
          min (actualBalanceAt x c.sourceIndex.toNat) v.effectiveBalance.toNat else 0
      | none => 0).sum
  else 0

/-- `Bd`: the largest effective balance that exits in two adjacent epochs of the window. -/
private def boundaryLoad (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  ((List.range (horizon + 1)).map fun t =>
    (x.state.validators.data.toList.map fun v =>
      if v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t ∨
          v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t + 1 then
        v.effectiveBalance.toNat else 0).sum).foldr max 0

/-- `XS`: the caps of the unslashed validators that have exited but are not yet withdrawable.

The cap is the largest effective balance of the credentials at `x`. -/
private def slashableInactiveStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if !v.slashed && decide (v.exitEpoch ≤ getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.withdrawableEpoch) then
      (withdrawalMaxEffectiveBalance preset x.fork v).toNat else 0).sum

/-- `H₁`: the epochs of the window before Electra, and zero from Electra on.

A state before Electra whose epoch has reached the fork epoch never upgrades.

The upgrade fires only at the boundary of that epoch.

`H₁ = 1` then fails the no-crossing clause of the guard, so the drift falls back to `W - Z`. -/
private def forkEpochs (config : Config) (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if x.fork < .pectra then
    if (getCurrentEpoch x.state).toNat < config.ELECTRA_FORK_EPOCH.toNat then
      min (driftHorizon x high + 2)
        (config.ELECTRA_FORK_EPOCH.toNat - (getCurrentEpoch x.state).toNat)
    else 1
  else 0

/-- The guard of a branch from `x` through `high + 1`, with every observable read at `x`. -/
private noncomputable def aprioriGuardAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Prop :=
  aprioriGuard preset config (refStake x) (slashedActiveStake x) (slashedPenalisedStake x)
    (refCount x) (startScore config x) (startSlack x) (fundingCarry x) (preActiveStake x)
    (scheduledCount x) (scheduledDepartures x (driftHorizon x high))
    (duePartials x (driftHorizon x high)) (slashableInactiveStake x) (fundedStake x)
    (driftHorizon x high) (forkEpochs config x high)

/-- The drift `f` of a branch from `x` through `high + 1`, with every observable read at `x`. -/
private noncomputable def aprioriDriftAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Nat :=
  aprioriDrift preset config (refStake x) (slashedActiveStake x) (slashedPenalisedStake x)
    (refCount x) (highKeys x) (startScore config x) (startSlack x) (initialExcess x)
    (fundingCarry x) (preActiveStake x) (scheduledCount x)
    (scheduledDepartures x (driftHorizon x high)) (duePartials x (driftHorizon x high))
    (dueCredits x (driftHorizon x high))
    -- `eX` and `eC`: the start of each queue less the current epoch, zero before Electra.
    (exitQueueStart x - (getCurrentEpoch x.state).toNat)
    (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
    (queueCarry x high) (boundaryLoad x (driftHorizon x high)) (slashableInactiveStake x)
    (fundedStake x) (driftHorizon x high) (forkEpochs config x high)

/-! ## The departures of a branch

The departures that a branch charges in its window fit the budget `Dnew` of the drift.

This is the bound of `departure_charges_le_window_from` with the counts and rates of the drift.

Two facts of the window are hypotheses here, since the ceiling of the active stake gives them.

Before the fork each step of the window starts with at most `A_{H+1}` active validators.

From Electra each step of the window starts with a consolidation churn of at most `Cc`.
-/

/-- A tail splits after its last step that starts by epoch `high + 1`.

The second part starts after `high + 1`, so it charges only exits after `high + 1`. -/
private theorem window_cut {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat) :
    ∃ (m : ForkedBeaconState preset) (cut : Run config checks x m) (rest : Run config checks m y),
      tail = cut.append rest ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), cut.Contains step →
        (getCurrentEpoch u.state).toNat ≤ high + 1) ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), rest.Contains step →
        high + 1 < (getCurrentEpoch u.state).toNat) ∧
      ∀ charge ∈ rest.departureCharges, high + 1 < charge.epoch := by
  induction tail with
  | nil => exact ⟨x, .nil, .nil, rfl, fun _ member => (by cases member),
      fun _ member => (by cases member),
      fun _ member => by simp [Run.departureCharges] at member⟩
  | @snoc b c pre step ih =>
    obtain ⟨m, cut, rest, rfl, inside, outside, later⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    by_cases within : (getCurrentEpoch b.state).toNat ≤ high + 1
    · -- The tail so far starts by `high + 1` at its end, so its second part is empty.
      cases rest with
      | nil =>
        refine ⟨c, cut.snoc step, .nil, rfl, fun later member => ?_,
          fun _ member => (by cases member),
          fun _ member => by simp [Run.departureCharges] at member⟩
        cases member with
        | last => exact within
        | earlier member => exact inside later member
      | snoc rest last =>
        have after := outside last (.last _ _)
        have ordered := UInt64.le_iff_toNat_le.mp last.chainStep.currentEpoch_le
        omega
    · refine ⟨m, cut, rest.snoc step, rfl, inside, fun later member => ?_, fun charge member => ?_⟩
      · cases member with
        | last => omega
        | earlier member => exact outside later member
      · rcases List.mem_append.mp member with old | latest
        · exact later charge old
        · have lower := departureCharges_epoch_ge step early charge latest
          omega

/-- The departures that a branch charges in its window fit the budget `Dnew`.

The window runs from the current epoch of `x` to `high + 1`.

A branch from Electra is charged its queue carry and the Electra churn from each queue end.

A branch before Electra ends before the fork epoch, so it is charged only the count churn. -/
private theorem departures_le_budget {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high : Nat) (guard : aprioriGuardAt config x high)
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat ≤ high + 1 → u.fork < .pectra →
        activeCount u.state ≤
          countPath config (refCount x + scheduledCount x) (driftHorizon x high + 1))
    (rates : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat ≤ high + 1 → .pectra ≤ u.fork →
        ∀ rate : Gwei, getConsolidationChurnLimit config u.state = .ok rate →
        rate.toNat ≤ consolidationChurn preset config
          (stakeCeiling preset config (refCount x) (scheduledCount x) (preActiveStake x)
            (fundingCarry x) (slashableInactiveStake x) (fundedStake x) (driftHorizon x high)
            (forkEpochs config x high) (driftHorizon x high + 1))) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      departureBudget preset config (refCount x) (scheduledCount x) (preActiveStake x)
        (fundingCarry x) (slashableInactiveStake x) (fundedStake x) (queueCarry x high)
        (exitQueueStart x - (getCurrentEpoch x.state).toNat)
        (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
        (driftHorizon x high) (forkEpochs config x high) := by
  -- D-Q reads only the steps of the window, and the steps after it charge later exits.
  obtain ⟨m, cut, rest, rfl, inside, -, later⟩ := window_cut tail early high
  have cutEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have bound := departure_charges_le_window_from shared cut genesis caps cutEarly high _ _
    (fun step member => counted step ((Run.contains_append _ _ _).mpr (.inl member))
      (inside step member))
    (fun step member => rates step ((Run.contains_append _ _ _).mpr (.inl member))
      (inside step member))
  have after : ((rest.departureCharges.filter fun c => c.epoch ≤ high + 1).map
      (·.amount)).sum = 0 := by
    rw [List.filter_eq_nil_iff.mpr fun c member => by
      simpa using later c member]
    rfl
  rw [Run.departureCharges_append, List.filter_append, List.map_append, List.sum_append, after,
    Nat.add_zero]
  obtain ⟨-, -, minimum, -, -, -, -, -, -, -, -, crossing⟩ := guard
  -- The written-out carry of D-Q is `queueCarry`.
  change _ ≤ queueCarry x high + _ + _ + _ at bound
  simp only [departureBudget]
  generalize countPath config (refCount x + scheduledCount x) (driftHorizon x high + 1) = A
    at bound ⊢
  generalize consolidationChurn preset config (stakeCeiling preset config (refCount x)
    (scheduledCount x) (preActiveStake x) (fundingCarry x) (slashableInactiveStake x)
    (fundedStake x) (driftHorizon x high) (forkEpochs config x high)
    (driftHorizon x high + 1)) = Cc at bound ⊢
  have horizon : driftHorizon x high = high + 2 - (getCurrentEpoch x.state).toNat := rfl
  rw [horizon] at crossing ⊢
  by_cases electra : .pectra ≤ x.fork
  · -- From Electra the count term is off, and each churn counts from its queue end on.
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    have zero : forkEpochs config x high = 0 := by simp [forkEpochs, notBefore]
    simp only [zero, lt_self_iff_false, ↓reduceIte, notBefore, Nat.mul_zero,
      Nat.add_zero] at bound ⊢
    have from_ (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) ≤
          high + 2 - (getCurrentEpoch x.state).toNat + 2 -
            (start - (getCurrentEpoch x.state).toNat) := by omega
    have exitTerm := Nat.mul_le_mul_right
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (from_ (exitQueueStart x))
    have consolidationTerm := Nat.mul_le_mul_right Cc (from_ (consolidationQueueStart x))
    omega
  · -- Before Electra the no-crossing clause puts the fork epoch after the window.
    have before : x.fork < .pectra := Nat.lt_of_not_ge electra
    have positive : 0 < forkEpochs config x high := by
      simp only [forkEpochs, before, ↓reduceIte, driftHorizon]
      split <;> omega
    have ends : high + 2 - (getCurrentEpoch x.state).toNat + 2 ≤ forkEpochs config x high :=
      crossing.resolve_left (Nat.ne_of_gt positive)
    have late : ¬ config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1 := by
      simp only [forkEpochs, before, ↓reduceIte, driftHorizon] at ends
      split at ends <;> omega
    have starts : exitQueueStart x = (getCurrentEpoch x.state).toNat := by
      simp [exitQueueStart, electra]
    -- A positive minimum churn makes the floor of one in the count churn redundant.
    have floor : max 1 (cohortCap config A) = cohortCap config A :=
      Nat.max_eq_right (Nat.le_trans minimum (Nat.le_max_left _ _))
    have rate := Nat.mul_le_mul_left (cohortCap config A)
      (UInt64.le_iff_toNat_le.mp caps.activation)
    have empty (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) = 0 := by omega
    simp only [before, ↓reduceIte, starts, Nat.max_self, Nat.add_zero, positive, floor,
      Nat.sub_self, empty, Nat.zero_mul] at bound ⊢
    have horizon := Nat.mul_le_mul
      (show high + 2 - (getCurrentEpoch x.state).toNat ≤
        high + 2 - (getCurrentEpoch x.state).toNat + 2 - 0 by omega)
      (show cohortCap config A * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat * cohortCap config A by
        rw [Nat.mul_comm preset.MIN_ACTIVATION_BALANCE.toNat]; exact rate)
    omega

end EthLib.Consensus.DirectSafety
