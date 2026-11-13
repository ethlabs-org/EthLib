module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
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

end EthLib.Consensus.DirectSafety
