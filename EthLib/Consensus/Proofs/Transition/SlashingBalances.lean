module

public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: the balance effects of a slashing, at every fork

A slashed validator pays a penalty, and the proposer that includes the slashing gets a reward.

The penalty comes in `slashValidator`, when the validator is slashed.

It is the effective balance over `MIN_SLASHING_PENALTY_QUOTIENT` of the fork.

The same call pays the reward: the effective balance over the whistleblower quotient of the fork.

The proposer is the whistleblower by default, so the proposer gets the whole reward.

The reward splits into a proposer part and a whistleblower part.

Before Altair the proposer part is the reward over `PROPOSER_REWARD_QUOTIENT`.

From Altair it is `PROPOSER_WEIGHT / WEIGHT_DENOMINATOR` of the reward.

Each theorem here gives the balances after the step at every index, in natural numbers.

A penalty saturates at zero, since a balance cannot go below zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config}

/-- Starting an exit keeps the balances. -/
theorem initiateValidatorExit_balances {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    after.balances = state.balances := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · obtain ⟨_, rfl⟩ := setValidator_ok set
    exact (exitQueue_validators queue).2

/-! ## The payout of one slashing -/

/-- The reward of a slashing: the effective balance over the whistleblower quotient of the fork. -/
def whistleblowerReward (preset : Preset) (fork : Base.Fork) (validator : Validator) : Gwei :=
  validator.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT

/-- The proposer part of a reward is at most the reward.

So the whistleblower part, the reward minus the proposer part, does not wrap. -/
theorem proposerShare_le {reward share : Gwei}
    (computed : proposerShare preset fork reward = .ok share) : share ≤ reward := by
  unfold proposerShare at computed
  split at computed
  · simp only [bind_ok_iff, liftArith, mapError_ok_iff, mulChecked_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨product, ⟨_, exact⟩, rfl⟩ := computed
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_div, exact]
    -- `PROPOSER_WEIGHT / WEIGHT_DENOMINATOR` is `8 / 64`, below one.
    simp only [PROPOSER_WEIGHT, WEIGHT_DENOMINATOR, UInt64.reduceToNat]
    omega
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]
    exact Nat.div_le_self _ _

/-- Starting an exit keeps the effective balance of the validator. -/
theorem initiateValidatorExit_effectiveBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (computed : initiateValidatorExit config state index = .ok after) :
    ∃ exiting, getValidator after index = .ok exiting ∧
      exiting.effectiveBalance = validator.effectiveBalance := by
  obtain ⟨read, readOk, ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact ⟨validator, found, rfl⟩
  · have same : read = validator := Except.ok.inj (readOk.symm.trans found)
    subst same
    exact ⟨_, getValidator_setValidator_self set, rfl⟩

/-- A slashing pays its whole reward to the proposer.

`penalized` is the state just before the reward.

The validator has started to exit, is slashed, and has paid the first penalty.

The proposer of that state gets the reward in two parts.

It gets its own part, then the whistleblower part, since it is the whistleblower too.

No other balance changes, and the sum does not overflow, since the call succeeded.

`penalized` has the balances of the state before the call, with the first penalty at the index.
-/
theorem slashValidator_payout {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (found : getValidator state index = .ok validator)
    (computed : slashValidator config state index = .ok after) :
    ∃ (penalized : BeaconState preset fork) (proposer : ValidatorIndex) (share : Gwei)
      (inside : proposer.toNat < penalized.balances.data.size),
      getBeaconProposerIndex penalized = .ok proposer ∧
      proposerShare preset fork (whistleblowerReward preset fork validator) = .ok share ∧
      share ≤ whistleblowerReward preset fork validator ∧
      after.validators = penalized.validators ∧
      penalized.balances.data[proposer.toNat].toNat +
        (whistleblowerReward preset fork validator).toNat < 2 ^ 64 ∧
      after.balances.data = penalized.balances.data.set proposer.toNat
        (penalized.balances.data[proposer.toNat] + whistleblowerReward preset fork validator)
        inside ∧
      ∃ slashedInside : index.toNat < state.balances.data.size,
        penalized.balances.data = state.balances.data.set index.toNat
          (saturatingSub state.balances.data[index.toNat]
            (validator.effectiveBalance /
              (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT)) slashedInside := by
  unfold slashValidator at computed
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, read, readOk, _, _, marked, markedOk, _, _, _, _, _, _,
    penalized, penalizedOk, proposer, proposerOk, share, shareOk, raised, raisedOk, paid, paidOk,
    done⟩ := computed
  -- The reward reads the validator after its exit starts, which keeps its effective balance.
  obtain ⟨exiting, exitingOk, sameBalance⟩ := initiateValidatorExit_effectiveBalance found exitedOk
  have same : read = exiting := Except.ok.inj (readOk.symm.trans exitingOk)
  subst same
  have reward : read.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT =
      whistleblowerReward preset fork validator := by
    rw [whistleblowerReward, sameBalance]
  rw [reward] at shareOk paidOk
  have below := proposerShare_le shareOk
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp raisedOk
  obtain ⟨_, fitsPaid, rfl⟩ := increaseBalance_eq_ok_iff.mp paidOk
  have last := slashValidator_last done
  -- Before the penalty, the exit and the slashed flag keep the balances.
  have markedBalances : marked.balances = state.balances := by
    have exitedBalances := initiateValidatorExit_balances exitedOk
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    exact exitedBalances
  have penalty : read.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT =
      validator.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT := by
    rw [sameBalance]
  rw [penalty] at penalizedOk
  obtain ⟨slashedInside, penalizedEq⟩ := decreaseBalance_eq_ok_iff.mp penalizedOk
  refine ⟨penalized, proposer, share, inside, proposerOk, shareOk, below, last.1, ?_, ?_,
    ?_⟩
  · -- The two parts add up to the reward, since the proposer part is at most the reward.
    have partsNat := UInt64.le_iff_toNat_le.mp below
    simp only [BeaconState.putBalance, Option.getD_none, Array.getElem_set_self] at fitsPaid
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ below, Nat.mod_eq_of_lt fits] at fitsPaid
    omega
  · rw [last.2]
    simp only [BeaconState.putBalance, Option.getD_none, Array.getElem_set_self, Array.set_set]
    congr 1
    -- In arithmetic modulo `2^64` the two parts add up to the reward.
    rw [UInt64.add_assoc, UInt64.add_comm share, UInt64.sub_add_cancel]
  · refine ⟨by simpa [markedBalances] using slashedInside, ?_⟩
    rw [penalizedEq]
    simp only [BeaconState.putBalance, markedBalances]

/-! ## The balances after a slashing -/

/-- The first penalty of a slashed validator: its effective balance over the quotient of the fork.
-/
def initialSlashingPenalty (preset : Preset) (fork : Base.Fork) (validator : Validator) : Nat :=
  validator.effectiveBalance.toNat / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat

/-- The balances after a slashing, at every index.

The slashed validator pays `initialSlashingPenalty`, saturating at zero.

Then the proposer gets the whole reward, as both proposer and whistleblower.

The proposer is that of `penalized`, the state just before the reward.

No other balance changes. -/
theorem slashValidator_balances {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (found : getValidator state index = .ok validator)
    (computed : slashValidator config state index = .ok after) :
    ∃ (penalized : BeaconState preset fork) (proposer : ValidatorIndex),
      getBeaconProposerIndex penalized = .ok proposer ∧
      ∀ position, (after.balances.data[position]?).map UInt64.toNat =
        (state.balances.data[position]?).map fun balance =>
          balance.toNat -
              (if position = index.toNat then initialSlashingPenalty preset fork validator
                else 0) +
            (if position = proposer.toNat then (whistleblowerReward preset fork validator).toNat
              else 0) := by
  obtain ⟨penalized, proposer, _, inside, proposerOk, _, _, _, fits, paid, slashedInside,
    lowered⟩ := slashValidator_payout found computed
  refine ⟨penalized, proposer, proposerOk, fun position => ?_⟩
  have penaltyNat : (validator.effectiveBalance /
      (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT).toNat =
      initialSlashingPenalty preset fork validator := UInt64.toNat_div _ _
  -- The balances before the reward: the penalty at the index of the slashed validator.
  have before : ∀ other, penalized.balances.data[other]? =
      if index.toNat = other then
        some (saturatingSub state.balances.data[index.toNat]
          (validator.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT))
      else state.balances.data[other]? := by
    intro other
    rw [lowered, Array.getElem?_set]
  have slashedRead : state.balances.data[index.toNat]? = some state.balances.data[index.toNat] :=
    Array.getElem?_eq_getElem slashedInside
  -- The reward does not overflow, so it adds to the balance in natural numbers.
  have rewardNat : (penalized.balances.data[proposer.toNat] +
      whistleblowerReward preset fork validator).toNat =
      penalized.balances.data[proposer.toNat].toNat +
        (whistleblowerReward preset fork validator).toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have proposerRead := before proposer.toNat
  rw [Array.getElem?_eq_getElem inside] at proposerRead
  rw [paid, Array.getElem?_set]
  by_cases atProposer : proposer.toNat = position
  · subst atProposer
    simp only [↓reduceIte, Option.map_some, rewardNat]
    by_cases atSlashed : index.toNat = proposer.toNat
    · simp only [atSlashed, ↓reduceIte, Option.some.injEq] at proposerRead
      have read : state.balances.data[proposer.toNat]? =
          some state.balances.data[index.toNat] := atSlashed ▸ slashedRead
      rw [proposerRead, read]
      simp [toNat_saturatingSub, penaltyNat, atSlashed.symm]
    · simp only [atSlashed, ↓reduceIte] at proposerRead
      rw [← proposerRead]
      simp [Ne.symm atSlashed]
  · simp only [atProposer, ↓reduceIte]
    rw [before position]
    by_cases atSlashed : index.toNat = position
    · subst atSlashed
      simp [slashedRead, toNat_saturatingSub, penaltyNat, Ne.symm atProposer]
    · simp [atSlashed, Ne.symm atSlashed, Ne.symm atProposer]

end EthLib.Consensus
