module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound

/-!
# The rate of a rewards pass at a state is at most the leak rate of the pin reserve

The rewards pass of an epoch debits a key by its flag penalties and its inactivity penalty.

Both are bounded at the state that ends the epoch, in terms of the total active balance there.

`pinReserve` reads the base reward per increment at the pulled-up state R instead.

The total at the state is at least two thirds of R's.
So the square root of the state's total is at least the square root of a quarter of R's total.

The rate at the state is then at most twice the key's increments times the base reward per increment at that quarter.
The inactivity term adds a bound on the score.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit2

open Base Uint64 Models

variable {preset : Preset} {config : Config}

/-- The rate at which one rewards pass can debit a key at a state is at most the leak rate the pin reserve reads.

The rate is taken at the key's effective balance at the state.

`pulledTotal` is R's total read, and `quarter` is `max inc (pulledTotal / 4)`.
The reserve reads the base reward per increment at the quarter.

The state's total is at least two thirds of R's, so its square root is at least the quarter's.

The score bound `scoreBound` covers the pass's score after its update, which is the score plus one bias.

Effective balances are whole increments.

`roomy` makes the rounding of the per-increment reward lose less than its fraction.

The flag term is `40 / 64` of a base reward per increment for each increment.
It fits in `2 * (increments * perIncrement)`, because the floor of a quotient that is at least one is at least half of it.

The left side is `passPenaltyRate config z v` of `PinDriftBound`, restated. -/
theorem passPenaltyRate_le_leak (z : ForkedBeaconState preset) (v : ℕ) (pulledTotal : ℕ)
    (scoreBound : ℕ)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (roomy : 2 ^ 33 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat)
    (pulledFits : pulledTotal < 2 ^ 64)
    (aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ effectiveAt z v)
    (band : 2 * pulledTotal ≤ 3 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (Finset.range z.state.validators.data.size).filter
          (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
        ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0))
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤ scoreBound) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let total := max inc
      (∑ i ∈ (Finset.range z.state.validators.data.size).filter
          (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
        ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
    let score := if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
    let quarter := max inc (pulledTotal / 4)
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / quarter.sqrt
    (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
        effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
      effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
    2 * (effectiveAt z v / inc * perIncrement) +
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  intro inc total score quarter perIncrement
  have weights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = 40 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  obtain ⟨k, hk⟩ := aligned
  have hinc : inc ≤ total := le_max_left _ _
  have hfactor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat := by
    rcases Nat.eq_zero_or_pos preset.BASE_REWARD_FACTOR.toNat with zero | pos
    · rw [zero, Nat.mul_zero] at roomy
      exact absurd roomy (by decide)
    · exact pos
  -- the numerator of the per-increment reward, `X`, dominates the square root of the quarter
  obtain ⟨X, hX⟩ : ∃ X, inc * preset.BASE_REWARD_FACTOR.toNat = X := ⟨_, rfl⟩
  rw [hX] at roomy
  have hp : perIncrement = X / quarter.sqrt := by
    simp only [perIncrement, hX]
  have incX : inc ≤ X := by
    rw [← hX]
    exact Nat.le_mul_of_pos_right _ hfactor
  have quarterLe : quarter ≤ X ^ 2 := by
    refine max_le ?_ ?_
    · exact Nat.le_trans incX (Nat.le_self_pow (by decide) _)
    · have : 2 ^ 66 ≤ X ^ 2 := by
        calc 2 ^ 66 = (2 ^ 33) ^ 2 := by norm_num
          _ ≤ X ^ 2 := Nat.pow_le_pow_left roomy 2
      have : pulledTotal / 4 < 2 ^ 62 := by omega
      omega
  have quarterRoot : quarter.sqrt ≤ X := by
    have := Nat.sqrt_le_sqrt quarterLe
    rwa [Nat.sqrt_eq'] at this
  have quarterTotal : quarter ≤ total := by
    refine max_le hinc ?_
    have : 2 * pulledTotal ≤ 3 * total := band
    omega
  have totalRoot : quarter.sqrt ≤ total.sqrt := Nat.sqrt_le_sqrt quarterTotal
  have quarterPositive : 0 < quarter.sqrt :=
    Nat.sqrt_pos.mpr (Nat.lt_of_lt_of_le positive (le_max_left _ _))
  have perOne : 1 ≤ X / quarter.sqrt := (Nat.le_div_iff_mul_le quarterPositive).mpr (by omega)
  have rewardRate : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v / (64 * total.sqrt) ≤
      2 * (effectiveAt z v / inc * perIncrement) := by
    have increments : effectiveAt z v / inc = k := by
      rw [hk, Nat.mul_div_cancel_left _ positive]
    have numerator : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v = 40 * (k * X) := by
      rw [hk, ← hX]
      ring
    have totalPositive : 0 < total.sqrt := Nat.lt_of_lt_of_le quarterPositive totalRoot
    rw [increments, numerator]
    calc 40 * (k * X) / (64 * total.sqrt)
        ≤ 40 * (k * X) / (40 * total.sqrt) :=
          Nat.div_le_div_left (Nat.mul_le_mul_right _ (by decide)) (by positivity)
      _ = k * X / total.sqrt := Nat.mul_div_mul_left _ _ (by decide)
      _ ≤ k * X / quarter.sqrt := Nat.div_le_div_left totalRoot quarterPositive
      _ ≤ 2 * (k * perIncrement) := by
        refine Nat.div_le_of_le_mul ?_
        have split : X < (X / quarter.sqrt + 1) * quarter.sqrt := by
          have := Nat.lt_mul_div_succ X quarterPositive
          rwa [Nat.mul_comm] at this
        have step : X ≤ 2 * perIncrement * quarter.sqrt := by
          have : (X / quarter.sqrt + 1) ≤ 2 * (X / quarter.sqrt) := by omega
          rw [hp]
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le split (Nat.mul_le_mul_right _ this))
        calc k * X ≤ k * (2 * perIncrement * quarter.sqrt) := Nat.mul_le_mul_left _ step
          _ = quarter.sqrt * (2 * (k * perIncrement)) := by ring
  have scoreRate : effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ scored)
  exact Nat.add_le_add rewardRate scoreRate

/-- `roomy` on mainnet and minimal. -/
theorem roomy_mainnet :
    2 ^ 33 ≤ Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat *
      Preset.mainnet.BASE_REWARD_FACTOR.toNat ∧
    2 ^ 33 ≤ Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat *
      Preset.minimal.BASE_REWARD_FACTOR.toNat := by
  decide

end EthLib.Consensus.Models.Network.PinSplit2
