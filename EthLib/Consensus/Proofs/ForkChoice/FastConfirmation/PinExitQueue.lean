module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound

/-!
# Gain rate and preset facts for the pin split

The gain rate of a key is at most the gain rate at the largest effective balance.

The preset facts that the pin's floors read hold for the mainnet and minimal presets.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-! ## Group C: exit counts, gain rate, new keys, preset facts (items 15, 16, new-key step, N6) -/

/-- C2 (item 16).
Every key's gain rate is at most the gain rate at the largest effective balance.
The effective balance of a key is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
theorem gain_le_capMax (perIncrement eb : ℕ)
    (capped : eb ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    eb / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
          WEIGHT_DENOMINATOR.toNat :=
  Nat.div_le_div_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right capped)))

/-- C4 (preset facts, mainnet).
The slashing quotients are large enough, the ejection balance exceeds an increment,
and the ejection balance less an increment fits below two thirds of the activation balance
less the slashing penalty, the downward band and an increment. -/
theorem preset_facts_mainnet :
    4 ≤ (parameters Preset.mainnet .fusaka).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
    2 ≤ (parameters Preset.mainnet .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat < Config.mainnet.EJECTION_BALANCE.toNat ∧
    Config.mainnet.EJECTION_BALANCE.toNat - Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * Preset.mainnet.MIN_ACTIVATION_BALANCE.toNat / 3 -
        Preset.mainnet.MIN_ACTIVATION_BALANCE.toNat /
          (parameters Preset.mainnet .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        Preset.mainnet.downwardBand - Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  decide

/-- C4 (preset facts, minimal preset).
The same four facts as for the mainnet preset. -/
theorem preset_facts_minimal :
    4 ≤ (parameters Preset.minimal .fusaka).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
    2 ≤ (parameters Preset.minimal .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat < Config.minimal.EJECTION_BALANCE.toNat ∧
    Config.minimal.EJECTION_BALANCE.toNat - Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * Preset.minimal.MIN_ACTIVATION_BALANCE.toNat / 3 -
        Preset.minimal.MIN_ACTIVATION_BALANCE.toNat /
          (parameters Preset.minimal .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        Preset.minimal.downwardBand - Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  decide

end EthLib.Consensus.Models.Network.PinSplit
