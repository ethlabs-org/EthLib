module

public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset

/-!
# Proofs: parameters of the mainnet and minimal configurations

The largest effective balance before Electra is the activation balance.

[EIP-7251] raises the largest effective balance of a compounding validator above that balance.

A validator waits at least one epoch between its exit and its withdrawal.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/

@[expose] public section

namespace EthLib.Consensus

/-- Before Electra, the mainnet preset's largest effective balance is the activation balance. -/
private theorem Preset.maxEffectiveBalance_eq_minActivationBalance_mainnet :
    Preset.mainnet.MAX_EFFECTIVE_BALANCE = Preset.mainnet.MIN_ACTIVATION_BALANCE := by
  decide

/-- Before Electra, the minimal preset's largest effective balance is the activation balance. -/
private theorem Preset.maxEffectiveBalance_eq_minActivationBalance_minimal :
    Preset.minimal.MAX_EFFECTIVE_BALANCE = Preset.minimal.MIN_ACTIVATION_BALANCE := by
  decide

/-- From Electra, the mainnet preset's largest effective balance is at least the activation one. -/
private theorem Preset.minActivationBalance_le_maxEffectiveBalanceElectra_mainnet :
    Preset.mainnet.MIN_ACTIVATION_BALANCE ≤ Preset.mainnet.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide

/-- From Electra, the minimal preset's largest effective balance is at least the activation one. -/
private theorem Preset.minActivationBalance_le_maxEffectiveBalanceElectra_minimal :
    Preset.minimal.MIN_ACTIVATION_BALANCE ≤ Preset.minimal.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide

/-- The mainnet configuration makes a validator wait at least one epoch before it can withdraw. -/
private theorem Config.one_le_minValidatorWithdrawabilityDelay_mainnet :
    1 ≤ Config.mainnet.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  decide

/-- The minimal configuration makes a validator wait at least one epoch before it can withdraw. -/
private theorem Config.one_le_minValidatorWithdrawabilityDelay_minimal :
    1 ≤ Config.minimal.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  decide

end EthLib.Consensus
