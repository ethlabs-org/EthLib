import EthLib.Consensus.Transition.EpochUpdates
open EthLib.Consensus
/-- A key at the split: effective balance 32 ETH, balance 31.755 ETH.
On R's branch its balance falls to 31.747 ETH; on C's it is 31.751 ETH.
At the next epoch update R lowers the effective balance to 31 ETH, and C keeps 32 ETH. -/
example : (match updatedEffectiveBalance Preset.mainnet 2048000000000 31747000000 32000000000 with
    | .ok e => some e.toNat | .error _ => none) = some 31000000000 := by rfl
example : (match updatedEffectiveBalance Preset.mainnet 2048000000000 31751000000 32000000000 with
    | .ok e => some e.toNat | .error _ => none) = some 32000000000 := by rfl
