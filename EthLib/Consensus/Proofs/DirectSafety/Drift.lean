module

public import EthLib.Consensus.Proofs.DirectSafety.Core

/-!
# Drift computed from the concrete transitions

Charge active departures and balance losses separately from recent arrivals and balance gains.

Recent means active in either of the two epochs whose attestations justification may count.

Interval bounds must include initial previous-epoch voters, even for a zero-length tail.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable def leaving (x y : ForkedBeaconState preset) : Nat :=
  Quorum.weight (effectiveWeight x.state) (activeKeys x.state \ activeKeys y.state)

noncomputable def losing (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ activeKeys x.state ∩ activeKeys y.state,
    (effectiveWeight x.state k - effectiveWeight y.state k)

noncomputable def gaining (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ recentKeys x.state ∩ recentKeys y.state,
    (effectiveWeight y.state k - effectiveWeight x.state k)

/-- The epoch test is in the tail, not in the inherited prefix, under this slot bound. -/
theorem call_after_reference {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (low : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail)) (later : low ≤ call.target.epoch.toNat) :
    tail.Contains (.slot call.advanced) := by
  sorry

end EthLib.Consensus.DirectSafety
