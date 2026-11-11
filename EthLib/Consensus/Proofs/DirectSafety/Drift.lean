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
  ∑ k ∈ activeKeys x.state ∩ recentKeys y.state,
    (effectiveWeight y.state k - effectiveWeight x.state k)

/-- Exact reference loss outside keys already slashed at this state. -/
noncomputable def referenceLoss (x y : ForkedBeaconState preset) : Nat := by
  classical
  let unslashed := (activeKeys x.state).filter fun k =>
    ¬ ∃ v ∈ y.state.validators.data.toList, v.pubkey = k ∧ v.slashed = true
  exact ∑ k ∈ unslashed,
    (effectiveWeight x.state k - Quorum.supported (recentKeys y.state)
      (effectiveWeight y.state) k)

/-- Exact gains on the voting support, without charging reference stake that just exited. -/
noncomputable def referenceGain (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ recentKeys y.state,
    (effectiveWeight y.state k - Quorum.supported (activeKeys x.state)
      (effectiveWeight x.state) k)

/-- Previous-epoch stake outside the current quorum denominator, at one boundary only. -/
noncomputable def boundaryStake (y : ForkedBeaconState preset) : Nat :=
  Quorum.weight (effectiveWeight y.state) (recentKeys y.state \ activeKeys y.state)

/-- The combined transfer assigns coefficients two, one and two to loss, gain and boundary stake.

For current-active voters with fixed balances this gives the churn constants of [EIP-8061].

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period
-/
noncomputable def stateDrift (x y : ForkedBeaconState preset) : Nat :=
  2 * referenceLoss x y + referenceGain x y + 2 * boundaryStake y

/-- Maximum observed state budget, including the initial state and excluding later epochs. -/
noncomputable def derivedDrift {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y → Nat
  | _, .nil => stateDrift x x
  | y, .snoc pre _ =>
    if (getCurrentEpoch y.state).toNat ≤ high + 1 then
      max (derivedDrift high pre) (stateDrift x y)
    else derivedDrift high pre

/-- The boundary correction is a maximum single-epoch cohort, not cumulative exits. -/
noncomputable def boundaryWindow {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y → Nat
  | _, .nil => boundaryStake x
  | y, .snoc pre _ =>
    if (getCurrentEpoch y.state).toNat ≤ high + 1 then
      max (boundaryWindow high pre) (boundaryStake y)
    else boundaryWindow high pre

/-- The epoch test is in the tail, not in the inherited prefix, under this slot bound. -/
theorem call_after_reference {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (low : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail)) (later : low ≤ call.target.epoch.toNat) :
    tail.Contains (.slot call.advanced) := by
  sorry

end EthLib.Consensus.DirectSafety
