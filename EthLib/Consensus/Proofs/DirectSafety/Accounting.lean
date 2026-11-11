module

public import EthLib.Consensus.Proofs.DirectSafety.Fields

/-!
# Transporting actual quorum counts to a common state's stake

The bound is explicit about changed membership and changed effective balances.

Closing these terms with churn or reward rates is a separate task, not a premise about finality.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable def allowance {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (reference : ForkedBeaconState preset) (call : QuorumCall run) : Nat :=
  Quorum.change (activeKeys reference.state) (activeKeys call.cached) call.voters
    (effectiveWeight reference.state) (effectiveWeight call.cached)

/-- Bounds only tests in the epoch interval used by the double-vote or surround argument. -/
def AccountingBound {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (reference : ForkedBeaconState preset) (low high budget : Nat) : Prop :=
  ∀ call : QuorumCall run, low ≤ call.target.epoch.toNat → call.target.epoch.toNat ≤ high →
    allowance reference call ≤ budget

theorem quorum_at_reference {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) (enough : EnoughStake run)
    (reference : ForkedBeaconState preset) (call : QuorumCall run) :
    2 * Quorum.weight (effectiveWeight reference.state) (activeKeys reference.state) ≤
      3 * Quorum.weight (effectiveWeight reference.state)
        (activeKeys reference.state ∩ call.voters) + allowance reference call := by
  sorry

theorem allowance_of_flows {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (reference : ForkedBeaconState preset) (call : QuorumCall run)
    (leaving lost entering gained : Nat)
    (leave : Quorum.weight (effectiveWeight reference.state)
      (activeKeys reference.state \ activeKeys call.cached) ≤ leaving)
    (loss : (∑ key ∈ activeKeys reference.state ∩ activeKeys call.cached,
      (effectiveWeight reference.state key - effectiveWeight call.cached key)) ≤ lost)
    (enter : Quorum.weight (effectiveWeight call.cached)
      (call.voters \ activeKeys reference.state) ≤ entering)
    (gain : (∑ key ∈ activeKeys reference.state ∩ call.voters,
      (effectiveWeight call.cached key - effectiveWeight reference.state key)) ≤ gained) :
    allowance reference call ≤ 2 * (leaving + lost) + 3 * (entering + gained) := by
  sorry

end EthLib.Consensus.DirectSafety
