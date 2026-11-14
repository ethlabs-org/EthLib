module

public import EthLib.Consensus.Proofs.DirectSafety.Terminal
import all EthLib.Consensus.Proofs.DirectSafety.Fields

/-!
# Quorums from a terminal justification projection

The terminal input is reachable, so its participation evidence comes from the real run.

The projection supplies checked balance reads without requiring a future epoch transition.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem terminal_quorum_count {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (enough : ∀ high, view.enough high) (call : TerminalQuorum view) :
    2 * Models.stake (effectiveWeight a.state) (activeKeys a.state) ≤
      3 * Models.stake (effectiveWeight a.state) call.voters := by
  have floor := enough (getCurrentEpoch a.state).toNat
  rw [call.selected] at floor
  exact call.passes.stake_le (run.pubkeysDistinct genesis) (floor (by omega) call.later)

private theorem terminal_quorum_attestations {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (_early : a.fork < .hegota) (view : TerminalView a) (call : TerminalQuorum view) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target :=
  view_quorum_attestations run parameters genesis (.inr call)

private theorem terminal_quorum_recent {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (_early : a.fork < .hegota) (view : TerminalView a) (call : TerminalQuorum view) :
    call.voters ⊆ recentKeys a.state :=
  view_voters_recent run parameters genesis (.inr call)

theorem terminal_quorum_epochs {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (_parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (call : TerminalQuorum view) :
    call.source.epoch < call.target.epoch := by
  exact terminal_epochs run genesis call

end EthLib.Consensus.DirectSafety
