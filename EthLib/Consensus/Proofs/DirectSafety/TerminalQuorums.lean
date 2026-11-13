module

public import EthLib.Consensus.Proofs.DirectSafety.Terminal

/-!
# Quorums from a terminal justification projection

The terminal input is reachable, so its participation evidence comes from the real run.

The projection supplies checked balance reads without requiring a future epoch transition.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

theorem terminal_quorum_count {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (enough : view.enough) (call : TerminalQuorum view) :
    2 * Models.stake (effectiveWeight a.state) (activeKeys a.state) ≤
      3 * Models.stake (effectiveWeight a.state) call.voters := by
  rw [call.selected] at enough
  exact call.passes.stake_le (run.unique (genesis_unique genesis)) (enough call.later)

theorem terminal_quorum_attestations {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .hegota) (view : TerminalView a) (call : TerminalQuorum view) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target :=
  counted_accepted run (run_participation run parameters genesis early) call.later call.current
    call.target call.targetEpoch call.targetRoot call.counted
    fun index data validator found voted =>
      selected_vote_key run (genesis_unique genesis) index data validator found voted

theorem terminal_quorum_recent {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .hegota) (view : TerminalView a) (call : TerminalQuorum view) :
    call.voters ⊆ recentKeys a.state :=
  counted_recent (run_participation run parameters genesis early).1 call.later call.current
    call.target call.targetEpoch call.counted

theorem terminal_quorum_epochs {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (call : TerminalQuorum view) :
    call.source.epoch < call.target.epoch := by
  have _ := parameters
  obtain ⟨holds, _, separated⟩ := run_justified_separated run genesis
  exact link_source_lt holds.settled separated call.later call.current call.target
    call.targetEpoch

end EthLib.Consensus.DirectSafety
