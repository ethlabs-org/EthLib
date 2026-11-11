module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.DirectSafety.Safety

/-!
# Selected runs for stored block states

Before the next fork activation, each held block state has a validated run from the anchor.

Consumers can prepend their supplied genesis run without assuming a future transition succeeds.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Stored states retain the execution's checks and actual successful block inputs. -/
theorem Execution.exists_run_of_blockState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {root : Root} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state) :
    Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) := by
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  obtain ⟨block, found⟩ := (reachable k).known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, initial, -⟩ := (reachable k).blockStatesFromParents found
    have equal : post = state := Option.some.inj (postOk.symm.trans stored)
    rw [← equal, initial same]
    exact ⟨.nil⟩
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored same
    obtain ⟨pre⟩ := exists_run_of_blockState anchored honest start before parentFound
    have across : stateTransitionAcross config checks sources.engine ⟨fork, parent⟩ signed true =
        .ok state := by
      rw [stateTransitionAcross_of_before (by simpa only [message] using before root block found)]
      exact transitioned
    obtain ⟨advanced, slots, due, applied, -, -, -⟩ :=
      Run.stateTransition sources.engine signed across
    exact ⟨pre.append (slots.snoc (.block sources.engine signed due applied))⟩
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

end EthLib.Consensus.Models.Network
