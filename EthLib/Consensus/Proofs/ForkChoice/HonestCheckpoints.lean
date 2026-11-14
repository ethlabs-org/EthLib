module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.Transition.FfgJustification
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# State-transition provenance in honest stores

A non-anchor block's cached state comes from a transition with the execution's checks and sources.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- Each non-anchor block in an honest store has a transition with the execution's checks. -/
theorem Execution.exists_transition_of_nonanchor_block {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : ((e.world k).state w).blocks[root]? = some block)
    (stored : ((e.world k).state w).blockStates[root]? = some state)
    (other : block ≠ anchorBlock) :
    ∃ parent signed, signed.message = block ∧
      ((e.world k).state w).blockStates[block.parentRoot]? = some parent ∧
      stateTransition config checks sources.engine parent signed true = .ok state := by
  rcases e.exists_signed_of_blocks honest found with old |
    ⟨signed, parent, post, -, message, -, parentFound, transitioned, postFound⟩
  · obtain ⟨anchorRoot, -, blocks, -⟩ := getForkchoiceStore_maps anchored
    rw [start, blocks, getElem?_insert_root] at old
    split at old
    · exact (other (Option.some.inj old.1).symm).elim
    · simp at old
  · rw [stored, Option.some.injEq] at postFound
    subst post
    exact ⟨parent, signed, message, parentFound, transitioned⟩

end Models.Network

end EthLib.Consensus
