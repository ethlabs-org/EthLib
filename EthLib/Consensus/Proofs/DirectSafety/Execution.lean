module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Transition.Genesis
public import Mathlib.Data.Finset.Basic

/-!
# Concrete executions for the direct safety statement

Blocks are the actual inputs of successful transitions, with result validation enabled.

No relation over all reachable paths stands in for the selected execution.

This fork-only statement draft deliberately leaves the proofs for review.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def Genesis (g : ForkedBeaconState preset) : Prop :=
  ∃ hash time deposits,
    initializeBeaconStateFromEth1 config checks hash time deposits = .ok g.state ∧
      isValidGenesisState config g.state = true

structure Parameters (preset : Preset) : Prop where
  slots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  roots : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
  increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  registry : preset.VALIDATOR_REGISTRY_LIMIT.toNat < 2 ^ 64

/-- The header of the actual block input, including its supplied and checked state root. -/
def blockHeader {fork : Fork} (block : BeaconBlock preset fork) : Option BeaconBlockHeader := do
  let bodyRoot ← (hashTreeRoot block.body).toOption
  pure ⟨block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, bodyRoot⟩

def _root_.EthLib.Consensus.Step.headers {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List BeaconBlockHeader :=
  match step with
  | .slot _ => []
  | .block _ signed _ _ => (blockHeader signed.message).toList

def _root_.EthLib.Consensus.Run.headers {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List BeaconBlockHeader :=
  match run with
  | .nil => []
  | .snoc pre step => pre.headers ++ step.headers

/-- Actual block headers up to a checkpoint boundary, without identifying equal hashes. -/
def _root_.EthLib.Consensus.Run.checkpointPath {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (checkpoint : Checkpoint) : List BeaconBlockHeader :=
  run.headers.filter fun h => h.slot.toNat ≤ checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat

def Conflict {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (f j : Checkpoint) : Prop :=
  ¬ (left.checkpointPath f).IsPrefix (right.checkpointPath j) ∧
    ¬ (right.checkpointPath j).IsPrefix (left.checkpointPath f)

end EthLib.Consensus.DirectSafety
