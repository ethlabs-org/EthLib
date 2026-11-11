module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# Hash evidence restricted to the supplied executions

Collision evidence uses only the selected block headers, not full beacon-state commitments.

States are included only for the zero-root alternative.

A zero state root leaves processSlot's empty-root sentinel unset.

A later slot can then refill it.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

inductive HashObject (preset : Preset) where
  | header (value : BeaconBlockHeader)
  | state (value : ForkedBeaconState preset)

def HashObject.root (object : HashObject preset) : Option Root :=
  match object with
  | .header h => (hashTreeRoot h).toOption
  | .state s => (hashTreeRoot s.state).toOption

def HashObject.messages (object : HashObject preset) : List Bytes :=
  match object with
  | .header h => ((valueTree (SszType.desc BeaconBlockHeader) (SszType.toValue h)).toOption.map
      (fun tree => tree.messages)).getD []
  | .state _ => []

def _root_.EthLib.Consensus.Step.hashObjects {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List (HashObject preset) :=
  [.state before, .state after, .header before.state.latestBlockHeader,
    .header after.state.latestBlockHeader] ++
  (match step with
  | .slot _ => match (processSlot before.state).toOption with
    | none => []
    | some cached => [.state ⟨before.fork, cached⟩, .header cached.latestBlockHeader]
  | .block _ signed _ _ => ((blockHeader signed.message).toList.map HashObject.header))

def _root_.EthLib.Consensus.Run.hashObjects {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List (HashObject preset) :=
  match run with
  | .nil => [.state first, .header first.state.latestBlockHeader]
  | .snoc pre step => pre.hashObjects ++ step.hashObjects

def HashEvidence (objects : List (HashObject preset)) : Prop :=
  (∃ x ∈ objects.flatMap HashObject.messages, ∃ y ∈ objects.flatMap HashObject.messages,
    MessageCollision x y) ∨
  ∃ object ∈ objects, object.root = some (Vector.replicate 32 0)

theorem header_binding (objects : List (HashObject preset)) (a b : BeaconBlockHeader)
    (one : .header a ∈ objects) (two : .header b ∈ objects) (root : Root)
    (sameA : hashTreeRoot a = .ok root) (sameB : hashTreeRoot b = .ok root) :
    a = b ∨ HashEvidence objects := by
  sorry

/-- Equal checkpoint roots identify equal header prefixes, or the scan finds hash evidence. -/
theorem checkpoint_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (epoch : Epoch) (root : Root)
    (one : getBlockRoot a.state epoch = .ok root)
    (two : getBlockRoot b.state epoch = .ok root) :
    left.checkpointPath epoch = right.checkpointPath epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  sorry

end EthLib.Consensus.DirectSafety
