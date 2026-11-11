module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# Hash evidence restricted to the supplied executions

The scan covers block headers and endpoint and cached states, not all reachable states.

It returns SHA-256 input collisions or an observed state or header whose root is zero.
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
  | .state s => ((valueTree (SszType.desc (BeaconState preset s.fork))
      (SszType.toValue s.state)).toOption.map (fun tree => tree.messages)).getD []

def Step.hashObjects {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List (HashObject preset) :=
  [.state before, .state after, .header before.state.latestBlockHeader,
    .header after.state.latestBlockHeader] ++
  (match step with
  | .slot _ => match (processSlot before.state).toOption with
    | none => []
    | some cached => [.state ⟨before.fork, cached⟩, .header cached.latestBlockHeader]
  | .block _ signed _ _ => ((blockHeader signed.message).toList.map HashObject.header))

def Run.hashObjects {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List (HashObject preset) :=
  match run with
  | .nil => [.state first, .header first.state.latestBlockHeader]
  | .snoc pre step => pre.hashObjects ++ step.hashObjects

def HashEvidence (objects : List (HashObject preset)) : Prop :=
  (∃ x y, findMessageCollision (objects.flatMap HashObject.messages)
    (objects.flatMap HashObject.messages) = some (x, y) ∧ MessageCollision x y) ∨
  ∃ object ∈ objects, object.root = some (Vector.replicate 32 0)

theorem header_binding (objects : List (HashObject preset)) (a b : BeaconBlockHeader)
    (one : .header a ∈ objects) (two : .header b ∈ objects) (root : Root)
    (sameA : hashTreeRoot a = .ok root) (sameB : hashTreeRoot b = .ok root) :
    a = b ∨ HashEvidence objects := by
  sorry

theorem state_binding (objects : List (HashObject preset)) {fork : Fork}
    (a b : BeaconState preset fork) (one : .state ⟨fork, a⟩ ∈ objects)
    (two : .state ⟨fork, b⟩ ∈ objects) (root : Root)
    (sizeA : CommitmentSized (SszType.desc (BeaconState preset fork)) (SszType.toValue a))
    (sizeB : CommitmentSized (SszType.desc (BeaconState preset fork)) (SszType.toValue b))
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
    left.checkpointPath ⟨epoch, root⟩ = right.checkpointPath ⟨epoch, root⟩ ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  sorry

end EthLib.Consensus.DirectSafety
