module

public import EthLib.Consensus.Proofs.DirectSafety.Terminal
public import EthLib.Consensus.Proofs.Containers.Block

/-!
# Executable hash evidence including full blocks

The fast-confirmation inputs include full blocks as well as master's headers and states.

The searches inspect their actual SSZ node messages and successful roots.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A header or state from direct safety, or a full block supplied by a fast-confirmation run. -/
inductive FcrHashObject (preset : Preset) where
  | header (value : BeaconBlockHeader)
  | state (value : ForkedBeaconState preset)
  | block (fork : Fork) (value : BeaconBlock preset fork)

/-- Embed a direct-safety object without changing its root or node messages. -/
def HashObject.fcr : HashObject preset → FcrHashObject preset
  | .header h => .header h
  | .state s => .state s

/-- The successful SSZ root of an input, if hashing succeeds. -/
def FcrHashObject.root : FcrHashObject preset → Option Root
  | .header h => (hashTreeRoot h).toOption
  | .state s => (hashTreeRoot s.state).toOption
  | .block _ b => (hashTreeRoot b).toOption

/-- The SSZ node messages of a header or full block; states supply only their roots. -/
def FcrHashObject.messages : FcrHashObject preset → List Bytes
  | .header h => (HashObject.header (preset := preset) h).messages
  | .state _ => []
  | .block fork b =>
    ((valueTree (SszType.desc (BeaconBlock preset fork)) (SszType.toValue b)).toOption.map
      (fun tree => tree.messages)).getD []

/-- A step's states and headers, and the full block when the step applies one. -/
def _root_.EthLib.Consensus.Step.fcrHashObjects {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List (FcrHashObject preset) :=
  step.hashObjects.map HashObject.fcr ++ match step with
    | .slot _ => []
    | .block _ signed _ _ => [.block _ signed.message]

/-- The first state and header, followed by each step's hash inputs. -/
def _root_.EthLib.Consensus.Run.fcrHashObjects {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List (FcrHashObject preset) :=
  match run with
  | .nil => [.state first, .header first.state.latestBlockHeader]
  | .snoc pre step => pre.fcrHashObjects ++ step.fcrHashObjects

/-- A terminal view contributes the same headers and states as direct safety. -/
def TerminalView.fcrHashObjects {a : ForkedBeaconState preset}
    (view : TerminalView a) : List (FcrHashObject preset) :=
  view.hashObjects.map HashObject.fcr

/-- Search the given inputs for colliding node messages or a successful zero root. -/
def FcrHashEvidence (objects : List (FcrHashObject preset)) : Prop :=
  (∃ x y, findMessageCollision (objects.flatMap FcrHashObject.messages)
      (objects.flatMap FcrHashObject.messages) = some (x, y)) ∨
    ∃ object, (objects.find? fun object =>
      decide (object.root = some (Vector.replicate 32 0))) = some object

/-- The executable searches find exactly a collision or zero root among the supplied inputs. -/
theorem fcrHashEvidence_iff {objects : List (FcrHashObject preset)} :
    FcrHashEvidence objects ↔
      (∃ x ∈ objects.flatMap FcrHashObject.messages,
        ∃ y ∈ objects.flatMap FcrHashObject.messages, MessageCollision x y) ∨
      ∃ object ∈ objects, object.root = some (Vector.replicate 32 0) := by
  constructor
  · rintro (⟨x, y, found⟩ | ⟨object, found⟩)
    · obtain ⟨xm, ym, collision⟩ := findMessageCollision_valid found
      exact .inl ⟨x, xm, y, ym, collision⟩
    · exact .inr ⟨object, List.mem_of_find?_eq_some found, by
        simpa using List.find?_some found⟩
  · rintro (⟨x, xm, y, ym, collision⟩ | ⟨object, member, zero⟩)
    · exact .inl (findMessageCollision_of_collision xm ym collision)
    · right
      apply Option.isSome_iff_exists.mp
      apply Option.isSome_iff_ne_none.mpr
      intro none
      have missing := List.find?_eq_none.mp none object member
      simp [zero] at missing

/-- Enlarging the supplied inputs preserves executable collision or zero-root evidence. -/
theorem FcrHashEvidence.mono {one two : List (FcrHashObject preset)}
    (subset : one ⊆ two) (evidence : FcrHashEvidence one) : FcrHashEvidence two := by
  rw [fcrHashEvidence_iff] at evidence ⊢
  rcases evidence with ⟨x, xm, y, ym, collision⟩ | ⟨object, member, zero⟩
  · have mem {z} (member : z ∈ one.flatMap FcrHashObject.messages) :
        z ∈ two.flatMap FcrHashObject.messages := by
      obtain ⟨object, member, hashed⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨object, subset member, hashed⟩
    exact .inl ⟨x, mem xm, y, mem ym, collision⟩
  · exact .inr ⟨object, subset member, zero⟩

private theorem Run.hashObjects_fcr_subset {g a : ForkedBeaconState preset}
    (run : Run config checks g a) : run.hashObjects.map HashObject.fcr ⊆ run.fcrHashObjects := by
  induction run with
  | nil => exact List.Subset.refl _
  | snoc pre step ih =>
    simp only [Run.hashObjects, List.map_append, Run.fcrHashObjects]
    intro object member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (ih member)
    · exact List.mem_append_right _ (List.mem_append_left _ member)

/-- Direct-safety evidence is still found when full-block inputs are supplied as well. -/
theorem HashEvidence.fcr {objects : List (HashObject preset)}
    {extended : List (FcrHashObject preset)}
    (subset : objects.map HashObject.fcr ⊆ extended) (evidence : HashEvidence objects) :
    FcrHashEvidence extended := by
  rw [hashEvidence_iff] at evidence
  rw [fcrHashEvidence_iff]
  have messages {message : Bytes} (member : message ∈ objects.flatMap HashObject.messages) :
      message ∈ extended.flatMap FcrHashObject.messages := by
    obtain ⟨object, member, inside⟩ := List.mem_flatMap.mp member
    refine List.mem_flatMap.mpr ⟨object.fcr,
      subset (List.mem_map.mpr ⟨object, member, rfl⟩), ?_⟩
    cases object <;> exact inside
  rcases evidence with ⟨x, xm, y, ym, collision⟩ | ⟨object, member, zero⟩
  · exact .inl ⟨x, messages xm, y, messages ym, collision⟩
  · refine .inr ⟨object.fcr, subset (List.mem_map.mpr ⟨object, member, rfl⟩), ?_⟩
    cases object <;> exact zero

/-- Evidence from two terminal runs remains executable on the full-block inputs. -/
theorem terminal_hashEvidence_fcr {g a b : ForkedBeaconState preset}
    {left : Run config checks g a} {right : Run config checks g b}
    {va : TerminalView a} {vb : TerminalView b}
    (evidence : HashEvidence (left.hashObjects ++ right.hashObjects ++
      va.hashObjects ++ vb.hashObjects)) :
    FcrHashEvidence (left.fcrHashObjects ++ right.fcrHashObjects ++
      va.fcrHashObjects ++ vb.fcrHashObjects) := by
  apply evidence.fcr
  simp only [List.map_append, TerminalView.fcrHashObjects]
  intro object member
  simp only [List.mem_append] at member ⊢
  rcases member with ((member | member) | member) | member
  · exact .inl (.inl (.inl (Run.hashObjects_fcr_subset left member)))
  · exact .inl (.inl (.inr (Run.hashObjects_fcr_subset right member)))
  · exact .inl (.inr member)
  · exact .inr member

/-- Equal roots of full blocks before Gloas give equality or executable collision evidence. -/
theorem fcr_block_binding {fork : Fork}
    [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
    [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (early : fork < .glamsterdam)
    (objects : List (FcrHashObject preset)) (a b : BeaconBlock preset fork)
    (one : .block fork a ∈ objects) (two : .block fork b ∈ objects) (root : Root)
    (sameA : hashTreeRoot a = .ok root) (sameB : hashTreeRoot b = .ok root) :
    a = b ∨ FcrHashEvidence objects := by
  rcases SszType.hashTreeRoot_binding (a.commitmentSized early) (b.commitmentSized early)
      sameA sameB with same | collision
  · exact .inl same
  · obtain ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, leftMem, rightMem, collided⟩ := collision
    right
    rw [fcrHashEvidence_iff]
    left
    refine ⟨x, List.mem_flatMap.mpr ⟨.block fork a, one, ?_⟩,
      y, List.mem_flatMap.mpr ⟨.block fork b, two, ?_⟩, collided⟩
    · simpa [FcrHashObject.messages, leftOk, Except.toOption] using leftMem
    · simpa [FcrHashObject.messages, rightOk, Except.toOption] using rightMem

end EthLib.Consensus.DirectSafety
