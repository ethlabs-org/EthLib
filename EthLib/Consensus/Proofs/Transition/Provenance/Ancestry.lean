module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Transition.Provenance.Roots
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# Proofs: parent roots, and the hash evidence that replaces collision-freedom

A block names its parent by the root of the latest header of the state it runs on.

Along one chain that header is the header of the previous block, or of the start.

Its state root was filled at the first slot after that block, with the root of the state then.

So the parent root of a block is the root of the previous block's header, with that state root.

This needs no assumption on SHA-256: it follows the computations of one chain.

One case needs care: the state after a block may have the zero root.

Then the header stays unfilled, and a later slot fills it with another state's root.

The statement keeps that case as an alternative, with the state that has the zero root.

Comparing roots across two chains does need an assumption, or evidence.

Two equal header roots give equal headers, or two different 64-byte inputs of SHA-256 with one
digest.

`HashCollisionFound` records such a pair, found by an executable search over the hash inputs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Hash evidence -/

/-- The inputs of the SHA-256 calls that compute the SSZ root of a value. -/
def sszMessages {α : Type} [SszType α] (value : α) : List Bytes :=
  (valueTree (desc α) (toValue value)).toOption.toList.flatMap (·.messages)

/-- The search over a pool of SHA-256 inputs finds two different 64-byte inputs with one digest.

Such a pair is a collision of SHA-256's compression of two nodes. -/
def HashCollisionFound (pool : List Bytes) : Prop :=
  ∃ first second, findMessageCollision pool pool = some (first, second) ∧
    MessageCollision first second

/-- A collision found in a pool is found in any larger pool. -/
theorem HashCollisionFound.mono {pool larger : List Bytes} (subset : ∀ x ∈ pool, x ∈ larger)
    (found : HashCollisionFound pool) : HashCollisionFound larger := by
  obtain ⟨first, second, searched, collision⟩ := found
  obtain ⟨firstMember, secondMember, -⟩ := findMessageCollision_valid searched
  obtain ⟨a, b, again⟩ :=
    findMessageCollision_of_collision (subset _ firstMember) (subset _ secondMember) collision
  exact ⟨a, b, again, (findMessageCollision_valid again).2.2⟩

/-- A beacon block header has no variable-size count in its SSZ commitment. -/
theorem beaconBlockHeader_commitmentSized (header : BeaconBlockHeader) :
    CommitmentSized (desc BeaconBlockHeader) (toValue header) := by
  apply CommitmentSized.container
  intro pair member
  simp only [desc, toValue, SszFields.descs, SszFields.toValues,
    List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .uint _ _
  · exact .uint _ _
  · exact .byteVector _ _
  · exact .byteVector _ _
  · exact .byteVector _ _

/-- Two headers with one root are equal, or the search over their hash inputs finds a
collision. -/
theorem beaconBlockHeader_root_binding {left right : BeaconBlockHeader} {root : Root}
    (leftRoot : hashTreeRoot left = .ok root) (rightRoot : hashTreeRoot right = .ok root) :
    left = right ∨ HashCollisionFound (sszMessages left ++ sszMessages right) := by
  rcases hashTreeRoot_binding (beaconBlockHeader_commitmentSized left)
      (beaconBlockHeader_commitmentSized right) leftRoot rightRoot with same |
    ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, xMember, yMember, collision⟩
  · exact .inl same
  · refine .inr ?_
    have xIn : x ∈ sszMessages left ++ sszMessages right := by
      apply List.mem_append_left
      simp only [sszMessages, leftOk, Except.toOption, Option.toList_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact xMember
    have yIn : y ∈ sszMessages left ++ sszMessages right := by
      apply List.mem_append_right
      simp only [sszMessages, rightOk, Except.toOption, Option.toList_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact yMember
    obtain ⟨a, b, found⟩ := findMessageCollision_of_collision xIn yIn collision
    exact ⟨a, b, found, (findMessageCollision_valid found).2.2⟩

/-! ## Parent roots along a chain -/

/-- The parent root of a block of a chain.

The block runs on `state`, which a chain from `start` reaches with no upgrade due.

Either no block step came before it in the chain.
Then its parent root is the root of the start's header, with its state root settled.

Or the last block step before it ran on `state'` and left `post'`.
Then its parent root is the root of that block's header, with the root of `post'` as state root.
Or `post'` has the zero root. -/
theorem Reaches.parentRoot {start : ForkedBeaconState preset} {fork : Fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {state post : BeaconState preset fork}
    (chain : Reaches config checks start ⟨fork, state⟩)
    (applied : applySignedBlock config checks engine state signed validateResult = .ok post) :
    (HeaderSettled config checks start ⟨fork, state⟩ start.state.latestBlockHeader ∧
        hashTreeRoot state.latestBlockHeader = .ok signed.message.parentRoot) ∨
      ∃ (fork' : Fork) (engine' : ExecutionEngine preset fork')
        (signed' : SignedBeaconBlock preset fork') (validateResult' : Bool)
        (state' post' : BeaconState preset fork') (bodyRoot : Root),
        Reaches config checks start ⟨fork', state'⟩ ∧ upgradeDue config ⟨fork', state'⟩ = false ∧
        applySignedBlock config checks engine' state' signed' validateResult' = .ok post' ∧
        hashTreeRoot signed'.message.body = .ok bodyRoot ∧
        Reaches config checks ⟨fork', post'⟩ ⟨fork, state⟩ ∧
        ((∃ stateRoot, hashTreeRoot post' = .ok stateRoot ∧
            hashTreeRoot { signed'.message.header bodyRoot with stateRoot } =
              .ok signed.message.parentRoot ∧
            (validateResult' = true → stateRoot = signed'.message.stateRoot)) ∨
          hashTreeRoot post' = .ok (Vector.replicate 32 0)) := by
  obtain ⟨blockSlot, newer, parent, -⟩ := applySignedBlock_roots applied
  rcases chain.latestBlockHeader with settled | ⟨fork', engine', signed', validateResult',
    state', post', bodyRoot, head, notDue', applied', bodyRootOk, settled⟩
  · exact .inl ⟨settled, parent⟩
  · refine .inr ⟨fork', engine', signed', validateResult', state', post', bodyRoot, head, notDue',
      applied', bodyRootOk, settled.1, ?_⟩
    rcases settled.of_block notDue' applied' with ⟨header, sameSlot⟩ | ⟨root, rootOk, header,
      validated⟩ | zero
    · -- A block at the slot of the previous one is not newer than it.
      exfalso
      obtain ⟨headerSlot, -, -, -, postSlot, -⟩ := applySignedBlock_roots applied'
      simp only at header sameSlot
      have : state.latestBlockHeader.slot = state.slot := by
        rw [header, sameSlot, postSlot]
        exact headerSlot
      rw [this, blockSlot] at newer
      exact UInt64.lt_irrefl _ newer
    · simp only at header
      rw [header] at parent
      exact .inl ⟨root, rootOk, parent, validated⟩
    · exact .inr zero

end EthLib.Consensus
