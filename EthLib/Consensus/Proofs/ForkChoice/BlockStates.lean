module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable
import EthLib.Consensus.Proofs.Containers.Block

/-!
# Proofs: each block state of a store comes from the state of its parent

A reachable store keeps a state for each known block.

A known anchor block has the anchor state.

Each other block has the state that its transition gives from the state of its parent.

So along a chain of known blocks above the anchor, each state is the transition of the one before.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

/-- Each known block of a store has a state, the state after that block.

A known anchor block has the anchor state.

That case reads the block, not its root; a reachable store keeps each block at its own root.

Any other block is the message of a signed block whose transition gives that state.

The transition starts from the state of the parent, which the store keeps.

It ran with some signature checks and some execution engine, which may differ between blocks.

It checks the state root, and the signature of the proposer under those checks.

Some checks accept every signature, so this says nothing on signatures. -/
def BlockStatesFromParents (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) (store : Store preset fork) : Prop :=
  ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄, store.blocks[root]? = some block →
    ∃ state, store.blockStates[root]? = some state ∧
      (block = anchorBlock → state = anchorState) ∧
      (block ≠ anchorBlock → ∃ parentState checks engine, ∃ signed : SignedBeaconBlock preset fork,
        signed.message = block ∧ store.blockStates[block.parentRoot]? = some parentState ∧
        stateTransition config checks engine parentState signed true = .ok state)

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- A reachable store knows the anchor block, at its own root. -/
private theorem Store.Reachable.anchor_known
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      store.blocks[root]? = some anchorBlock := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, hashed, blocks, -⟩ := getForkchoiceStore_maps made
    exact ⟨anchorRoot, hashed, by rw [blocks, getElem?_insert_root]; simp⟩
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, -⟩ := Store.onTick_frame ticked
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | @block _ _ _ _ _ _ added ih =>
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, onBlock_blocks_of_found added f⟩
  | attestation _ attested ih =>
    obtain ⟨-, blocks, -⟩ := Store.onAttestation_frame attested
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, -⟩ := Store.onAttesterSlashing_frame slashed
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, -⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := Store.onExecutionPayloadEnvelope_frame accepted
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | inclusionList _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := Store.onInclusionList_frame accepted
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩

/-- In a reachable store, each known block has the state after it, from the state of its parent.

A known anchor block has the anchor state instead. -/
theorem Store.Reachable.blockStatesFromParents
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.BlockStatesFromParents config anchorState anchorBlock := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, -, blocks, states⟩ := getForkchoiceStore_maps made
    intro root block found
    rw [blocks, getElem?_insert_root] at found
    rw [states, getElem?_insert_root]
    by_cases same : anchorRoot = root
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      simp only [same, ↓reduceIte]
      subst found
      exact ⟨_, rfl, fun _ => rfl, fun ne => absurd rfl ne⟩
    · simp [same] at found
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, states⟩ := Store.onTick_frame ticked
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | @block prior _ _ _ signed previous added ih =>
    rcases Store.onBlock_same_or_insert added with
      same | ⟨blockRoot, hashed, fresh, blocks, pre, state, preFound, ok, states⟩
    · subst same
      exact ih
    have parentNe : ∀ {parentState : BeaconState preset fork} {parentRoot : Root},
        prior.blockStates[parentRoot]? = some parentState → blockRoot ≠ parentRoot := by
      rintro _ _ hasState rfl
      have none := previous.blockState_eq_none fresh
      rw [none] at hasState
      cases hasState
    intro root block found
    rw [blocks, getElem?_insert_root] at found
    rw [states, getElem?_insert_root]
    by_cases same : blockRoot = root
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      subst found
      simp only [same, ↓reduceIte]
      have notAnchor : signed.message ≠ anchorBlock := by
        intro eq
        obtain ⟨r, h, f⟩ := previous.anchor_known
        rw [← eq, hashed] at h
        cases h
        rw [fresh] at f
        cases f
      refine ⟨state, rfl, fun eq => absurd eq notAnchor, fun _ => ⟨pre, _, _, _, rfl, ?_, ok⟩⟩
      rw [getElem?_insert_root]
      simp only [← same, parentNe preFound, ↓reduceIte]
      exact preFound
    · simp only [same, ↓reduceIte] at found ⊢
      obtain ⟨old, oldFound, rest⟩ := ih found
      refine ⟨old, oldFound, rest.1, fun ne => ?_⟩
      obtain ⟨p, c, e, s, hs, hp, ht⟩ := rest.2 ne
      refine ⟨p, c, e, s, hs, ?_, ht⟩
      rw [getElem?_insert_root]
      simp only [parentNe hp, ↓reduceIte]
      exact hp
  | attestation _ attested ih =>
    obtain ⟨-, blocks, states⟩ := Store.onAttestation_frame attested
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, states⟩ := Store.onAttesterSlashing_frame slashed
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onExecutionPayloadEnvelope_frame accepted
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | inclusionList _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onInclusionList_frame accepted
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found

/-- The root of the anchor state is the state root declared by its block. -/
theorem Store.Reachable.anchorState_root
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    SszType.hashTreeRoot anchorState = .ok anchorBlock.stateRoot := by
  induction reachable with
  | anchor made =>
    unfold getForkchoiceStore at made
    cases hashed : SszType.hashTreeRoot anchorState with
    | error err => simp [hashed, bind, Except.bind, Except.mapError] at made
    | ok root =>
      simp only [hashed, bind, Except.bind, Except.mapError] at made
      split at made
      · simp [throw, throwThe, MonadExceptOf.throw] at made
      · rename_i same
        simp only [not_not.mp same]
  | _ => assumption

/-- A non-anchor block state has the block's slot and its header with an empty state root. -/
theorem Store.Reachable.blockState_header
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state)
    (other : block ≠ anchorBlock) :
    state.slot = block.slot ∧ SszType.hashTreeRoot state = .ok block.stateRoot ∧
      ∃ bodyRoot, SszType.hashTreeRoot block.body = .ok bodyRoot ∧
        state.latestBlockHeader =
          { slot := block.slot, proposerIndex := block.proposerIndex,
            parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } := by
  obtain ⟨post, postOk, -, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  obtain ⟨parent, checks, engine, signed, message, -, transitioned⟩ := produced other
  obtain ⟨advanced, -, -, -, processed, rooted⟩ := stateTransition_ok transitioned
  refine ⟨by simpa [message] using (stateTransition_slot transitioned).2, ?_, ?_⟩
  · simpa [message] using rooted rfl
  · simpa [message] using (processBlock_blockRoots_latestBlockHeader processed).2

/-- Advancing a non-anchor block state reconstructs the block root from its header.

The block's state root must be nonzero so that later empty slots do not replace it. -/
theorem Store.Reachable.blockState_processSlots_header
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork} {state advanced : BeaconState preset fork}
    {checks : SignatureChecks} {slot : Slot}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state)
    (other : block ≠ anchorBlock) (nonzero : block.stateRoot ≠ Vector.replicate 32 0)
    (computed : processSlots config checks state slot = .ok advanced) :
    SszType.hashTreeRoot advanced.latestBlockHeader = .ok root := by
  obtain ⟨-, hashed, bodyRoot, bodyHashed, header⟩ :=
    reachable.blockState_header found stored other
  have filled := processSlots_latestBlockHeader_of_zero
    (by rw [header]) hashed nonzero computed
  rw [filled, header]
  exact (BeaconBlock.hashTreeRoot_header bodyHashed).trans (reachable.root found)

/-- A history read written after a non-anchor block names that block until the next block. -/
theorem Store.Reachable.blockState_processSlots_root
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root readRoot : Root} {block : BeaconBlock preset fork}
    {state advanced : BeaconState preset fork} {checks : SignatureChecks} {slot query : Slot}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state)
    (other : block ≠ anchorBlock) (nonzero : block.stateRoot ≠ Vector.replicate 32 0)
    (computed : processSlots config checks state slot = .ok advanced)
    (read : getBlockRootAtSlot advanced query = .ok readRoot) (later : block.slot ≤ query) :
    readRoot = root := by
  obtain ⟨atSlot, hashed, bodyRoot, bodyHashed, header⟩ :=
    reachable.blockState_header found stored other
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advancedOk⟩ := computed
  have readHash := getBlockRootAtSlot_advanceSlots_of_zero
    (by rw [header]) hashed nonzero advancedOk read (atSlot ▸ later)
  rw [header] at readHash
  have blockHash := (BeaconBlock.hashTreeRoot_header bodyHashed).trans (reachable.root found)
  exact Except.ok.inj (readHash.symm.trans blockHash)

/-- Every held block state hashes to the state root of its block, including the anchor. -/
theorem Store.Reachable.blockState_root
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state) :
    SszType.hashTreeRoot state = .ok block.stateRoot := by
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same, same]
    exact reachable.anchorState_root
  · exact (reachable.blockState_header found stored same).2.1

/-- A history read later than the anchor state names a held block.

The proof follows earlier block states until it reaches the slot run that wrote the root.

For that run, the next block validates the cached header as its held parent. -/
theorem Store.Reachable.blockState_history_known
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {state : BeaconState preset fork} {query : Slot}
    (stored : store.blockStates[root]? = some state)
    (read : getBlockRootAtSlot state query = .ok readRoot)
    (later : anchorState.slot ≤ query) :
    ∃ block, store.blocks[readRoot]? = some block := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · rw [anchored same] at read
    have before := (getBlockRootAtSlot_ok_iff.mp read).1
    have le := UInt64.le_iff_toNat_le.mp later
    omega
  · obtain ⟨parent, checks, engine, signed, message, parentFound, transitioned⟩ := produced same
    obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok transitioned
    have advancedRead : getBlockRootAtSlot advanced query = .ok readRoot := by
      unfold getBlockRootAtSlot at read ⊢
      rwa [(processBlock_slot blockOk), (processBlock_blockRoots_latestBlockHeader blockOk).1]
        at read
    by_cases old : query < parent.slot
    · have run := slotsOk
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
      obtain ⟨_, -, advancedOk⟩ := run
      exact reachable.blockState_history_known nonzero parentFound
        (getBlockRootAtSlot_of_advanceSlots advancedOk advancedRead old) later
    · obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
      have cached := getBlockRootAtSlot_processSlots_header
        (reachable.blockState_root parentKnown parentFound) (nonzero _ _ parentKnown)
        slotsOk advancedRead (UInt64.not_lt.mp old)
      have parentHash := processBlock_parentRoot blockOk
      rw [message] at parentHash
      have eq := Except.ok.inj (cached.symm.trans parentHash)
      exact ⟨parentBlock, eq ▸ parentKnown⟩
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A held child's pre-block history also names held blocks after the anchor state slot. -/
theorem Store.Reachable.preBlock_history_known
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {state advanced : BeaconState preset fork} {query : Slot}
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (stored : store.blockStates[root]? = some state)
    (processed : processBlock config checks engine advanced block = .ok state)
    (read : getBlockRootAtSlot advanced query = .ok readRoot)
    (later : anchorState.slot ≤ query) :
    ∃ ancestor, store.blocks[readRoot]? = some ancestor := by
  apply reachable.blockState_history_known nonzero stored _ later
  unfold getBlockRootAtSlot
  rw [processBlock_slot processed, (processBlock_blockRoots_latestBlockHeader processed).1]
  exact read

end EthLib.Consensus
