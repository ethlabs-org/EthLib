module

public import EthLib.Consensus.Proofs.Transition.Provenance.Kept
public import EthLib.Consensus.Proofs.Transition.Reachable
public import EthLib.Consensus.Proofs.Transition.Slot

/-!
# Proofs: where the block roots and state roots come from

A state keeps the roots of its recent history in two circular buffers.

```text
    blockRoots[slot mod N]  the root of the latest block header, cached at that slot
    stateRoots[slot mod N]  the root of the state at the end of that slot
```

Here `N` is `SLOTS_PER_HISTORICAL_ROOT`.

Only the caching of a slot, `processSlot`, writes the buffers.

It writes one entry, at the slot of the state.

It also fills the state root of the latest block header, if that root is still zero.

A block writes the header, with a zero state root, since the state after it has no root yet.

This file traces each entry of a buffer to the slot step of a chain that wrote it.

It traces the latest header to the block step that wrote it, or to the start of the chain.

No statement assumes that SHA-256 has no collision, or that no state has the zero root.

The zero root matters: a header whose state root stays zero is filled again at the next slot.

So when the state after a block has the zero root, the header can take a later state's root.

The statements keep that case as an explicit alternative.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The latest header with its state root filled, as the caching of a slot does.

A header whose state root is not zero keeps it. -/
def fillStateRoot (header : BeaconBlockHeader) (stateRoot : Root) : BeaconBlockHeader :=
  if header.stateRoot = Vector.replicate 32 0 then { header with stateRoot } else header

/-! ## One step -/

/-- What the caching of a slot writes.

The root of the state goes into the state roots, at the slot of the state.

The latest header has its state root filled with that root, if it was zero.

The root of that header goes into the block roots, at the same slot.

The justification bits stay. -/
theorem processSlot_roots (computed : processSlot state = .ok after) :
    ∃ stateRoot blockRoot,
      hashTreeRoot state = .ok stateRoot ∧
      after.latestBlockHeader = fillStateRoot state.latestBlockHeader stateRoot ∧
      hashTreeRoot after.latestBlockHeader = .ok blockRoot ∧
      writeCircular state.stateRoots.elements state.slot stateRoot =
        .ok after.stateRoots.elements ∧
      writeCircular state.blockRoots.elements state.slot blockRoot =
        .ok after.blockRoots.elements ∧
      after.justificationBits = state.justificationBits := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨stateRoot, stateRootOk, stateRoots, stateRootsOk, blockRoot, blockRootOk, blockRoots,
    blockRootsOk, computed⟩ := computed
  -- From Gloas the last step also clears one bit of payload availability, and nothing else.
  have last : after = { state with
      stateRoots, latestBlockHeader := fillStateRoot state.latestBlockHeader stateRoot,
      blockRoots } ∨
      ∃ availability, after = { state with
        stateRoots, latestBlockHeader := fillStateRoot state.latestBlockHeader stateRoot,
        blockRoots, executionPayloadAvailability := availability } := by
    split at computed
    · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
      exact .inr ⟨_, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl computed.symm
  have stateWrite := writeCircularRooted_elements state.stateRoots state.slot stateRoot
  have blockWrite := writeCircularRooted_elements state.blockRoots state.slot blockRoot
  rw [stateRootsOk] at stateWrite
  rw [blockRootsOk] at blockWrite
  rcases last with rfl | ⟨_, rfl⟩ <;>
    exact ⟨stateRoot, blockRoot, stateRootOk, rfl, blockRootOk, stateWrite.symm,
      blockWrite.symm, rfl⟩

/-- One slot step caches the slot, then may close the epoch, then moves the slot on.

Closing the epoch keeps the header and the two buffers, so they are those of the cached state.
-/
theorem advanceSlot_roots (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, processSlot state = .ok cached ∧
      after.slot.toNat = state.slot.toNat + 1 ∧
      after.latestBlockHeader = cached.latestBlockHeader ∧
      after.blockRoots = cached.blockRoots ∧ after.stateRoots = cached.stateRoots := by
  have slot := advanceSlot_slot computed
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  refine ⟨cached, cachedOk, slot, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, kept⟩ := processEpoch_kept epochedOk
    obtain ⟨header, blockRoots, stateRoots⟩ := processJustificationAndFinalization_roots justifiedOk
    exact ⟨kept.latestBlockHeader.trans header, kept.blockRoots.trans blockRoots,
      kept.stateRoots.trans stateRoots⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, rfl⟩

/-- What a block step writes.

The block runs at the slot of the state, after the latest block, and names it as its parent.

From Gloas the payload of the parent runs first, and keeps the latest header.

The new latest header is that of the block, with a zero state root.

The slot and the two buffers stay.

When the result is validated, the block's state root is the root of the state after it. -/
theorem applySignedBlock_roots {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : applySignedBlock config checks engine state signed validateResult = .ok after) :
    signed.message.slot = state.slot ∧
      state.latestBlockHeader.slot < signed.message.slot ∧
      hashTreeRoot state.latestBlockHeader = .ok signed.message.parentRoot ∧
      (∃ bodyRoot, hashTreeRoot signed.message.body = .ok bodyRoot ∧
        after.latestBlockHeader =
          { slot := signed.message.slot, proposerIndex := signed.message.proposerIndex,
            parentRoot := signed.message.parentRoot, stateRoot := Vector.replicate 32 0,
            bodyRoot }) ∧
      after.slot = state.slot ∧ after.blockRoots = state.blockRoots ∧
      after.stateRoots = state.stateRoots ∧
      (validateResult = true → hashTreeRoot after = .ok signed.message.stateRoot) := by
  obtain ⟨-, processed, validated⟩ := applySignedBlock_ok computed
  obtain ⟨paid, headed, paidKept, headedOk, headedKept⟩ := processBlock_kept processed
  obtain ⟨slot, newer, -, parent, -⟩ := processBlockHeader_checks headedOk
  obtain ⟨bodyRoot, bodyRootOk, rfl⟩ := processBlockHeader_eq headedOk
  rw [paidKept.latestBlockHeader, paidKept.slot] at *
  exact ⟨slot, newer, parent, ⟨bodyRoot, bodyRootOk, headedKept.latestBlockHeader⟩,
    headedKept.slot, headedKept.blockRoots.trans paidKept.blockRoots,
    headedKept.stateRoots.trans paidKept.stateRoots, validated⟩

end EthLib.Consensus
