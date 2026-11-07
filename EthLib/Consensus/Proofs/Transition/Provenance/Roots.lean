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

/-- An upgrade keeps the slot, the latest header and the two buffers. -/
theorem upgradeNext_roots {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.slot = pre.state.slot ∧
      post.val.state.latestBlockHeader = pre.state.latestBlockHeader ∧
      post.val.state.blockRoots = pre.state.blockRoots ∧
      post.val.state.stateRoots = pre.state.stateRoots := by
  have same := upgradeNext_history computed
  simp only [BeaconState.history, Prod.mk.injEq] at same
  exact ⟨same.1, same.2.1, same.2.2.1, same.2.2.2.1⟩

/-! ## Chains -/

/-- Along a chain the slot never decreases. -/
theorem stepRelation_slot :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      forked.state.slot.toNat ≤ after.state.slot.toNat where
  refl _ := Nat.le_refl _
  trans first second := Nat.le_trans first second
  advanceSlot computed := by
    simp only [advanceSlot_slot computed]
    omega
  upgradeNext _ computed := Nat.le_of_eq (by rw [(upgradeNext_roots computed).1])
  applySignedBlock computed :=
    Nat.le_of_eq (by simp only [(applySignedBlock_roots computed).2.2.2.2.1])

theorem Reaches.slot_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    start.state.slot.toNat ≤ after.state.slot.toNat :=
  stepRelation_slot.reaches chain

/-- A chain caches a slot at one of its slot steps.

The step starts at `state`, whose slot is that slot, and its caching gives `cached`.

The chain runs from its start to `state`, and on from the state after the step. -/
def CachesSlot (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (slot : Slot) {fork : Fork} (state cached : BeaconState preset fork) : Prop :=
  state.slot = slot ∧ processSlot state = .ok cached ∧
    ∃ next, advanceSlot config checks state = .ok next ∧
      Reaches config checks start ⟨fork, state⟩ ∧ Reaches config checks ⟨fork, next⟩ after

theorem CachesSlot.extend {start middle after : ForkedBeaconState preset} {slot : Slot}
    {fork : Fork} {state cached : BeaconState preset fork}
    (caches : CachesSlot config checks start middle slot state cached)
    (step : Step config checks middle after) :
    CachesSlot config checks start after slot state cached :=
  have ⟨atSlot, cachedOk, next, nextOk, head, tail⟩ := caches
  ⟨atSlot, cachedOk, next, nextOk, head, tail.step step⟩

/-- Two different slots less than the length of the buffer apart take different entries. -/
theorem mod_ne_of_lt {n earlier later : UInt64} (before : earlier.toNat < later.toNat)
    (near : later.toNat < earlier.toNat + n.toNat) : later % n ≠ earlier % n := by
  intro same
  have same := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
  have := Nat.sub_mod_eq_zero_of_mod_eq same
  have positive : 0 < later.toNat - earlier.toNat := by omega
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
  rcases k with _ | k
  · omega
  · rw [Nat.mul_succ] at hk
    omega

/-- Where an entry of the two buffers of roots comes from.

Take a chain, and a slot from the start of the chain up to the slot before its end.

The entry must still be in the buffer: the end is at most `N` slots after that slot.

Then one slot step of the chain cached that slot.

The block root is the root of the latest header after that caching.

The state root is the root of the state that the caching started from. -/
theorem Reaches.roots_written {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) {slot : Slot}
    (fromStart : start.state.slot.toNat ≤ slot.toNat) (written : slot.toNat < after.state.slot.toNat)
    (recent : after.state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork),
      CachesSlot config checks start after slot state cached ∧
      (∃ root, hashTreeRoot cached.latestBlockHeader = .ok root ∧
        readCircular after.state.blockRoots.elements slot = .ok root) ∧
      (∃ root, hashTreeRoot state = .ok root ∧
        readCircular after.state.stateRoots.elements slot = .ok root) := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => omega
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next computed =>
      obtain ⟨cached, cachedOk, nextSlot, header, blockRoots, stateRoots⟩ :=
        advanceSlot_roots computed
      obtain ⟨stateRoot, blockRoot, stateRootOk, _, blockRootOk, stateWrite, blockWrite, _⟩ :=
        processSlot_roots cachedOk
      simp only at written recent nextSlot ⊢
      rw [blockRoots, stateRoots]
      by_cases here : slot.toNat = state.slot.toNat
      · -- This step cached the slot.
        have same : state.slot = slot := UInt64.toNat_inj.mp here.symm
        subst same
        refine ⟨fork, state, cached, ⟨rfl, cachedOk, next, computed, middleChain, .refl _⟩,
          ⟨blockRoot, blockRootOk, ?_⟩, ⟨stateRoot, stateRootOk, ?_⟩⟩
        · exact readCircular_writeCircular blockWrite
        · exact readCircular_writeCircular stateWrite
      · -- An earlier step cached it, and this step writes another entry.
        obtain ⟨fork', state', cached', caches, ⟨blockRoot', blockRootOk', blockRead⟩,
          ⟨stateRoot', stateRootOk', stateRead⟩⟩ :=
          more (by simp only; omega) (by simp only; omega)
        have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
            slot % preset.SLOTS_PER_HISTORICAL_ROOT :=
          mod_ne_of_lt (by simp only at *; omega) (by simp only at *; omega)
        refine ⟨fork', state', cached', caches.extend (.slot computed),
          ⟨blockRoot', blockRootOk', ?_⟩, ⟨stateRoot', stateRootOk', ?_⟩⟩
        · rw [readCircular_writeCircular_of_ne blockWrite other]
          exact blockRead
        · rw [readCircular_writeCircular_of_ne stateWrite other]
          exact stateRead
    | upgrade due computed =>
      obtain ⟨slotSame, _, blockRoots, stateRoots⟩ := upgradeNext_roots computed
      rw [slotSame] at written recent
      obtain ⟨fork', state', cached', caches, blockPart, statePart⟩ :=
        more written recent
      rw [blockRoots, stateRoots]
      exact ⟨fork', state', cached', caches.extend (.upgrade due computed), blockPart, statePart⟩
    | block engine signed validateResult computed =>
      obtain ⟨-, -, -, -, slotSame, blockRoots, stateRoots, -⟩ := applySignedBlock_roots computed
      simp only at written recent ⊢
      rw [slotSame] at written recent
      obtain ⟨fork', state', cached', caches, blockPart, statePart⟩ :=
        more written recent
      rw [blockRoots, stateRoots]
      exact ⟨fork', state', cached', caches.extend (.block engine signed validateResult computed),
        blockPart, statePart⟩

end EthLib.Consensus
