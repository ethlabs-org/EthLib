module

public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.Models.Network.Model

/-!
# Proofs: honest validators that run the fork choice over the network

Each honest validator keeps a store of the fork choice.

At each move it ticks its store to the current time, or processes a message of its view.

The messages are those of the fork choice handlers.

A block is processed with the votes and slashings that it carries.

The block is rejected with them when one of them is rejected.

A message that the handler rejects leaves the store as it was, and may be processed later.

What lies outside the beacon chain, such as the execution engine, is one source for all.

The store of each honest validator stays reachable from the anchor along every execution.

Along an execution of the network model, an honest store that starts with a forward clock keeps one.

An honest store built with the signature checks of the model stays built that way.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A message of the fork choice. -/
inductive Message (preset : Preset) (fork : Fork)
  /-- A signed block. -/
  | block (signed : SignedBeaconBlock preset fork)
  /-- An attestation. -/
  | attestation (attestation : Attestation preset fork)
  /-- An attester slashing. -/
  | attesterSlashing (slashing : AttesterSlashing preset fork)
  /-- From Gloas, a vote of a member of the payload committee. -/
  | payloadAttestation (gloas : .glamsterdam ≤ fork) (message : PayloadAttestationMessage)
  /-- From Gloas, a signed envelope. -/
  | envelope (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork)
  /-- From Heze, a signed inclusion list. -/
  | inclusionList (heze : .hegota ≤ fork) (signed : SignedInclusionList)

/-- The moves of the store of an honest validator, at a time and with a view.

A tick sets the store to the time, which must fit in 64 bits.

That time must not lie before the clock of the store.

Every other move processes a message of the view, as one from the network.

The votes inside a block are processed with it, and a rejected vote rejects the block.

Blocks and envelopes are judged with the given sources outside the beacon chain. -/
inductive Handles (config : Config) (checks : SignatureChecks) (sources : BlockSources preset fork)
    (time : ℕ) (view : Set (Message preset fork)) (store : Store preset fork) :
    Store preset fork → Prop
  /-- The store after a tick at the time. -/
  | tick {after : Store preset fork} :
    store.timeMs.toNat ≤ time → time < 2 ^ 64 → store.onTick config time.toUInt64 = .ok after →
      Handles config checks sources time view store after
  /-- The store after a block of the view, with its votes. -/
  | block {after : Store preset fork} {signed : SignedBeaconBlock preset fork} :
    .block signed ∈ view → store.onBlockWithVotes config checks sources signed = .ok after →
      Handles config checks sources time view store after
  /-- The store after an attestation of the view. -/
  | attestation {after : Store preset fork} {attestation : Attestation preset fork} :
    .attestation attestation ∈ view →
      store.onAttestation config checks attestation false = .ok after →
      Handles config checks sources time view store after
  /-- The store after an attester slashing of the view. -/
  | attesterSlashing {after : Store preset fork} {slashing : AttesterSlashing preset fork} :
    .attesterSlashing slashing ∈ view →
      store.onAttesterSlashing config checks slashing = .ok after →
      Handles config checks sources time view store after
  /-- From Gloas, the store after a vote of the payload committee from the view. -/
  | payloadAttestation {after : Store preset fork} {gloas : .glamsterdam ≤ fork}
      {message : PayloadAttestationMessage} :
    .payloadAttestation gloas message ∈ view →
      store.onPayloadAttestationMessage config checks gloas message false = .ok after →
      Handles config checks sources time view store after
  /-- From Gloas, the store after a signed envelope of the view. -/
  | envelope {after : Store preset fork} {gloas : .glamsterdam ≤ fork}
      {signed : SignedExecutionPayloadEnvelope preset fork} :
    .envelope gloas signed ∈ view →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      Handles config checks sources time view store after
  /-- From Heze, the store after an inclusion list of the view. -/
  | inclusionList {after : Store preset fork} {heze : .hegota ≤ fork}
      {signed : SignedInclusionList} :
    .inclusionList heze signed ∈ view →
      store.onInclusionList config checks heze signed = .ok after →
      Handles config checks sources time view store after

/-- The protocol where honest validators run the fork choice.

The signed statements of a message and the messages that honest validators send are parameters.

The moves of an honest validator are those of its store, with sources shared by all. -/
def forkChoice {ν κ : Type*} (config : Config) (checks : SignatureChecks)
    (sources : BlockSources preset fork) (signed : Message preset fork → Set (ν × κ))
    (sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop) :
    Protocol ν (Message preset fork) (Store preset fork) κ where
  signed := signed
  Sends := sends
  Moves := fun _ time view store after => Handles config checks sources time view store after

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- A move of the store leads from a reachable store to a reachable store. -/
theorem Handles.reachable {checks : SignatureChecks} {sources : BlockSources preset fork}
    {time : ℕ} {view : Set (Message preset fork)} {store after : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    Store.Reachable config anchorState anchorBlock after := by
  cases handles with
  | tick _ _ ticked => exact reachable.tick ticked
  | block _ added => exact reachable.onBlockWithVotes added
  | attestation _ attested => exact reachable.attestation attested
  | attesterSlashing _ slashed => exact reachable.attesterSlashing slashed
  | payloadAttestation _ voted => exact reachable.payloadAttestation voted
  | envelope _ accepted => exact reachable.envelope accepted
  | inclusionList _ accepted => exact reachable.inclusionList accepted

/-- A move of the store keeps each checkpoint, or moves it to one at a greater epoch. -/
theorem Handles.checkpointsAdvance {checks : SignatureChecks}
    {sources : BlockSources preset fork} {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (handles : Handles config checks sources time view store after) :
    store.CheckpointsAdvance after := by
  cases handles with
  | tick _ _ ticked => exact (Store.onTick_frame ticked).2.1
  | block _ added => exact Store.onBlockWithVotes_checkpointsAdvance added
  | attestation _ attested => exact (Store.onAttestation_frame attested).1
  | attesterSlashing _ slashed => exact (Store.onAttesterSlashing_frame slashed).1
  | payloadAttestation _ voted =>
    exact (Store.onPayloadAttestationMessage_onlyPtcVotes voted).frame.1
  | envelope _ accepted => exact (Store.onExecutionPayloadEnvelope_frame accepted).1
  | inclusionList _ accepted => exact (Store.onInclusionList_frame accepted).1

/-- Along an execution, the store of each honest validator stays reachable from the anchor.

The stores of the honest validators must be reachable at the start. -/
theorem Execution.reachable {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.Reachable config anchorState anchorBlock (e.start v)) (n : ℕ) :
    ∀ v ∈ J, Store.Reachable config anchorState anchorBlock ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ reachable moved => moved.reachable reachable) n

/-- A move of an honest validator keeps its store reachable with a forward clock. -/
theorem Handles.forwardReachable {checks : SignatureChecks} {sources : BlockSources preset fork}
    {time : ℕ} {view : Set (Message preset fork)} {store after : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (forward : Store.ForwardReachable config anchorState anchorBlock store) :
    Store.ForwardReachable config anchorState anchorBlock after := by
  cases handles with
  | tick le lt ticked =>
    refine forward.tick ?_ ticked
    rw [UInt64.le_iff_toNat_le, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' lt]
    exact le
  | block _ added => exact forward.onBlockWithVotes added
  | attestation _ attested => exact forward.attestation attested
  | attesterSlashing _ slashed => exact forward.attesterSlashing slashed
  | payloadAttestation _ voted => exact forward.payloadAttestation voted
  | envelope _ accepted => exact forward.envelope accepted
  | inclusionList _ accepted => exact forward.inclusionList accepted

/-- Along an execution, the store of each honest validator stays reachable with a forward clock.

The stores of the honest validators must be reachable with a forward clock at the start. -/
theorem Execution.forwardReachable {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.ForwardReachable config anchorState anchorBlock (e.start v)) (n : ℕ) :
    ∀ v ∈ J, Store.ForwardReachable config anchorState anchorBlock ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ forward moved => moved.forwardReachable forward) n

/-- A move of an honest validator keeps its store built with the setting of the checks of the model.

The clock of that store also stays forward. -/
theorem Handles.forwardReachableWith {checks : SignatureChecks}
    {sources : BlockSources preset fork} {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store) :
    Store.ForwardReachableWith config checks anchorState anchorBlock after := by
  cases handles with
  | tick le lt ticked =>
    refine reached.tick ?_ ticked
    rw [UInt64.le_iff_toNat_le, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' lt]
    exact le
  | block _ added => exact reached.onBlockWithVotes added
  | attestation _ attested => exact reached.attestation attested
  | attesterSlashing _ slashed => exact reached.attesterSlashing slashed
  | payloadAttestation _ voted => exact reached.payloadAttestation voted
  | envelope _ accepted => exact reached.envelope accepted
  | inclusionList _ accepted => exact reached.inclusionList accepted

/-- Along an execution, each honest store stays built with the setting of the checks of the model.

The stores of the honest validators must be built that way at the start. -/
theorem Execution.forwardReachableWith {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.ForwardReachableWith config checks anchorState anchorBlock (e.start v))
    (n : ℕ) :
    ∀ v ∈ J, Store.ForwardReachableWith config checks anchorState anchorBlock
      ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ reached moved => moved.forwardReachableWith reached) n

/-- A store can start from a mainnet state at slot zero and a block with the root of that state.

Other presets are not covered.
-/
theorem exists_getForkchoiceStore (config : Config) {state : BeaconState .mainnet fork}
    (zero : state.slot = 0) (block : BeaconBlock .mainnet fork) :
    ∃ stateRoot store, SszType.hashTreeRoot state = .ok stateRoot ∧
      getForkchoiceStore config state { block with stateRoot } = .ok store := by
  have : NeZero Preset.mainnet.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  obtain ⟨stateRoot, rooted⟩ := SszType.hashTreeRoot_total state
  obtain ⟨blockRoot, blockRooted⟩ :=
    SszType.hashTreeRoot_total ({ block with stateRoot } : BeaconBlock .mainnet fork)
  have time : computeTimeAtSlotMs config (secondsToMilliseconds state.genesisTime) state.slot =
      .ok (secondsToMilliseconds state.genesisTime) := by
    have fits := UInt64.toNat_lt (secondsToMilliseconds state.genesisTime)
    simp [computeTimeAtSlotMs, zero, Uint64.mulChecked, Uint64.addChecked, bind, Except.bind,
      fits]
  refine ⟨stateRoot, ?_⟩
  simp only [true_and, getForkchoiceStore, rooted, blockRooted, time, Except.mapError, bind,
    Except.bind, ne_eq, not_true_eq_false, ite_false]
  exact ⟨_, rfl⟩

/-- A store ticks to a time in its current slot by setting its clock to that time alone. -/
theorem onTick_sameSlot {store : Store preset fork} {slot : Slot} {timeMs : UInt64}
    (current : store.getCurrentSlot config = .ok slot)
    (slotted : computeSlotAtTimeMs config store.genesisTimeMs timeMs = .ok slot) :
    store.onTick config timeMs = .ok { store with timeMs } := by
  have caught : Store.catchUp config store slot = .ok store := by
    rw [Store.catchUp]
    simp [current, bind, Except.bind, pure, Except.pure]
  have later : ({ store with timeMs } : Store preset fork).getCurrentSlot config = .ok slot := by
    simp [Store.getCurrentSlot, slotted, Except.mapError]
  have ticked : store.onTickPerSlot config timeMs = .ok { store with timeMs } := by
    simp [Store.onTickPerSlot, current, later, computeSlotsSinceEpochStart,
      computeStartSlotAtEpoch_computeEpochAtSlot, bind, Except.bind, pure, Except.pure,
      Except.mapError]
  simp [Store.onTick, slotted, caught, ticked, Except.mapError, bind, Except.bind]

/-- A store whose clock has a slot ticks to its own time and stays as it is. -/
theorem onTick_timeMs {store : Store preset fork} {slot : Slot}
    (current : store.getCurrentSlot config = .ok slot) :
    store.onTick config store.timeMs = .ok store := by
  have slotted : computeSlotAtTimeMs config store.genesisTimeMs store.timeMs = .ok slot := by
    unfold Store.getCurrentSlot at current
    cases computed : computeSlotAtTimeMs config store.genesisTimeMs store.timeMs with
    | error e => simp [computed, Except.mapError] at current
    | ok s => simpa [computed, Except.mapError] using current
  exact onTick_sameSlot current slotted

/-- A store built from an anchor can tick to its own time, when slots last a positive time.

So an honest validator can move from such a store, whatever its view. -/
theorem Handles.tick_anchor {checks : SignatureChecks} {sources : BlockSources preset fork}
    {store : Store preset fork} (positive : 0 < config.SLOT_DURATION_MS)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (view : Set (Message preset fork)) :
    Handles config checks sources store.timeMs.toNat view store store := by
  refine .tick le_rfl (UInt64.toNat_lt _) ?_
  have round : store.timeMs.toNat.toUInt64 = store.timeMs :=
    UInt64.toNat_inj.mp (by simp)
  rw [round]
  exact onTick_timeMs (getCurrentSlot_getForkchoiceStore positive anchored)

/-- Honest validators that run the fork choice have an execution where a block reaches all.

No message carries a signed statement here, so unforgeability asks nothing.

Each validator starts from a store built from an anchor, and the clock starts at its time.

An honest validator sends a block from an empty view, as the protocol allows.

Two events later every validator has the block, with the clock and the stores as at the start.

The stores stay reachable.

There the honest validator may also move to its own store, when slots last a positive time.

The execution is partially synchronous for every GST and every positive delay. -/
theorem exists_forkChoice_execution {ν κ : Type*} [DecidableEq ν] (checks : SignatureChecks)
    (sources : BlockSources preset fork) {store : Store preset fork}
    (slots : 0 < config.SLOT_DURATION_MS)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    {J : Set ν} {v : ν} (honest : v ∈ J) (signed : SignedBeaconBlock preset fork) {Δ : ℕ}
    (positive : 0 < Δ) :
    ∃ e : Execution (forkChoice config checks sources (fun _ => (∅ : Set (ν × κ)))
        fun _ _ _ _ m => m = .block signed) J,
      e.startTime = store.timeMs.toNat ∧ e.start = (fun _ => store) ∧
      e.events 0 = .send v (.block signed) ∧ (e.world 2).time = store.timeMs.toNat ∧
      (e.world 2).state = (fun _ => store) ∧ (∀ u, .block signed ∈ (e.world 2).view u) ∧
      Allowed (forkChoice config checks sources (fun _ => (∅ : Set (ν × κ)))
        fun _ _ _ _ m => m = .block signed) J (e.world 2) (.move v store) ∧
      (∀ GST, e.PartiallySynchronous GST Δ) ∧
      ∀ n, ∀ u ∈ J, Store.Reachable config anchorState anchorBlock ((e.world n).state u) := by
  obtain ⟨e, startTime, start, sends, time, states, delivered, sync⟩ :=
    exists_partiallySynchronous
      (P := forkChoice config checks sources (fun _ => (∅ : Set (ν × κ)))
        fun _ _ _ _ m => m = .block signed) (time := store.timeMs.toNat)
      (state := fun _ => store) honest rfl (fun _ none => none.elim) positive
  refine ⟨e, startTime, start, sends, time, states, delivered, ⟨honest, ?_⟩, sync,
    e.reachable fun u _ => ?_⟩
  · show Handles config checks sources (e.world 2).time ((e.world 2).view v)
      ((e.world 2).state v) store
    rw [time, states]
    exact Handles.tick_anchor slots anchored _
  rw [start]
  exact .anchor anchored

section CheckpointStates

variable {checks : SignatureChecks} {sources : BlockSources preset fork}
  {κ : Type} {signed : Message preset fork → Set (ValidatorIndex × κ)}
  {sends : ValidatorIndex → Nat → Set (Message preset fork) → Store preset fork →
    Message preset fork → Prop} {J : Set ValidatorIndex}
  {e : Execution (forkChoice config checks sources signed sends) J}

/-- The state that a store keeps for a checkpoint comes from the state of its block.

It is the state of the block when that is at the start of the epoch or later.

Otherwise it is that state processed with the given checks to the start of the epoch. -/
private def CheckpointStatesChecked (config : Config) (checks : SignatureChecks)
    (store : Store preset fork) : Prop :=
  ∀ ⦃checkpoint : Checkpoint⦄ ⦃state : BeaconState preset fork⦄,
    store.checkpointStates[checkpoint]? = some state →
      ∃ base start, store.blockStates[checkpoint.root]? = some base ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok start ∧
        ((start ≤ base.slot ∧ state = base) ∨
          (base.slot < start ∧ processSlots config checks base start = .ok state))

/-- Two checkpoints equal in the order of checkpoints are the same checkpoint. -/
private theorem checkpoint_eq_of_compare_eq {a b : Checkpoint}
    (same : Checkpoint.compare a b = .eq) : a = b := by
  unfold Checkpoint.compare at same
  rw [Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq,
    Std.LawfulEqCmp.compare_eq_iff_eq] at same
  cases a
  cases b
  cases same.1
  cases same.2
  rfl

private theorem CheckpointStatesChecked.of_maps {store after : Store preset fork}
    (holds : CheckpointStatesChecked config checks store)
    (states : after.blockStates = store.blockStates)
    (kept : after.checkpointStates = store.checkpointStates) :
    CheckpointStatesChecked config checks after := by
  intro checkpoint state found
  rw [kept] at found
  rw [states]
  exact holds found

private theorem CheckpointStatesChecked.of_compute {store : Store preset fork}
    {target : Checkpoint} {state : BeaconState preset fork}
    (computed : store.computeCheckpointState config checks target = .ok state) :
    ∃ base start, store.blockStates[target.root]? = some base ∧
      computeStartSlotAtEpoch preset target.epoch = .ok start ∧
      ((start ≤ base.slot ∧ state = base) ∨
        (base.slot < start ∧ processSlots config checks base start = .ok state)) := by
  unfold Store.computeCheckpointState at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨base, found, start, startOk, computed⟩ := computed
  refine ⟨base, start, Store.blockState_ok_iff.mp found, Base.mapError_ok_iff.mp startOk, ?_⟩
  split at computed
  · exact .inr ⟨‹_›, Base.mapError_ok_iff.mp computed⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact .inl ⟨UInt64.not_lt.mp ‹_›, computed.symm⟩

private theorem CheckpointStatesChecked.block {store after : Store preset fork}
    {signed : SignedBeaconBlock preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (holds : CheckpointStatesChecked config checks store)
    (added : store.onBlock config checks sources signed = .ok after) :
    CheckpointStatesChecked config checks after := by
  rcases Store.onBlock_same_or_insert added with
    same | ⟨blockRoot, -, fresh, blocks, -, state, -, -, states⟩
  · subst same
    exact holds
  have kept := (Store.onBlock_checkpointStates_latestMessages added).1
  intro checkpoint checkpointState found
  rw [kept] at found
  obtain ⟨base, start, baseFound, rest⟩ := holds found
  refine ⟨base, start, ?_, rest⟩
  have other : blockRoot ≠ checkpoint.root := by
    rintro rfl
    rw [reachable.blockState_eq_none fresh] at baseFound
    cases baseFound
  rw [states, getElem?_insert_root]
  simp only [other, ↓reduceIte]
  exact baseFound

private theorem CheckpointStatesChecked.attestation {store after : Store preset fork}
    {attestation : Attestation preset fork} {isFromBlock : Bool}
    (holds : CheckpointStatesChecked config checks store)
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    CheckpointStatesChecked config checks after := by
  obtain ⟨-, -, states⟩ := Store.onAttestation_frame attested
  unfold Store.onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
  have storedFrom : CheckpointStatesChecked config checks stored := by
    unfold Store.storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact holds
    · simp only [bind_ok_iff] at storing
      obtain ⟨computedState, computed, storing⟩ := storing
      simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      intro checkpoint state keptFound
      simp only [Std.TreeMap.getElem?_insert] at keptFound
      split at keptFound
      · rename_i same
        cases keptFound
        obtain rfl := checkpoint_eq_of_compare_eq same
        exact CheckpointStatesChecked.of_compute computed
      · exact holds keptFound
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    intro checkpoint state found
    exact storedFrom found
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

private theorem CheckpointStatesChecked.step {store after : Store preset fork}
    {time : Nat} {view : Set (Message preset fork)}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (holds : CheckpointStatesChecked config checks store)
    (moved : Handles config checks sources time view store after) :
    CheckpointStatesChecked config checks after := by
  cases moved with
  | tick _ _ ticked =>
    exact holds.of_maps (Store.onTick_frame ticked).2.2.2
      (Store.onTick_checkpointStates_latestMessages ticked).1
  | block _ added =>
    exact (Store.onBlockWithVotes_preserves
      (P := fun s => Store.Reachable config anchorState anchorBlock s ∧
        CheckpointStatesChecked config checks s)
      (fun h added => ⟨h.1.block added, CheckpointStatesChecked.block h.1 h.2 added⟩)
      (fun _ h attested => ⟨h.1.attestation attested,
        CheckpointStatesChecked.attestation h.2 attested⟩)
      (fun _ h slashed => ⟨h.1.attesterSlashing slashed,
        h.2.of_maps (Store.onAttesterSlashing_frame slashed).2.2.1
          (Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1⟩)
      ⟨reachable, holds⟩ added).2
  | attestation _ attested => exact CheckpointStatesChecked.attestation holds attested
  | attesterSlashing _ slashed =>
    exact holds.of_maps (Store.onAttesterSlashing_frame slashed).2.2.1
      (Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1
  | payloadAttestation _ voted =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact holds
  | envelope _ accepted =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact holds
  | inclusionList _ accepted =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
    exact holds

/-- The state of a checkpoint of an honest store comes from the state of its block.

It is that state when that state is at the start of the epoch or later.

Otherwise it is that state with its slots processed to the start of the epoch.

The slots are processed with the checks of the execution. -/
theorem Execution.checkpointState_fromBlock {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {w : ValidatorIndex} (honest : w ∈ J) {k : Nat}
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (found : ((e.world k).state w).checkpointState checkpoint = .ok state) :
    ∃ base boundary, ((e.world k).state w).blockStates[checkpoint.root]? = some base ∧
      computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧
      ((boundary ≤ base.slot ∧ state = base) ∨
        (base.slot < boundary ∧ processSlots config checks base boundary = .ok state)) := by
  have both : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) ∧
      CheckpointStatesChecked config checks ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w) ∧
        CheckpointStatesChecked config checks (e.start w)
      rw [start w honest]
      refine ⟨.anchor anchored, ?_⟩
      obtain ⟨anchorRoot, rootOk, states⟩ := getForkchoiceStore_checkpointStates anchored
      obtain ⟨_, rootOk', blocks, blockStates⟩ := getForkchoiceStore_maps anchored
      rw [rootOk, Except.ok.injEq] at rootOk'
      subst rootOk'
      intro checkpoint state found
      rw [states, Std.TreeMap.getElem?_insert] at found
      split at found
      · rename_i same
        cases found
        obtain rfl := checkpoint_eq_of_compare_eq same
        have startOk := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset)
          anchorState.slot
        refine ⟨anchorState, _, by simp [blockStates], startOk, .inl ⟨?_, rfl⟩⟩
        obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
        rw [UInt64.le_iff_toNat_le, value, computeEpochAtSlot, UInt64.toNat_div]
        exact Nat.div_mul_le_self _ _
      · simp at found
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact ⟨moved.reachable ih.1, CheckpointStatesChecked.step ih.1 ih.2 moved⟩
  exact (both k).2 (Store.checkpointState_ok_iff.mp found)

end CheckpointStates

end EthLib.Consensus.Models.Network
