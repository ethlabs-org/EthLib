module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety
public import EthLib.Consensus.Proofs.ForkChoice.AccountableCheckpoints
public import EthLib.Consensus.Proofs.DirectSafety.TerminalSafety
import EthLib.Consensus.Proofs.Transition.BlockRoots
import EthLib.Consensus.Proofs.Transition.FfgSlack
import EthLib.Consensus.Proofs.Transition.TargetSlots
import EthLib.Consensus.Proofs.Transition.TargetVotes

/-!
# Accountable fast-confirmation safety

`Execution.safeAt_confirmedRoot` assumes that honest stores agree on finalized prefixes, on one
justified checkpoint per epoch and on one block per root, and that held blocks have nonzero state
roots.

Here each of those facts is derived, or else the stores of two honest validators show a fault.

A fault is accountable: validators with enough stake signed slashable votes, up to the drift of
effective balances.

Or it is a concrete hash fault: a collision of two hash inputs, or a hash input with a zero root.

The derivation reads the runs of the state transition from a genesis state to the held states.

It uses the accountable safety theorems of `DirectSafety`, which follow
[Combining GHOST and Casper][gasper], Lemmas 4.11 and 5.1.

[gasper]: https://arxiv.org/abs/2003.03052
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models DirectSafety Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- A state that an honest store holds for one of its blocks, at an event up to a last time. -/
def Execution.HeldState
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (limit : ℕ) (state : BeaconState preset fork) : Prop :=
  ∃ w ∈ J, ∃ (k : ℕ) (root : Root), (e.world k).time ≤ limit ∧
    ((e.world k).state w).blockStates[root]? = some state

/-- Two held states whose runs show accountable stake for a checkpoint conflict.

Each run starts at a genesis state, goes through the history to the anchor, then to a held state.

Each held state is read as it is or after one justification step, as `TerminalView` says.

The justified checkpoint `j` of one of the two views is at most the horizon.

The bound is that of `accountable_terminal_finalized_prefix`, with the drift up to `j`.

The reference state is the anchor, or else the genesis state with the whole run as its tail. -/
def Execution.AccountableFault
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) {g : ForkedBeaconState preset}
    (history : Run config checks g ⟨fork, anchorState⟩) (horizon : Epoch) (limit : ℕ) : Prop :=
  ∃ (stateA stateB : BeaconState preset fork)
    (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
    (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
    (va : TerminalView ⟨fork, stateA⟩) (vb : TerminalView ⟨fork, stateB⟩) (j : Checkpoint),
    e.HeldState limit stateA ∧ e.HeldState limit stateB ∧
    (j = va.state.previousJustifiedCheckpoint ∨ j = va.state.currentJustifiedCheckpoint ∨
      j = vb.state.previousJustifiedCheckpoint ∨ j = vb.state.currentJustifiedCheckpoint) ∧
    j.epoch ≤ horizon ∧
    (Quorum.weight (effectiveWeight anchorState) (activeKeys anchorState) ≤
        3 * Quorum.weight (effectiveWeight anchorState)
          (accountableKeys (history.append left) (history.append right) ⟨fork, anchorState⟩) +
        2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) ∨
      Quorum.weight (effectiveWeight g.state) (activeKeys g.state) ≤
        3 * Quorum.weight (effectiveWeight g.state)
          (accountableKeys ((Run.nil).append (history.append left))
            ((Run.nil).append (history.append right)) g) +
        2 * max (terminalDrift j.epoch.toNat (history.append left) va)
          (terminalDrift j.epoch.toNat (history.append right) vb))

/-- Two held states whose runs, with the anchor block, show a concrete hash fault.

The hash inputs are those of the two runs, of the two views, and the header of the anchor block. -/
def Execution.HashFault
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) {g : ForkedBeaconState preset}
    (history : Run config checks g ⟨fork, anchorState⟩) (limit : ℕ) : Prop :=
  ∃ (stateA stateB : BeaconState preset fork)
    (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
    (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
    (va : TerminalView ⟨fork, stateA⟩) (vb : TerminalView ⟨fork, stateB⟩),
    e.HeldState limit stateA ∧ e.HeldState limit stateB ∧
    HashEvidence ((history.append left).hashObjects ++ (history.append right).hashObjects ++
      va.hashObjects ++ vb.hashObjects ++ (blockHeader anchorBlock).toList.map HashObject.header)

/-- A state holds the justified checkpoints of an epoch, and records its first root, at one root.

This holds trivially when the state neither justifies the epoch nor can read its root. -/
def EpochRootFixed (epoch : Epoch) (root : Root) (state : BeaconState preset fork) : Prop :=
  (state.currentJustifiedCheckpoint.epoch = epoch → state.currentJustifiedCheckpoint.root = root) ∧
  (state.previousJustifiedCheckpoint.epoch = epoch →
    state.previousJustifiedCheckpoint.root = root) ∧
  ∀ read, getBlockRoot state epoch = .ok read → read = root

/-- One slot keeps the fixed root of an epoch whose first slot is at or before the slot.

At the first slot of the epoch itself the slot records its header, which must have that root. -/
theorem EpochRootFixed.of_advanceSlot
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} {root : Root} {state after : BeaconState preset fork}
    (holds : EpochRootFixed epoch root state)
    (computed : advanceSlot config checks state = .ok after)
    (first : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat = state.slot.toNat →
      SszType.hashTreeRoot after.latestBlockHeader = .ok root) :
    EpochRootFixed epoch root after := by
  obtain ⟨current, previous, reads⟩ := holds
  refine ⟨?_, ?_, ?_⟩
  · intro same
    by_cases kept : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
    · rw [kept] at same ⊢
      exact current same
    · obtain ⟨-, rootOk, -⟩ :=
        advanceSlot_getBlockRoot_currentJustified_of_ne window computed kept
      rw [same] at rootOk
      exact reads _ rootOk
  · rcases advanceSlot_previousJustified computed with same | ⟨same, -⟩
    · rw [same]
      exact previous
    · rw [same]
      exact current
  · intro read rootOk
    obtain ⟨start, startOk, atSlot⟩ := getBlockRoot_ok_iff.mp rootOk
    rcases getBlockRootAtSlot_advanceSlot_cases computed atSlot with ⟨-, old⟩ | ⟨same, hashed⟩
    · exact reads read (getBlockRoot_ok_iff.mpr ⟨start, startOk, old⟩)
    · have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
      rw [first (by rw [← startNat, same])] at hashed
      exact (Except.ok.inj hashed).symm

/-- Empty slots from a slot at or after the first slot of an epoch keep its fixed root.

If they start at that first slot, the header after the first of them must have that root. -/
theorem EpochRootFixed.of_advanceSlots
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} {root : Root} :
    ∀ (count : ℕ) {state after : BeaconState preset fork}, EpochRootFixed epoch root state →
      advanceSlots config checks count state = .ok after →
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat →
      (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat = state.slot.toNat →
        ∀ next, advanceSlot config checks state = .ok next →
          SszType.hashTreeRoot next.latestBlockHeader = .ok root) →
      EpochRootFixed epoch root after
  | 0, _, _, holds, computed, _, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds
  | count + 1, state, _, holds, computed, started, first => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, stepped, rest⟩ := computed
    have slot := (advanceSlot_cachedRoots stepped).choose_spec.2.2.2.2.2.2
    apply EpochRootFixed.of_advanceSlots window count
      (holds.of_advanceSlot window stepped fun same => first same next stepped) rest (by omega)
    intro same
    omega

/-- Slots processed from a slot at or after the first slot of an epoch keep its fixed root. -/
theorem EpochRootFixed.of_processSlots
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} {root : Root} {state after : BeaconState preset fork} {slot : Slot}
    (holds : EpochRootFixed epoch root state)
    (computed : processSlots config checks state slot = .ok after)
    (started : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat)
    (first : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat = state.slot.toNat →
      ∀ next, advanceSlot config checks state = .ok next →
        SszType.hashTreeRoot next.latestBlockHeader = .ok root) :
    EpochRootFixed epoch root after := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advanced⟩ := computed
  exact EpochRootFixed.of_advanceSlots window _ holds advanced started first

/-- A block keeps the justified checkpoints, the slot and the roots, so the fixed root too. -/
theorem EpochRootFixed.of_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {epoch : Epoch} {root : Root}
    {state after : BeaconState preset fork} (holds : EpochRootFixed epoch root state)
    (computed : processBlock config checks engine state block = .ok after) :
    EpochRootFixed epoch root after := by
  have frame := frame_processBlock computed
  have roots := processBlock_blockRoots computed
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.currentJustified]
    exact holds.1
  · rw [frame.previousJustified]
    exact holds.2.1
  · intro read rootOk
    apply holds.2.2 read
    obtain ⟨start, startOk, atSlot⟩ := getBlockRoot_ok_iff.mp rootOk
    rw [getBlockRootAtSlot_ok_iff, roots, frame.slot] at atSlot
    exact getBlockRoot_ok_iff.mpr ⟨start, startOk, getBlockRootAtSlot_ok_iff.mpr atSlot⟩

/-- A justification step on a state with a fixed root justifies the epoch only at that root. -/
theorem EpochRootFixed.of_processJustificationAndFinalization {epoch : Epoch} {root : Root}
    {state after : BeaconState preset fork} (holds : EpochRootFixed epoch root state)
    (computed : processJustificationAndFinalization state = .ok after) :
    (after.currentJustifiedCheckpoint.epoch = epoch →
        after.currentJustifiedCheckpoint.root = root) ∧
      (after.previousJustifiedCheckpoint.epoch = epoch →
        after.previousJustifiedCheckpoint.root = root) := by
  constructor
  · intro same
    rcases processJustificationAndFinalization_currentJustified computed with kept | ⟨-, rootOk⟩
    · rw [kept] at same ⊢
      exact holds.1 same
    · rw [same] at rootOk
      exact holds.2.2 _ rootOk
  · rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
    · exact holds.2.1
    · rw [(weighJustificationAndFinalization_checkpoints weighed).1]
      exact holds.1

/-- A new store checks that the anchor block commits to the root of the anchor state. -/
private theorem anchor_stateRoot {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor) :
    SszType.hashTreeRoot anchorState = .ok anchorBlock.stateRoot := by
  unfold getForkchoiceStore at anchored
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at anchored
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at anchored
    split at anchored
    · simp [throw, throwThe, MonadExceptOf.throw] at anchored
    · rename_i same
      rw [not_not] at same
      rw [same]

/-- A successful epoch-start test identifies the rounded boundary with the slot. -/
private theorem anchor_boundary {slot : Slot}
    (atStart : isStartSlotAtEpoch preset slot = .ok true) :
    (computeEpochAtSlot preset slot).toNat * preset.SLOTS_PER_EPOCH.toNat = slot.toNat := by
  have boundary := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
  unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at atStart
  rw [boundary] at atStart
  simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, decide_eq_true_eq] at atStart
  have h := (computeStartSlotAtEpoch_ok_iff.mp boundary).2
  have le : (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat ≤ slot.toNat := by
    rw [h, computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  have zero := congrArg UInt64.toNat atStart
  simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
  have upper := slot.toNat_lt
  have lower := (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
  rw [← h]
  omega

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

omit [DecidablePred (· ∈ J)] in
/-- Each held state records the anchor root for the anchor epoch and justifies it only there.

The anchor block is at the start of a later epoch than the first one.

The anchor state then neither justifies its own epoch nor reads its root.

The first block after the anchor checks that its parent root is the root of the header after the
anchor slot.

The store found the anchor state under that parent root, so it is the root of the anchor block.

The anchor state root must be nonzero, so that the anchor slot fills the header only once. -/
theorem Execution.epochRootFixed_of_blockState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (later : 0 < (getCurrentEpoch anchorState).toNat)
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    {anchorRoot : Root} (rooted : SszType.hashTreeRoot anchorBlock = .ok anchorRoot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ} {root : Root}
    {state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state) :
    EpochRootFixed (getCurrentEpoch anchorState) anchorRoot state := by
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  -- The anchor slot is the first slot of the anchor epoch.
  have boundary : (getCurrentEpoch anchorState).toNat * preset.SLOTS_PER_EPOCH.toNat =
      anchorState.slot.toNat := by
    have := anchor_boundary anchorAtBoundary
    rw [anchorSlot] at this
    exact this
  have base : ∀ fixed, EpochRootFixed (getCurrentEpoch anchorState) fixed anchorState := by
    intro fixed
    have settled := UInt64.le_iff_toNat_le.mp sound.settled
    have ordered := UInt64.le_iff_toNat_le.mp sound.ordered.2
    have previous := getPreviousEpoch_toNat anchorState
    refine ⟨fun same => ?_, fun same => ?_, fun read rootOk => ?_⟩
    · rw [same] at settled
      omega
    · rw [same] at ordered
      omega
    · have := getBlockRoot_start_lt rootOk
      omega
  obtain ⟨block, found⟩ := (reachable k).known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, initial, -⟩ := (reachable k).blockStatesFromParents found
    have equal : post = state := Option.some.inj (postOk.symm.trans stored)
    rw [← equal, initial same]
    exact base anchorRoot
  obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
    e.exists_transition_of_nonanchor_block anchored honest start found stored same
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transitioned
  apply EpochRootFixed.of_processBlock (engine := sources.engine) (block := signed.message) ?_
    blockOk
  obtain ⟨parentBlock, parentKnown⟩ := (reachable k).known_of_blockState parentFound
  by_cases first : parentBlock = anchorBlock
  · -- The first block after the anchor fixes the root through its parent check.
    obtain ⟨post, postOk, initial, -⟩ := (reachable k).blockStatesFromParents parentKnown
    have equal : post = parent := Option.some.inj (postOk.symm.trans parentFound)
    rw [initial first] at equal
    subst parent
    have keyed := (reachable k).root parentKnown
    rw [first, rooted] at keyed
    have parentRoot := processBlock_parentRoot blockOk
    rw [message, ← Except.ok.inj keyed] at parentRoot
    apply EpochRootFixed.of_processSlots window (base anchorRoot) slotsOk boundary.le
    intro _ next stepped
    have hashed := anchor_stateRoot anchored
    -- The header after the anchor slot has a nonzero state root, and empty slots keep it.
    have filled : next.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 := by
      obtain ⟨cached, cachedOk, -, -, header, -, -, -⟩ := advanceSlot_cachedRoots stepped
      rw [header]
      by_cases zero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0
      · rw [processSlot_latestBlockHeader_of_zero zero hashed cachedOk]
        exact nonzero
      · rw [processSlot_latestBlockHeader_of_nonzero zero cachedOk]
        exact zero
    have ahead := (processSlots_slot slotsOk).1
    have run := slotsOk
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
    obtain ⟨_, -, advancedRun⟩ := run
    obtain ⟨count, counted⟩ : ∃ count,
        signed.message.slot.toNat - anchorState.slot.toNat = count + 1 :=
      ⟨signed.message.slot.toNat - anchorState.slot.toNat - 1, by
        have := UInt64.lt_iff_toNat_lt.mp ahead
        omega⟩
    rw [counted] at advancedRun
    simp only [advanceSlots, bind_ok_iff] at advancedRun
    obtain ⟨next', stepped', rest⟩ := advancedRun
    rw [stepped, Except.ok.injEq] at stepped'
    subst next'
    rw [← advanceSlots_latestBlockHeader_of_nonzero filled rest]
    exact parentRoot
  · -- A later parent is past the anchor slot, so its slots never reach the anchor slot again.
    have parentFixed := Execution.epochRootFixed_of_blockState anchored sound window anchorSlot
      anchorAtBoundary later nonzero rooted honest start parentFound
    obtain ⟨grand, grandSigned, grandMessage, grandFound, grandTransitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start parentKnown parentFound first
    have grandLe := UInt64.le_iff_toNat_le.mp ((reachable k).anchorSlot_le_blockState grandFound)
    have parentSlots := stateTransition_slot grandTransitioned
    have parentLt := UInt64.lt_iff_toNat_lt.mp parentSlots.1
    have parentEq := congrArg UInt64.toNat parentSlots.2
    apply EpochRootFixed.of_processSlots window parentFixed slotsOk (by omega)
    intro atStart
    omega
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- Before the next fork, the blocks of honest stores up to a last time are before its activation.

The epoch of each store is at most the horizon, and the next fork activates after the horizon. -/
theorem Execution.heldBlocks_before_nextFork {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) {horizon : Epoch} {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (activation : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  sorry

/-- Honest stores agree on finalized prefixes up to the horizon, or two held states show a fault.

The history to the anchor has enough stake for the count of each epoch, as `EnoughStake` asks.

After the anchor, the bound `large` on counting states gives the same for the runs of the stores.

A finalized checkpoint of a store that is the anchor's own is on every chain of the stores. -/
theorem Execution.finalizedPrefix_or_fault {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {g : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (history : Run config checks g ⟨fork, anchorState⟩) {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (historyEnough : EnoughStake history)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state)) :
    FinalizedPrefix e horizon limit ∨ e.AccountableFault history horizon limit ∨
      e.HashFault history limit := by
  sorry

/-- Honest stores hold one justified checkpoint per epoch up to the horizon, or show a fault. -/
theorem Execution.oneJustifiedPerEpoch_or_fault {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {g : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (history : Run config checks g ⟨fork, anchorState⟩) {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (historyEnough : EnoughStake history)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state)) :
    OneJustifiedPerEpoch e horizon limit ∨ e.AccountableFault history horizon limit ∨
      e.HashFault history limit := by
  sorry

/-- Honest stores agree on the block at each shared root, or two held states show a hash fault.

This needs the block hash inputs of `DirectSafety`, which are not yet in `HashObject`. -/
theorem Execution.oneBlockPerRoot_or_fault {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS)
    {g : ForkedBeaconState preset} (history : Run config checks g ⟨fork, anchorState⟩)
    {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon) :
    OneBlockPerRoot e limit ∨ e.HashFault history limit := by
  sorry

/-- Each block of an honest store has a nonzero state root, or a held state shows a hash fault.

A zero state root of a held block is the root of a state among the hash inputs. -/
theorem Execution.nonzero_or_fault {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS)
    {g : ForkedBeaconState preset} (history : Run config checks g ⟨fork, anchorState⟩)
    {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon) :
    (∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0) ∨ e.HashFault history limit := by
  sorry

/-- Theorem 1, accountable safety: the stored block is safe, or two honest stores show a fault.

This is `Execution.safeAt_confirmedRoot` without its hypotheses on agreement of honest stores.

It does not assume that honest stores agree on finalized prefixes, on one justified checkpoint
per epoch or on one block per root, or that held blocks have nonzero state roots.

Instead the anchor state has an actual run from a genesis state, with enough stake for the count
of each epoch.

The next fork activates after the horizon, so the stores stay at one fork.

Then the stored block is safe from the start of the next slot to the last time.

Or validators with enough stake signed slashable votes, up to the drift of effective balances.

Or two runs to held states show a concrete hash fault.

The hypothesis `anchorParent` stays: it is a condition on checkpoint sync, not on hashes. -/
theorem Execution.safeAt_confirmedRoot_accountable {Δ : ℕ} (sync : e.Synchronous Δ)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {limit : ℕ} (votes : Votes e.startTime limit e)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e limit)
    (committees : CommitteesFollow e limit) (follows : HeadFollowsSupport e limit)
    (admitted : BlocksAdmitted e 0 Δ limit)
    (included : TargetIncluded e limit)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    (_syncStart : (getCurrentEpoch anchorState).toNat = 0 ∨
      anchor.genesisTimeMs.toNat + ((getCurrentEpoch anchorState).toNat +
        preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat *
          config.SLOT_DURATION_MS.toNat ≤ e.startTime)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    (parameters : DirectSafety.Parameters preset)
    {g : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (history : Run config checks g ⟨fork, anchorState⟩)
    (historyEnough : EnoughStake history)
    {threshold margin : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      stake (fun v => balanceAt state v.toNat) (activeVoters state) ≤ stakeCapGwei)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (headDrifts : ∀ w ∈ J, ∀ n head headState epoch, (e.world n).time ≤ limit →
      ((e.world n).state w).getPulledUpHeadState config head = .ok headState →
      ((e.world n).state w).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ v ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
        ((e.world k).state v).Counts config state →
        epoch.toNat ≤ (getCurrentEpoch state).toNat →
        (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 →
        DriftAtMost headState state margin)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
      ((e.world n).view u) ((e.world n).state u))
    (lower : ∀ n ∈ events, ((e.world n).state u).ParentsBelow)
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {last : FastConfirmationStore}
    (ran : (events.map fun n => (e.world n).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) =
        .ok last)
    {shift : ℕ}
    (bounds : RuleBounds e u events (getFastConfirmationStore anchor) margin shift limit)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastCall : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (nonempty : following.toNat ≤ limit) :
    (∀ time, following.toNat ≤ time → time ≤ limit → SafeAt e time last.confirmedRoot) ∨
      e.AccountableFault history horizon limit ∨ e.HashFault history limit := by
  -- Each derived fact holds, or its bridge returns a fault.
  rcases e.finalizedPrefix_or_fault anchored sound start anchorSlot anchorAtBoundary slots
      parameters genesis history forkWindow inHorizon historyEnough large with
    chain | fault | fault
  rotate_left
  · exact .inr (.inl fault)
  · exact .inr (.inr fault)
  rcases e.oneJustifiedPerEpoch_or_fault anchored sound start anchorSlot anchorAtBoundary slots
      parameters genesis history forkWindow inHorizon historyEnough large with
    unique | fault | fault
  rotate_left
  · exact .inr (.inl fault)
  · exact .inr (.inr fault)
  rcases e.oneBlockPerRoot_or_fault anchored start anchorSlot slots history forkWindow
      inHorizon with oneBlock | fault
  rotate_left
  · exact .inr (.inr fault)
  rcases e.nonzero_or_fault anchored start anchorSlot slots history forkWindow inHorizon with
    nonzero | fault
  rotate_left
  · exact .inr (.inr fault)
  exact .inl (e.safeAt_confirmedRoot sync half slots long window lookahead votes fits prompt
    committees follows forkWindow.1 oneBlock admitted included anchored sound anchorSlot
    anchorAtBoundary start noVotes _syncStart maxAligned increment chain unique byzantine
    unslashed supply positive enough large nonzero headDrifts caller upToDate lower atSlots ran
    bounds inHorizon anchorParent lastCall slotOk nextOk followingOk nonempty)

end EthLib.Consensus.Models.Network
