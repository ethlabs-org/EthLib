module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety
public import EthLib.Consensus.Proofs.ForkChoice.AccountableCheckpoints
public import EthLib.Consensus.Proofs.DirectSafety.TerminalSafety
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationExitReserve
import EthLib.Consensus.Proofs.ForkChoice.HonestHeads
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

The hash inputs are those of the two runs, of the two views, and the anchor block and its header.

The anchor block is in no run, as the runs start at the anchor state. -/
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
      va.hashObjects ++ vb.hashObjects ++ (blockHeader anchorBlock).toList.map HashObject.header ++
      [HashObject.block fork anchorBlock])

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

/-- The stake that leaves the active set within two epochs of a reachable state fits its reserve.

The state is reached from genesis, and a later state is reached from it within two epochs.

Each validator active in the first state and not in the later one exits in between.

Its exit was scheduled before the first state, or charged during the epoch of the first state.

The first kind is the scheduled term of `exitReserve`; the queues bound the second kind.

The seed lookahead puts the earliest exit of a new charge two epochs after its epoch. -/
theorem exitStake_le_exitReserve {g y : ForkedBeaconState preset}
    {source : BeaconState preset fork}
    (genesis : Genesis (config := config) (checks := checks) g)
    (shared : Run config checks g ⟨fork, source⟩)
    (tail : Run config checks ⟨fork, source⟩ y)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (preGloas : y.fork < .glamsterdam)
    (near : (getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch source).toNat + 2) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | v ∉ activeVoters y.state} ≤
      exitReserve config source := by
  have bound := ExitChurn.departing_stake_le genesis shared tail lookahead preGloas near
  unfold ExitChurn.activeSet ExitChurn.scheduled at bound
  unfold exitReserve activeVoters
  exact bound

/-- The stake that is inactive at a queried epoch of a later state fits the reserve of the source.

The epoch is no earlier than the epoch of the later state, and within two epochs of the source.

The later state need not be at that epoch: its registry at the epoch is read as it is. -/
theorem exitStake_le_exitReserve_epoch {g y : ForkedBeaconState preset}
    {source : BeaconState preset fork}
    (genesis : Genesis (config := config) (checks := checks) g)
    (shared : Run config checks g ⟨fork, source⟩)
    (tail : Run config checks ⟨fork, source⟩ y)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (preGloas : y.fork < .glamsterdam) {epoch : Epoch}
    (later : getCurrentEpoch y.state ≤ epoch)
    (near : epoch.toNat ≤ (getCurrentEpoch source).toNat + 2) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | isActiveAt y.state epoch v.toNat = false} ≤
      exitReserve config source := by
  have bound := ExitChurn.departing_stake_le_epoch genesis shared tail lookahead preGloas later
    near
  unfold ExitChurn.activeSet ExitChurn.scheduled at bound
  unfold exitReserve activeVoters
  exact bound

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

omit [DecidablePred (· ∈ J)] in
/-- Before the next fork, the blocks of honest stores up to a last time are before its activation.

The epoch of each store is at most the horizon, and the next fork activates after the horizon. -/
theorem Execution.heldBlocks_before_nextFork {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (epochSlots : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {horizon : Epoch} {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (activation : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  have forward := e.forwardReachable
    (fun v hv => (start v hv) ▸ Store.ForwardReachable.anchor anchored) k w honest
  obtain ⟨current, currentOk, blocks, -⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk]
  have epochLe := UInt64.le_iff_toNat_le.mp (inHorizon w honest k _ bounded epochOk)
  intro root block found next member
  have blockLe := UInt64.le_iff_toNat_le.mp (blocks root block found)
  have epochLt := lt_of_le_of_lt epochLe (activation next member)
  rw [computeEpochAtSlot, UInt64.toNat_div] at epochLt
  exact lt_of_le_of_lt blockLe ((Nat.div_lt_iff_lt_mul epochSlots).mp epochLt)

private theorem active_weight_eq_stake {state : BeaconState preset fork}
    (early : fork < .glamsterdam) (unique : uniqueKeys state) :
    Quorum.weight (effectiveWeight state) (activeKeys state) =
      stake (fun v => balanceAt state v.toNat) (activeVoters state) := by
  apply keys_weight state _ unique
  intro i member
  obtain ⟨v, found, -⟩ := (mem_getActiveValidatorIndices (state.validators.bound early)).mp member
  exact (Array.getElem?_eq_some_iff.mp found).1

private theorem enough_append {g x a : ForkedBeaconState preset}
    {pre : Run config checks g x} {tail : Run config checks x a}
    (one : EnoughStake pre) (two : EnoughStake tail) : EnoughStake (pre.append tail) := by
  intro call
  rcases (pre.contains_append tail (.slot call.advanced)).mp call.member with member | member
  · exact one { call with member := member }
  · exact two { call with member := member }

private theorem enough_slot {state after : BeaconState preset fork}
    (early : fork < .glamsterdam) (unique : uniqueKeys state)
    (advanced : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, after⟩)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state)) :
    EnoughStake (Run.nil.snoc (.slot advanced)) := by
  intro call
  rcases call with ⟨before, after, advanced, member, boundary, cached, weighed,
    cachedOk, weighedOk, later⟩
  cases member with
  | earlier member => cases member
  | last =>
    have balances := processSlot_countingBalances cachedOk
    have same := (processSlot_ok cachedOk).choose_spec.choose_spec.choose_spec.choose_spec
    have cachedUnique : uniqueKeys cached := by
      rw [same]
      exact unique
    rw [active_weight_eq_stake early cachedUnique, balances.2.2.2.2.1]
    simpa only [balances.2.2.2.2.2.2] using large

private theorem headers_append {g a b : ForkedBeaconState preset}
    (pre : Run config checks g a) (tail : Run config checks a b) :
    (pre.append tail).headers = pre.headers ++ tail.headers := by
  induction tail with
  | nil => simp [Run.append, Run.headers]
  | snoc tail step ih => simp only [Run.append, Run.headers, ih, List.append_assoc]

private theorem run_enough_of_advanceSlots (count : ℕ)
    {state after : BeaconState preset fork}
    (early : fork < .glamsterdam) (unique : uniqueKeys state)
    (advanced : advanceSlots config checks count state = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      after.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (large : ∀ i current, i < count →
      advanceSlots config checks i state = .ok current →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt current v.toNat) (activeVoters current)) :
    ∃ run : Run config checks ⟨fork, state⟩ ⟨fork, after⟩,
      EnoughStake run ∧ run.headers = [] := by
  induction count generalizing state with
  | zero =>
    cases advanced
    refine ⟨.nil, ?_, rfl⟩
    rintro ⟨_, _, _, member, _⟩
    cases member
  | succ count ih =>
    obtain ⟨next, stepped, rest⟩ := bind_ok_iff.mp advanced
    have slotsEq := advanceSlots_slot count rest
    have nextSlot := advanceSlot_slot stepped
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, next⟩ := by
      rw [advanceSlotAcross_of_before (fun nextFork scheduled => by
        have := before nextFork scheduled
        omega), stepped]
      rfl
    obtain ⟨tail, enough, empty⟩ := ih ((Run.nil.snoc (.slot across)).unique unique) rest
      (fun i current small run => large (i + 1) current (by omega)
        (by simp only [advanceSlots, stepped, bind, Except.bind]; exact run))
    refine ⟨(Run.nil.snoc (.slot across)).append tail,
      enough_append (enough_slot early unique across (large 0 state (by omega) rfl)) enough, ?_⟩
    simp [headers_append, Run.headers, Step.headers, empty]

private theorem counts_epoch_le_current {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    {state : BeaconState preset fork} (counts : store.Counts config state) :
    ∃ epoch, store.getCurrentStoreEpoch config = .ok epoch ∧ getCurrentEpoch state ≤ epoch := by
  obtain ⟨current, currentOk, blocks, states⟩ :=
    forward.slots_le_current slots (by rw [anchorSlot]; exact UInt64.le_refl _)
  have bound : state.slot ≤ current := by
    obtain ⟨root, base, held, rfl | ⟨checks, slot, childRoot, child, found, _, low, advanced⟩⟩ :=
      counts
    · exact states root state held
    · rw [(processSlots_slot advanced).2]
      exact UInt64.le_trans low (blocks childRoot child found)
  refine ⟨computeEpochAtSlot preset current, ?_, ?_⟩
  · simp only [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  · simp only [UInt64.le_iff_toNat_le, getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp bound)

omit [DecidablePred (· ∈ J)] in
private theorem run_enough_of_blockState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (unique : uniqueKeys anchorState) (early : fork < .glamsterdam)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (large : ∀ state, ((e.world k).state w).Counts config state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    {root : Root} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state) :
    ∃ run : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩, EnoughStake run ∧
      ∀ epoch boundary, computeStartSlotAtEpoch preset epoch = .ok boundary →
        anchorBlock.slot ≤ boundary →
        ((e.world k).state w).getCheckpointBlock root epoch =
          ((run.checkpointPath epoch).getLast?.map SszType.hashTreeRoot |>.getD
            (SszType.hashTreeRoot anchorBlock)).mapError ForkChoiceError.ssz := by
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
  obtain ⟨block, found⟩ := (reachable k).known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, initial, -⟩ := (reachable k).blockStatesFromParents found
    have equal : post = state := Option.some.inj (postOk.symm.trans stored)
    rw [← equal, initial same]
    refine ⟨.nil, ?_, ?_⟩
    · rintro ⟨_, _, _, member, _⟩
      cases member
    · intro epoch boundary boundaryOk above
      have hashed := same ▸ (reachable k).root found
      simp [Run.checkpointPath, Run.headers, Store.getCheckpointBlock, boundaryOk,
        Store.getAncestor_of_le (node := ⟨root, .pending⟩) found (same ▸ above),
        hashed, Except.mapError, bind, Except.bind, pure, Except.pure]
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored same
    obtain ⟨pre, preEnough, preReads⟩ :=
      run_enough_of_blockState anchored unique early anchorSlot honest start before large
        parentFound
    have across : stateTransitionAcross config checks sources.engine ⟨fork, parent⟩ signed true =
        .ok state := by
      rw [stateTransitionAcross_of_before (by simpa only [message] using before root block found)]
      exact transitioned
    obtain ⟨advanced, slotRun, due, applied, slotsAcross, -, -⟩ :=
      Run.stateTransition sources.engine signed across
    have slotsOk : processSlots config checks parent signed.message.slot = .ok advanced := by
      rw [processSlotsAcross_of_before (by simpa only [message] using before root block found)]
        at slotsAcross
      cases computed : processSlots config checks parent signed.message.slot with
      | error err => simp [computed, Except.map] at slotsAcross
      | ok result =>
        simp only [computed, Except.map, Except.ok.injEq, ForkedBeaconState.mk.injEq,
          true_and, heq_eq_eq] at slotsAcross
        exact slotsAcross ▸ rfl
    have lastSlot := (processSlots_slot slotsOk).2
    have slotRuns := slotsOk
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotRuns
    obtain ⟨_, _, advancedSlots⟩ := slotRuns
    obtain ⟨tail, tailEnough, tailEmpty⟩ := run_enough_of_advanceSlots _ early (pre.unique unique)
      advancedSlots (by simpa only [lastSlot, message] using before root block found) (by
        intro i current small reached
        apply large current
        refine ⟨block.parentRoot, parent, parentFound, ?_⟩
        by_cases zero : i = 0
        · subst i
          cases reached
          exact .inl rfl
        · right
          have atSlot := advanceSlots_slot i reached
          dsimp only at atSlot small reached
          refine ⟨checks, current.slot, root, block, found, rfl, ?_, ?_⟩
          · rw [UInt64.le_iff_toNat_le, ← message]
            omega
          · simp only [processSlots, bind_ok_iff, ensure_ok_iff]
            refine ⟨(), UInt64.lt_iff_toNat_lt.mpr (by omega), ?_⟩
            have count : current.slot.toNat - parent.slot.toNat = i := by omega
            rw [count]
            exact reached)
    refine ⟨pre.append (tail.snoc (.block sources.engine signed due applied)), ?_, ?_⟩
    · apply enough_append preEnough
      intro call
      rcases call with ⟨before, after, advanced, member, boundary, cached, weighed,
        cachedOk, weighedOk, later⟩
      cases member with
      | earlier member =>
        exact tailEnough ⟨before, after, advanced, member, boundary, cached, weighed,
          cachedOk, weighedOk, later⟩
    · intro epoch boundary boundaryOk above
      obtain ⟨_, _, bodyRoot, bodyOk, _⟩ := (reachable k).blockState_header found stored same
      let header : BeaconBlockHeader :=
        ⟨block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, bodyRoot⟩
      have selected : blockHeader signed.message = some header := by
        simp [blockHeader, message, bodyOk, Except.toOption, header]
      have hashed : SszType.hashTreeRoot header = .ok root :=
        (BeaconBlock.hashTreeRoot_header bodyOk).trans ((reachable k).root found)
      have bound := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      by_cases below : block.slot ≤ boundary
      · have keep : header.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
          change block.slot.toNat ≤ _
          rw [← bound]
          exact UInt64.le_iff_toNat_le.mp below
        simp [Run.checkpointPath, headers_append, Run.headers, Step.headers, tailEmpty,
          selected, keep, Store.getCheckpointBlock, boundaryOk,
          Store.getAncestor_of_le (node := ⟨root, .pending⟩) found below,
          hashed, Except.mapError, bind, Except.bind, pure, Except.pure]
      · have skip : ¬header.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
          change ¬block.slot.toNat ≤ _
          rw [← bound, ← UInt64.le_iff_toNat_le]
          exact below
        obtain ⟨parentBlock, parentKnown⟩ := (reachable k).known_of_blockState parentFound
        have parentLe := (reachable k).blockState_slot_le (UInt64.le_of_eq anchorSlot)
          parentKnown parentFound
        have parentLt : parent.slot < block.slot := by
          simpa only [message] using (stateTransition_slot transitioned).1
        have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) early found below
          parentKnown (UInt64.lt_of_le_of_lt parentLe parentLt)
        simpa [Run.checkpointPath, headers_append, Run.headers, Step.headers, tailEmpty,
          selected, skip, Store.getCheckpointBlock, boundaryOk, step, Except.mapError,
          bind, Except.bind, pure, Except.pure]
          using preReads epoch boundary boundaryOk above
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

omit [DecidablePred (· ∈ J)] in
private theorem held_run_enough {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {g : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (history : Run config checks g ⟨fork, anchorState⟩) {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat) {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (historyEnough : EnoughStake history)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {root : Root} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state) :
    ∃ run : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
      EnoughStake (history.append run) ∧ (∀ view : TerminalView ⟨fork, state⟩, view.enough) ∧
      ∀ epoch boundary, computeStartSlotAtEpoch preset epoch = .ok boundary →
        anchorBlock.slot ≤ boundary →
        ((e.world k).state w).getCheckpointBlock root epoch =
          ((run.checkpointPath epoch).getLast?.map SszType.hashTreeRoot |>.getD
            (SszType.hashTreeRoot anchorBlock)).mapError ForkChoiceError.ssz := by
  have forward := e.forwardReachable (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun v member => by rw [start v member]; exact .anchor anchored) k w honest
  have countLarge (state : BeaconState preset fork)
      (counts : ((e.world k).state w).Counts config state) :
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state) := by
    obtain ⟨epoch, epochOk, bound⟩ := counts_epoch_le_current forward slots anchorSlot counts
    have high := UInt64.le_iff_toNat_le.mp (inHorizon w honest k epoch bounded epochOk)
    have low := UInt64.le_iff_toNat_le.mp bound
    exact large w honest k state bounded counts (by omega)
  obtain ⟨run, enough, reads⟩ := run_enough_of_blockState anchored
    (history.unique (genesis_unique genesis)) forkWindow.1 anchorSlot honest (start w honest)
    (by
      obtain ⟨current, currentOk, blocks, -⟩ := forward.slots_le_current slots
        (by rw [anchorSlot]; exact UInt64.le_refl _)
      have currentEpoch : ((e.world k).state w).getCurrentStoreEpoch config =
          .ok (computeEpochAtSlot preset current) := by
        simp only [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
      have high := UInt64.le_iff_toNat_le.mp
        (inHorizon w honest k _ bounded currentEpoch)
      simp only [computeEpochAtSlot, UInt64.toNat_div] at high
      intro root block found next scheduled
      have blockLe := UInt64.le_iff_toNat_le.mp (blocks root block found)
      have nextLt := forkWindow.2 next scheduled
      have positive := parameters.slots
      have currentLt : current.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
        (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
      omega) countLarge stored
  refine ⟨run, enough_append historyEnough enough, ?_, reads⟩
  intro view
  cases view with
  | realized => trivial
  | pulled after computed =>
    intro _
    rw [active_weight_eq_stake forkWindow.1 ((history.append run).unique (genesis_unique genesis))]
    exact countLarge state ⟨root, state, stored, .inl rfl⟩

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
    {time : ℕ} {view : Set (Message preset fork)}
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
        h.2.of_maps (Store.onAttesterSlashing_frame slashed).2.2
          (Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1⟩)
      ⟨reachable, holds⟩ added).2
  | attestation _ attested => exact CheckpointStatesChecked.attestation holds attested
  | attesterSlashing _ slashed =>
    exact holds.of_maps (Store.onAttesterSlashing_frame slashed).2.2
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

omit [DecidablePred (· ∈ J)] in
/-- The state of a checkpoint of an honest store comes from the state of its block.

It is that state when that state is at the start of the epoch or later.

Otherwise it is that state with its slots processed to the start of the epoch.

The slots are processed with the checks of the execution. -/
theorem Execution.checkpointState_fromBlock {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
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

/-- A run of empty slots, when all of them stay before the next fork. -/
private theorem run_of_advanceSlots (count : ℕ) {state after : BeaconState preset fork}
    (advanced : advanceSlots config checks count state = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      after.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, state⟩ ⟨fork, after⟩) := by
  induction count generalizing state with
  | zero =>
    cases advanced
    exact ⟨.nil⟩
  | succ count ih =>
    obtain ⟨next, stepped, rest⟩ := bind_ok_iff.mp advanced
    have slotsEq := advanceSlots_slot count rest
    have nextSlot := advanceSlot_slot stepped
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, next⟩ := by
      rw [advanceSlotAcross_of_before (fun nextFork scheduled => by
        have := before nextFork scheduled
        omega), stepped]
      rfl
    obtain ⟨tail⟩ := ih rest
    exact ⟨(Run.nil.snoc (.slot across)).append tail⟩

/-- A run from a state to the state at a later slot, when the slot stays before the next fork. -/
private theorem run_of_processSlots {state after : BeaconState preset fork} {slot : Slot}
    (processed : processSlots config checks state slot = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, state⟩ ⟨fork, after⟩) := by
  have lastSlot := (processSlots_slot processed).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
  obtain ⟨_, _, advanced⟩ := processed
  exact run_of_advanceSlots _ advanced (by simpa only [lastSlot] using before)

omit [DecidablePred (· ∈ J)] in
/-- A run from a state at a boundary slot along a chain of blocks above it to a later block state.

The start is the state of an ancestor block, kept as it is or processed to the boundary.

No block of the chain lies from the ancestor to the boundary except the ancestor itself. -/
private theorem run_along_chain {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {a : Root} {aBlock : BeaconBlock preset fork} {sa s0 : BeaconState preset fork}
    {boundary : Slot}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa)
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0)) :
    ∀ (n : ℕ) (b : Root) (block : BeaconBlock preset fork) (sb : BeaconState preset fork),
      block.slot.toNat = n →
      ((e.world k).state w).blocks[b]? = some block →
      ((e.world k).state w).blockStates[b]? = some sb →
      ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true →
      (∀ (q : Root) (qBlock : BeaconBlock preset fork),
        ((e.world k).state w).blocks[q]? = some qBlock →
        ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨q, .pending⟩ = .ok true →
        aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a) →
      boundary < block.slot →
      Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, sb⟩) := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
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
    exact all k
  have aLe : aBlock.slot ≤ boundary := by
    have h2 := reachable.blockState_slot_le (UInt64.le_of_eq anchorSlot) aFound storedA
    rcases bridge with ⟨h, _⟩ | ⟨h, _⟩
    · exact UInt64.le_trans h2 (UInt64.le_of_eq h)
    · exact UInt64.le_trans h2 (UInt64.le_of_lt h)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b block sb hn found stored descends clear far
    have aLt : aBlock.slot < block.slot := UInt64.lt_of_le_of_lt aLe far
    have other : block ≠ anchorBlock := by
      intro same
      have h1 := reachable.anchorSlot_le_block aFound
      rw [same] at aLt
      exact UInt64.lt_irrefl _ (UInt64.lt_of_le_of_lt h1 aLt)
    obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored other
    obtain ⟨pBlock, pFound⟩ := reachable.known_of_blockState parentFound
    have parentLe := reachable.blockState_slot_le (UInt64.le_of_eq anchorSlot) pFound parentFound
    have parentLt : parent.slot < block.slot := by
      simpa only [message] using (stateTransition_slot transitioned).1
    have pLt : pBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe parentLt
    have viaBefore : ∀ next ∈ config.nextFork fork,
        signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      simpa only [message] using before b block found
    have transitioned' := transitioned
    simp only [stateTransition, bind_ok_iff] at transitioned
    obtain ⟨adv, slotsOk, applied⟩ := transitioned
    by_cases isA : block.parentRoot = a
    · rw [isA, storedA, Option.some.injEq] at parentFound
      subst parentFound
      have viaS0 : processSlots config checks s0 signed.message.slot = .ok adv := by
        rcases bridge with ⟨_, rfl⟩ | ⟨lt, ran⟩
        · exact slotsOk
        · obtain ⟨middle, middleOk, rest⟩ := processSlots_split slotsOk lt
            (by simpa only [message] using far)
          rw [ran, Except.ok.injEq] at middleOk
          subst middleOk
          exact rest
      have across : stateTransitionAcross config checks sources.engine ⟨fork, s0⟩ signed true =
          .ok sb := by
        rw [stateTransitionAcross_of_before viaBefore]
        simp only [stateTransition, bind_ok_iff]
        exact ⟨adv, viaS0, applied⟩
      obtain ⟨advanced, slotRun, due, applied', -, -, -⟩ :=
        Run.stateTransition sources.engine signed across
      exact ⟨slotRun.snoc (.block sources.engine signed due applied')⟩
    · -- The walk from the block to the ancestor passes through the parent.
      have walk := Store.getAncestor_of_isAncestor_of_lt early aFound descends
      have step := Store.getAncestor_step (node := ⟨b, .pending⟩) (slot := aBlock.slot) found
        (UInt64.not_le.mpr aLt) pFound pLt
      rw [Store.parentPayloadStatus_of_lt early] at step
      rw [step] at walk
      have above : aBlock.slot ≤ pBlock.slot := by
        by_contra below
        have le : pBlock.slot ≤ aBlock.slot := UInt64.le_of_lt (UInt64.not_le.mp below)
        rw [Store.getAncestor_of_le (node := ⟨block.parentRoot, .pending⟩) pFound le] at walk
        exact isA (congrArg ForkChoiceNode.root (Except.ok.inj walk))
      have pDescends : ((e.world k).state w).isAncestor ⟨block.parentRoot, .pending⟩
          ⟨a, .pending⟩ = .ok true := by
        simp [Store.isAncestor, Store.block_ok_iff.mpr aFound, walk, bind, Except.bind,
          pure, Except.pure]
      have bToParent : ((e.world k).state w).isAncestor ⟨b, .pending⟩
          ⟨block.parentRoot, .pending⟩ = .ok true :=
        Store.isAncestor_of_parent early found pFound pLt (Store.isAncestor_self pFound)
      have pFar : boundary < pBlock.slot := by
        by_contra notFar
        exact isA (clear _ pBlock pFound bToParent above (UInt64.not_lt.mp notFar))
      have clear' : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
          ((e.world k).state w).blocks[q]? = some qBlock →
          ((e.world k).state w).isAncestor ⟨block.parentRoot, .pending⟩ ⟨q, .pending⟩ =
            .ok true → aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a :=
        fun q qBlock qFound h => clear q qBlock qFound
          (Store.isAncestor_of_parent early found pFound pLt h)
      obtain ⟨run⟩ := ih pBlock.slot.toNat (hn ▸ UInt64.lt_iff_toNat_lt.mp pLt) block.parentRoot
        pBlock parent rfl pFound parentFound pDescends clear' pFar
      have across : stateTransitionAcross config checks sources.engine ⟨fork, parent⟩ signed
          true = .ok sb := by
        rw [stateTransitionAcross_of_before viaBefore]
        exact transitioned'
      obtain ⟨advanced, slotRun, due, applied', -, -, -⟩ :=
        Run.stateTransition sources.engine signed across
      exact ⟨run.append (slotRun.snoc (.block sources.engine signed due applied'))⟩


/-- A checkpoint read leaves no block of the chain from the checkpoint block to the boundary. -/
private theorem clear_of_getCheckpointBlock {store : Store preset fork}
    (early : fork < .glamsterdam) {b a : Root} {aBlock : BeaconBlock preset fork}
    {epoch : Epoch} {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (read : store.getCheckpointBlock b epoch = .ok a)
    (aFound : store.blocks[a]? = some aBlock) :
    ∀ (q : Root) (qBlock : BeaconBlock preset fork), store.blocks[q]? = some qBlock →
      store.isAncestor ⟨b, .pending⟩ ⟨q, .pending⟩ = .ok true →
      aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a := by
  intro q qBlock qFound hq above below
  unfold Store.getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨boundary', boundaryOk', anc, walk, rootEq⟩ := read
  have same : boundary' = boundary := by
    have := mapError_ok_iff.mp boundaryOk'
    rw [boundaryOk] at this
    exact (Except.ok.inj this).symm
  subst same
  have pending := Store.getAncestor_pending_of_lt early rfl walk
  have ancEq : anc = ⟨a, .pending⟩ := by
    cases anc
    simp_all
  subst ancEq
  have toQ := Store.getAncestor_of_isAncestor_of_lt early qFound hq
  have through := Store.getAncestor_trans below walk
  rw [Store.getAncestor_of_le (node := ⟨a, .pending⟩) aFound above] at through
  rw [toQ, Except.ok.injEq] at through
  exact congrArg ForkChoiceNode.root through

/-- From a start state at a boundary, the same slots lead to a later state of the same ancestor. -/
private theorem run_from_bridge {sa s0 y : BeaconState preset fork} {boundary target : Slot}
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0))
    (later : boundary ≤ target)
    (reach : (sa.slot = target ∧ y = sa) ∨
      (sa.slot < target ∧ processSlots config checks sa target = .ok y))
    (before : ∀ next ∈ config.nextFork fork,
      target.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) := by
  rcases bridge with ⟨low, rfl⟩ | ⟨low, ran⟩
  · rcases reach with ⟨same, rfl⟩ | ⟨_, processed⟩
    · exact ⟨.nil⟩
    · exact run_of_processSlots processed before
  · rcases reach with ⟨same, rfl⟩ | ⟨_, processed⟩
    · exact absurd (UInt64.lt_of_lt_of_le low (same ▸ later)) (UInt64.lt_irrefl _)
    · by_cases equal : boundary = target
      · subst equal
        rw [ran, Except.ok.injEq] at processed
        subst processed
        exact ⟨.nil⟩
      · obtain ⟨middle, middleOk, rest⟩ := processSlots_split processed low
          (UInt64.lt_of_le_of_ne later equal)
        rw [ran, Except.ok.injEq] at middleOk
        subst middleOk
        exact run_of_processSlots rest before

omit [DecidablePred (· ∈ J)] in
/-- A block on the chain above an ancestor has a child of the ancestor on its chain.

That child is reached from the state of the ancestor by a successful run of slots. -/
private theorem exists_child_of_chain {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {a : Root} {aBlock : BeaconBlock preset fork} {sa : BeaconState preset fork}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa) :
    ∀ (n : ℕ) (b : Root) (block : BeaconBlock preset fork) (sb : BeaconState preset fork),
      block.slot.toNat = n →
      ((e.world k).state w).blocks[b]? = some block →
      ((e.world k).state w).blockStates[b]? = some sb →
      ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true →
      b ≠ a →
      ∃ (x : Root) (xBlock : BeaconBlock preset fork),
        ((e.world k).state w).blocks[x]? = some xBlock ∧
        ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨x, .pending⟩ = .ok true ∧
        xBlock.parentRoot = a ∧ aBlock.slot < xBlock.slot ∧
        ∃ advanced, processSlots config checks sa xBlock.slot = .ok advanced := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
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
    exact all k
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b block sb hn found stored descends distinct
    have walk := Store.getAncestor_of_isAncestor_of_lt early aFound descends
    have aLt : aBlock.slot < block.slot := by
      by_contra notLt
      rw [Store.getAncestor_of_le (node := ⟨b, .pending⟩) found (UInt64.not_lt.mp notLt)] at walk
      exact distinct (congrArg ForkChoiceNode.root (Except.ok.inj walk))
    have other : block ≠ anchorBlock := by
      intro same
      have h1 := reachable.anchorSlot_le_block aFound
      rw [same] at aLt
      exact UInt64.lt_irrefl _ (UInt64.lt_of_le_of_lt h1 aLt)
    obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored other
    obtain ⟨pBlock, pFound⟩ := reachable.known_of_blockState parentFound
    have parentLe := reachable.blockState_slot_le (UInt64.le_of_eq anchorSlot) pFound parentFound
    have parentLt : parent.slot < block.slot := by
      simpa only [message] using (stateTransition_slot transitioned).1
    have pLt : pBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe parentLt
    by_cases isA : block.parentRoot = a
    · rw [isA, storedA, Option.some.injEq] at parentFound
      subst parentFound
      obtain ⟨adv, slotsOk, _⟩ := bind_ok_iff.mp
        (show (processSlots config checks sa signed.message.slot >>= fun s =>
          applySignedBlock config checks sources.engine s signed true) = .ok sb from transitioned)
      exact ⟨b, block, found, Store.isAncestor_self found, isA, aLt,
        adv, by simpa only [message] using slotsOk⟩
    · have step := Store.getAncestor_step (node := ⟨b, .pending⟩) (slot := aBlock.slot) found
        (UInt64.not_le.mpr aLt) pFound pLt
      rw [Store.parentPayloadStatus_of_lt early] at step
      rw [step] at walk
      have above : aBlock.slot ≤ pBlock.slot := by
        by_contra below
        have le : pBlock.slot ≤ aBlock.slot := UInt64.le_of_lt (UInt64.not_le.mp below)
        rw [Store.getAncestor_of_le (node := ⟨block.parentRoot, .pending⟩) pFound le] at walk
        exact isA (congrArg ForkChoiceNode.root (Except.ok.inj walk))
      have pDescends : ((e.world k).state w).isAncestor ⟨block.parentRoot, .pending⟩
          ⟨a, .pending⟩ = .ok true := by
        simp [Store.isAncestor, Store.block_ok_iff.mpr aFound, walk, bind, Except.bind,
          pure, Except.pure]
      obtain ⟨x, xBlock, xFound, xAbove, xParent, xLt, xSlots⟩ :=
        ih pBlock.slot.toNat (hn ▸ UInt64.lt_iff_toNat_lt.mp pLt) block.parentRoot pBlock parent
          rfl pFound parentFound pDescends isA
      exact ⟨x, xBlock, xFound, Store.isAncestor_of_parent early found pFound pLt xAbove,
        xParent, xLt, xSlots⟩


omit [DecidablePred (· ∈ J)] in
/-- From the state of an ancestor block, a run reaches a head-chain state no later than an epoch.

The head state is no later than the epoch.

The run stops at the head state, or at the state of the ancestor when the head is the ancestor.

Its registry at the epoch is the one of the head state. -/
private theorem run_to_epoch_early {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {a : Root} {aBlock : BeaconBlock preset fork} {sa s0 : BeaconState preset fork}
    {boundary : Slot}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa)
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0))
    {head : Root} {headBlock : BeaconBlock preset fork} {hs : BeaconState preset fork}
    (headFound : ((e.world k).state w).blocks[head]? = some headBlock)
    (stored : ((e.world k).state w).blockStates[head]? = some hs)
    (descends : ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨a, .pending⟩ = .ok true)
    (clearC : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
      ((e.world k).state w).blocks[q]? = some qBlock →
      ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨q, .pending⟩ = .ok true →
      aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a)
    {epoch : Epoch}
    (boundaryEpoch : computeEpochAtSlot preset boundary ≤ epoch)
    (boundaryBefore : ∀ next ∈ config.nextFork fork,
      boundary.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (bounded : epoch.toNat < 2 ^ 64 - 1)
    (recent : epoch.toNat ≤ (getCurrentEpoch hs).toNat + 1)
    (cur : getCurrentEpoch hs ≤ epoch) :
    ∃ y : BeaconState preset fork, Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) ∧
      getCurrentEpoch y ≤ epoch ∧
      ∀ position, isActiveAt y epoch position = isActiveAt hs epoch position := by
  have s0Slot : s0.slot = boundary := by
    rcases bridge with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have aSlot : sa.slot = aBlock.slot := by
    have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
      have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
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
      exact all k
    exact blockState_slot_eq reachable anchorSlot aFound storedA
  by_cases isHeadA : head = a
  · subst isHeadA
    have same : hs = sa := Option.some.inj (stored.symm.trans storedA)
    subst same
    have runSa : Nonempty (Run config checks ⟨fork, hs⟩ ⟨fork, s0⟩) := by
      rcases bridge with ⟨_, rfl⟩ | ⟨_, ran⟩
      · exact ⟨.nil⟩
      · exact run_of_processSlots ran boundaryBefore
    obtain ⟨run⟩ := runSa
    refine ⟨s0, ⟨.nil⟩, ?_, ?_⟩
    · simpa only [getCurrentEpoch, s0Slot] using boundaryEpoch
    · intro position
      exact activeKept_of_chainSteps run.chainSteps epoch
        (ExitChurn.fixed_ge hs recent lookahead bounded) position
  · obtain ⟨hb, hbFound, aLeHead⟩ := Store.slot_le_of_isAncestor aFound descends
    have hbEq : hb = headBlock := Option.some.inj (hbFound.symm.trans headFound)
    subst hbEq
    have far : boundary < hb.slot := by
      by_contra notFar
      exact isHeadA (clearC head hb headFound (Store.isAncestor_self headFound) aLeHead
        (UInt64.not_lt.mp notFar))
    obtain ⟨run⟩ := run_along_chain anchored early anchorSlot honest start before aFound storedA
      bridge hb.slot.toNat head hb hs rfl headFound stored descends clearC far
    exact ⟨hs, ⟨run⟩, cur, fun _ => rfl⟩


omit [DecidablePred (· ∈ J)] in
/-- From the state of an ancestor block, a run reaches the start of an epoch on the head chain.

The head state is later than the epoch.

The registry of the reached state at the epoch is the one of the head state. -/
private theorem run_to_epoch_late {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {a : Root} {aBlock : BeaconBlock preset fork} {sa s0 : BeaconState preset fork}
    {boundary : Slot}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa)
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0))
    {head : Root} {headBlock : BeaconBlock preset fork} {hs : BeaconState preset fork}
    (headFound : ((e.world k).state w).blocks[head]? = some headBlock)
    (stored : ((e.world k).state w).blockStates[head]? = some hs)
    (descends : ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨a, .pending⟩ = .ok true)
    (clearC : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
      ((e.world k).state w).blocks[q]? = some qBlock →
      ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨q, .pending⟩ = .ok true →
      aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a)
    {epoch : Epoch} {S : Slot} (SOk : computeStartSlotAtEpoch preset epoch = .ok S)
    (boundaryLe : boundary ≤ S)
    (beforeS : ∀ next ∈ config.nextFork fork,
      S.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (bounded : epoch.toNat < 2 ^ 64 - 1)
    {bE : Root} (readE : ((e.world k).state w).getCheckpointBlock head epoch = .ok bE)
    (later : epoch < getCurrentEpoch hs) :
    ∃ y : BeaconState preset fork, Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) ∧
      getCurrentEpoch y ≤ epoch ∧
      ∀ position, isActiveAt y epoch position = isActiveAt hs epoch position := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
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
    exact all k
  have positiveNat : 0 < preset.SLOTS_PER_EPOCH.toNat := UInt64.lt_iff_toNat_lt.mp positive
  have headSlot : hs.slot = headBlock.slot :=
    blockState_slot_eq reachable anchorSlot headFound stored
  have aSlot : sa.slot = aBlock.slot := blockState_slot_eq reachable anchorSlot aFound storedA
  have aLe : aBlock.slot ≤ boundary := by
    rw [← aSlot]
    rcases bridge with ⟨h, _⟩ | ⟨h, _⟩
    · exact UInt64.le_of_eq h
    · exact UInt64.le_of_lt h
  have s0Slot : s0.slot = boundary := by
    rcases bridge with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have SEpoch : computeEpochAtSlot preset S = epoch :=
    computeEpochAtSlot_computeStartSlotAtEpoch positive SOk
  have SNat : S.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    (computeStartSlotAtEpoch_ok_iff.mp SOk).2
  have boundaryBefore : ∀ next ∈ config.nextFork fork,
      boundary.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := fun next member =>
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp boundaryLe) (beforeS next member)
  have curHs : (getCurrentEpoch hs).toNat =
      headBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div, headSlot]
  have farS : S.toNat < headBlock.slot.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp later
    rw [curHs] at this
    have step : epoch.toNat + 1 ≤ headBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := this
    have := (Nat.le_div_iff_mul_le positiveNat).mp step
    rw [SNat]
    nlinarith
  obtain ⟨S', bEBlock, SOk', bEFound, bELe, bEDesc⟩ :=
    Store.isAncestor_of_getCheckpointBlock early readE
  have SEq : S' = S := Except.ok.inj (SOk'.symm.trans SOk)
  subst S'
  have clearE := clear_of_getCheckpointBlock early SOk readE bEFound
  obtain ⟨sE, storedE⟩ : ∃ sE, ((e.world k).state w).blockStates[bE]? = some sE := by
    obtain ⟨post, postOk, -⟩ := reachable.blockStatesFromParents bEFound
    exact ⟨post, postOk⟩
  have sESlot : sE.slot = bEBlock.slot := blockState_slot_eq reachable anchorSlot bEFound storedE
  have headNe : head ≠ bE := by
    intro same
    subst same
    have eq : bEBlock = headBlock := Option.some.inj (bEFound.symm.trans headFound)
    subst eq
    exact absurd (UInt64.le_iff_toNat_le.mp bELe) (by omega)
  have farHead : S < headBlock.slot := UInt64.lt_iff_toNat_lt.mpr farS
  -- The state of the checkpoint block at the start of the epoch.
  obtain ⟨y, reach⟩ : ∃ y : BeaconState preset fork,
      (sE.slot = S ∧ y = sE) ∨ (sE.slot < S ∧ processSlots config checks sE S = .ok y) := by
    by_cases atS : sE.slot = S
    · exact ⟨sE, .inl ⟨atS, rfl⟩⟩
    · have below : sE.slot < S := UInt64.lt_of_le_of_ne (sESlot ▸ bELe) atS
      obtain ⟨x, xBlock, xFound, xAbove, xParent, xLt, advanced, xSlots⟩ :=
        exists_child_of_chain anchored early anchorSlot honest start bEFound storedE
          headBlock.slot.toNat head headBlock hs rfl headFound stored bEDesc headNe
      have xFar : S < xBlock.slot := by
        by_contra notFar
        have same := clearE x xBlock xFound xAbove (UInt64.le_of_lt xLt)
          (UInt64.not_lt.mp notFar)
        subst same
        have eq : bEBlock = xBlock := Option.some.inj (bEFound.symm.trans xFound)
        subst eq
        exact UInt64.lt_irrefl _ xLt
      obtain ⟨middle, middleOk, -⟩ := processSlots_split xSlots below xFar
      exact ⟨middle, .inr ⟨below, middleOk⟩⟩
  have ySlot : y.slot = S := by
    rcases reach with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have curY : getCurrentEpoch y = epoch := by
    simp only [getCurrentEpoch, ySlot]
    exact SEpoch
  have walkE : ((e.world k).state w).getAncestor ⟨head, .pending⟩ S = .ok ⟨bE, .pending⟩ := by
    have read := readE
    unfold Store.getCheckpointBlock at read
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
    obtain ⟨boundary', boundaryOk', anc, walk, rootEq⟩ := read
    have same : boundary' = S := by
      have := mapError_ok_iff.mp boundaryOk'
      rw [SOk] at this
      exact (Except.ok.inj this).symm
    subst same
    have pending := Store.getAncestor_pending_of_lt early rfl walk
    have ancEq : anc = ⟨bE, .pending⟩ := by
      cases anc
      simp_all
    rw [← ancEq]
    exact walk
  have runY : Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) := by
    by_cases isEA : bE = a
    · subst isEA
      have same : sE = sa := Option.some.inj (storedE.symm.trans storedA)
      subst same
      exact run_from_bridge bridge boundaryLe reach beforeS
    · have walkA := Store.getAncestor_of_isAncestor_of_lt early aFound descends
      have aLeS : aBlock.slot ≤ S := UInt64.le_trans aLe boundaryLe
      have through := Store.getAncestor_trans aLeS walkE
      rw [walkA] at through
      have aLeE : aBlock.slot ≤ bEBlock.slot := by
        by_contra notLe
        have le : bEBlock.slot ≤ aBlock.slot := UInt64.le_of_lt (UInt64.not_le.mp notLe)
        rw [Store.getAncestor_of_le (node := ⟨bE, .pending⟩) bEFound le] at through
        exact isEA (congrArg ForkChoiceNode.root (Except.ok.inj through)).symm
      have aDescE : ((e.world k).state w).isAncestor ⟨bE, .pending⟩ ⟨a, .pending⟩ =
          .ok true := by
        simp [Store.isAncestor, Store.block_ok_iff.mpr aFound, through.symm, bind, Except.bind,
          pure, Except.pure]
      have clearA : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
          ((e.world k).state w).blocks[q]? = some qBlock →
          ((e.world k).state w).isAncestor ⟨bE, .pending⟩ ⟨q, .pending⟩ = .ok true →
          aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a :=
        fun q qBlock qFound hq above below => clearC q qBlock qFound
          (Store.isAncestor_trans_of_lt early bEFound qFound bEDesc hq) above below
      have farE : boundary < bEBlock.slot := by
        by_contra notFar
        exact isEA (clearC bE bEBlock bEFound bEDesc aLeE (UInt64.not_lt.mp notFar))
      obtain ⟨r1⟩ := run_along_chain anchored early anchorSlot honest start before aFound storedA
        bridge bEBlock.slot.toNat bE bEBlock sE rfl bEFound storedE aDescE clearA farE
      obtain ⟨r2⟩ := run_from_bridge (sa := sE) (s0 := sE) (boundary := sE.slot)
        (.inl ⟨rfl, rfl⟩) (sESlot ▸ bELe) reach beforeS
      exact ⟨r1.append r2⟩
  obtain ⟨runYH⟩ := run_along_chain anchored early anchorSlot honest start before bEFound storedE
    reach headBlock.slot.toNat head headBlock hs rfl headFound stored bEDesc clearE farHead
  refine ⟨y, runY, UInt64.le_of_eq curY, ?_⟩
  intro position
  have kept := activeKept_of_chainSteps runYH.chainSteps epoch
    (ExitChurn.fixed_ge y (n := 0) (by rw [curY]; omega) (Nat.zero_le _) bounded) position
  exact kept.symm

private theorem cache_tick {store after : Store preset fork} {time : UInt64}
    (ticked : store.onTick config time = .ok after) :
    after.unrealizedJustifications = store.unrealizedJustifications := by
  have step : ∀ {s t : Store preset fork} {time : UInt64},
      s.onTickPerSlot config time = .ok t →
      t.unrealizedJustifications = s.unrealizedJustifications := by
    intro s t time ticked
    unfold Store.onTickPerSlot at ticked
    simp only [bind_ok_iff] at ticked
    obtain ⟨_, _, _, _, ticked⟩ := ticked
    split at ticked <;>
      · obtain ⟨_, _, ticked⟩ := ticked
        split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
          subst t <;> try rfl
        all_goals unfold Store.updateCheckpoints
        all_goals split <;> dsimp only <;> split <;> rfl
  have catchup : ∀ {s t : Store preset fork} {slot : Slot},
      Store.catchUp config s slot = .ok t →
      t.unrealizedJustifications = s.unrealizedJustifications := by
    intro s t slot caught
    induction s using Store.catchUp.induct config slot with
    | _ s ih =>
      rw [Store.catchUp.eq_1] at caught
      simp only [bind_ok_iff] at caught
      obtain ⟨_, _, caught⟩ := caught
      split at caught
      · simp only [bind_ok_iff] at caught
        obtain ⟨_, _, _, _, ticked, tick, caught⟩ := caught
        split at caught
        · exact (ih ticked ‹_› caught).trans (step tick)
        · cases caught
      · cases Except.ok.inj caught
        rfl
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨_, _, caught, caughtOk, ticked⟩ := ticked
  exact (step ticked).trans (catchup caughtOk)

private theorem cache_attestation {store after : Store preset fork}
    {attestation : Attestation preset fork} {fromBlock : Bool}
    (attested : store.onAttestation config checks attestation fromBlock = .ok after) :
    after.unrealizedJustifications = store.unrealizedJustifications := by
  unfold Store.onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, cached, caching, _, _, _, _, _, _, _, _, attested⟩ := attested
  have kept : cached.unrealizedJustifications = store.unrealizedJustifications := by
    unfold Store.storeTargetCheckpointState at caching
    split at caching
    · cases Except.ok.inj caching
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at caching
      obtain ⟨_, _, rfl⟩ := caching
      rfl
  split at attested
  · cases Except.ok.inj attested
    exact kept
  · cases attested

private theorem cache_pulled {store after : Store preset fork} {root key : Root}
    {checkpoint : Checkpoint}
    (computed : store.computePulledUpTip config root = .ok after)
    (entry : after.unrealizedJustifications[key]? = some checkpoint) :
    store.unrealizedJustifications[key]? = some checkpoint ∨
      ∃ state pulled, after.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = checkpoint := by
  have states := (Store.computePulledUpTip_frame computed).2.2.1
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, _, epoch, _, computed⟩ := computed
  have update : ∀ (s : Store preset fork) j f,
      (s.updateCheckpoints j f).unrealizedJustifications = s.unrealizedJustifications := by
    intro s j f
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> rfl
  have pending : ∀ (s : Store preset fork) j f,
      (s.updateUnrealizedCheckpoints j f).unrealizedJustifications =
        s.unrealizedJustifications := by
    intro s j f
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> rfl
  have cache : after.unrealizedJustifications =
      store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint := by
    split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
      subst after
    all_goals simp only [update, pending]
  rw [cache, getElem?_insert_root] at entry
  by_cases same : root = key
  · simp only [same, ↓reduceIte, Option.some.injEq] at entry
    exact .inr ⟨state, pulled, states.symm ▸ same ▸ Store.blockState_ok_iff.mp found,
      mapError_ok_iff.mp processed, entry⟩
  · exact .inl (by simpa [same] using entry)

private theorem cache_block {store after : Store preset fork}
    {signed : SignedBeaconBlock preset fork} {key : Root} {checkpoint : Checkpoint}
    (added : store.onBlock config checks sources signed = .ok after)
    (entry : after.unrealizedJustifications[key]? = some checkpoint) :
    store.unrealizedJustifications[key]? = some checkpoint ∨
      ∃ state pulled, after.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = checkpoint := by
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact .inl entry
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, _, head, _, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedCache : recorded.unrealizedJustifications = store.unrealizedJustifications := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        rfl
      · cases record
        rfl
    have boostedCache : boosted.unrealizedJustifications = store.unrealizedJustifications := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedCache
    rcases cache_pulled added entry with old | fresh
    · left
      have kept : (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).unrealizedJustifications =
            boosted.unrealizedJustifications := by
        unfold Store.updateCheckpoints
        split <;> dsimp only <;> split <;> rfl
      rwa [kept, boostedCache] at old
    · exact .inr fresh

private theorem cache_origin {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (early : fork < .glamsterdam) {key : Root} {checkpoint : Checkpoint}
    (entry : store.unrealizedJustifications[key]? = some checkpoint) :
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      ∃ state pulled, store.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.currentJustifiedCheckpoint := by
  induction reachable with
  | anchor made =>
    unfold getForkchoiceStore at made
    simp only [bind_ok_iff] at made
    obtain ⟨stateRoot, _, made⟩ := made
    split at made
    · cases made
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
      obtain ⟨root, rootOk, time, _, rfl⟩ := made
      rw [getElem?_insert_root] at entry
      split at entry
      · cases Option.some.inj entry
        exact .inl ⟨root, mapError_ok_iff.mp rootOk, rfl⟩
      · simp at entry
  | tick prior ticked ih =>
    rw [cache_tick ticked] at entry
    rcases ih entry with old | ⟨state, pulled, held, processed, same⟩
    · exact .inl old
    · exact .inr ⟨state, pulled, (Store.onTick_frame ticked).2.2.2.symm ▸ held, processed, same⟩
  | @block prior after checks sources signed reachable added ih =>
    rcases cache_block added entry with old | fresh
    · rcases ih old with old | ⟨state, pulled, held, processed, same⟩
      · exact .inl old
      · right
        refine ⟨state, pulled, ?_, processed, same⟩
        rcases Store.onBlock_same_or_insert added with eq |
          ⟨newRoot, _, fresh, _, _, _, _, _, states⟩
        · exact eq ▸ held
        have other : newRoot ≠ key := by
          rintro rfl
          rw [reachable.blockState_eq_none fresh] at held
          cases held
        rw [states, getElem?_insert_root]
        simpa only [other, ↓reduceIte] using held
    · obtain ⟨state, pulled, held, processed, same⟩ := fresh
      exact .inr ⟨state, pulled, held, processed, same.symm⟩
  | attestation prior attested ih =>
    rw [cache_attestation attested] at entry
    rcases ih entry with old | ⟨state, pulled, held, processed, same⟩
    · exact .inl old
    · exact .inr ⟨state, pulled, (Store.onAttestation_frame attested).2.2.symm ▸ held,
        processed, same⟩
  | attesterSlashing prior slashed ih =>
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact ih entry
  | payloadAttestation => exact False.elim (Nat.not_le_of_lt early ‹.glamsterdam ≤ fork›)
  | envelope => exact False.elim (Nat.not_le_of_lt early ‹.glamsterdam ≤ fork›)
  | inclusionList =>
    exact False.elim (Nat.not_le_of_lt early
      (Nat.le_trans (by decide : Fork.glamsterdam ≤ Fork.hegota) ‹.hegota ≤ fork›))

private theorem justified_origin {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (early : fork < .glamsterdam) {checkpoint : Checkpoint}
    (justified : store.Justified checkpoint) :
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      ∃ (root : Root) (state : BeaconState preset fork) (view : TerminalView ⟨fork, state⟩),
        store.blockStates[root]? = some state ∧
          checkpoint = view.state.currentJustifiedCheckpoint := by
  have fields (selected : checkpoint = store.justifiedCheckpoint ∨
      checkpoint = store.unrealizedJustifiedCheckpoint) :=
    reachable.justified_origins checkpoint selected
  rcases justified with real | pending | ⟨_, real | ⟨root, cached⟩⟩
  · rcases fields (.inl real) with anchor | ⟨root, state, held, same⟩ |
        ⟨root, state, pulled, held, processed, same⟩
    · exact .inl anchor
    · exact .inr ⟨root, state, .realized, held, same⟩
    · exact .inr ⟨root, state, .pulled pulled processed, held, same⟩
  · rcases fields (.inr pending) with anchor | ⟨root, state, held, same⟩ |
        ⟨root, state, pulled, held, processed, same⟩
    · exact .inl anchor
    · exact .inr ⟨root, state, .realized, held, same⟩
    · exact .inr ⟨root, state, .pulled pulled processed, held, same⟩
  · obtain ⟨root, state, held, same⟩ := real
    exact .inr ⟨root, state, .realized, held, same⟩
  · rcases cache_origin reachable early cached with anchor |
        ⟨state, pulled, held, processed, same⟩
    · exact .inl anchor
    · exact .inr ⟨root, state, .pulled pulled processed, held, same⟩

private theorem hash_evidence_mono {one two : List (HashObject preset)}
    (subset : ∀ object ∈ one, object ∈ two) (evidence : HashEvidence one) :
    HashEvidence two := by
  have messages : ∀ message ∈ one.flatMap HashObject.messages,
      message ∈ two.flatMap HashObject.messages := by
    intro message member
    obtain ⟨object, member, inside⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr ⟨object, subset object member, inside⟩
  rcases evidence with ⟨x, hx, y, hy, collision⟩ | ⟨object, member, zero⟩
  · exact .inl ⟨x, messages x hx, y, messages y hy, collision⟩
  · exact .inr ⟨object, subset object member, zero⟩

private theorem endpoint_hashObject {g a : ForkedBeaconState preset}
    (run : Run config checks g a) : HashObject.state a ∈ run.hashObjects := by
  cases run with
  | nil => simp [Run.hashObjects]
  | snoc pre step =>
    apply List.mem_append_right
    cases step <;> simp [Step.hashObjects]

private theorem nil_append_run {g a : ForkedBeaconState preset}
    (run : Run config checks g a) : Run.nil.append run = run := by
  induction run with
  | nil => rfl
  | snoc pre step ih => exact congrArg (fun run => run.snoc step) ih

private theorem checkpoint_fields {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) {anchorRoot : Root}
    (rooted : SszType.hashTreeRoot anchorBlock = .ok anchorRoot)
    (p : Checkpoint → Prop) (initial : p ⟨getCurrentEpoch anchorState, anchorRoot⟩)
    (newer : ∀ old next, p old → old.epoch < next.epoch → p next) :
    (p store.justifiedCheckpoint ∧ p store.unrealizedJustifiedCheckpoint) ∧
      p store.finalizedCheckpoint ∧ p store.unrealizedFinalizedCheckpoint := by
  let P := fun (s : Store preset fork) =>
    (p s.justifiedCheckpoint ∧ p s.unrealizedJustifiedCheckpoint) ∧
      p s.finalizedCheckpoint ∧ p s.unrealizedFinalizedCheckpoint
  have update (s : Store preset fork) j f (old : P s) : P (s.updateCheckpoints j f) := by
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split
    all_goals refine ⟨⟨?_, old.1.2⟩, ?_, old.2.2⟩
    all_goals first | exact old.1.1 | exact old.2.1 |
      exact newer _ _ old.1.1 ‹_› | exact newer _ _ old.2.1 ‹_›
  have pending (s : Store preset fork) j f (old : P s) : P (s.updateUnrealizedCheckpoints j f) := by
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split
    all_goals refine ⟨⟨old.1.1, ?_⟩, old.2.1, ?_⟩
    all_goals first | exact old.1.2 | exact old.2.2 |
      exact newer _ _ old.1.2 ‹_› | exact newer _ _ old.2.2 ‹_›
  have pull {s t : Store preset fork} {root : Root} (old : P s)
      (computed : s.computePulledUpTip config root = .ok t) : P t := by
    unfold Store.computePulledUpTip at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨state, _, pulled, _, block, _, epoch, _, computed⟩ := computed
    have kept := pending
      { s with unrealizedJustifications :=
          s.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint }
      pulled.currentJustifiedCheckpoint
      pulled.finalizedCheckpoint old
    split at computed <;> cases Except.ok.inj computed
    · exact update _ _ _ kept
    · exact kept
  have tick {s t : Store preset fork} {time : UInt64} (old : P s)
      (computed : s.onTickPerSlot config time = .ok t) : P t := by
    unfold Store.onTickPerSlot at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨previous, _, current, _, computed⟩ := computed
    split at computed <;>
      · obtain ⟨_, _, computed⟩ := computed
        split at computed <;> cases Except.ok.inj computed
        all_goals first | exact update _ _ _ old | exact old
  have invariant : P store := by
    induction reachable with
    | anchor made =>
      obtain ⟨root, rootOk, _, _, real, final, unrealized, pending⟩ :=
        getForkchoiceStore_anchor made
      rw [rooted, Except.ok.injEq] at rootOk
      subst root
      exact ⟨⟨real ▸ initial, unrealized ▸ initial⟩, final ▸ initial, pending ▸ initial⟩
    | tick before computed ih =>
      have catchup : ∀ {s t : Store preset fork} {slot : Slot}, P s →
          Store.catchUp config s slot = .ok t → P t := by
        intro s t slot old caught
        induction s using Store.catchUp.induct config slot with
        | _ s ih =>
          rw [Store.catchUp.eq_1] at caught
          simp only [bind_ok_iff] at caught
          obtain ⟨_, _, caught⟩ := caught
          split at caught
          · simp only [bind_ok_iff] at caught
            obtain ⟨_, _, _, _, ticked, tickOk, caught⟩ := caught
            split at caught
            · exact ih ticked ‹_› (tick old tickOk) caught
            · cases caught
          · cases Except.ok.inj caught
            exact old
      unfold Store.onTick at computed
      simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, caught, ticked⟩ := computed
      exact tick (catchup ih caught) ticked
    | @block before after checks sources signed reachable added ih =>
      cases root : SszType.hashTreeRoot signed.message with
      | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
      | ok blockRoot =>
        by_cases known : before.blocks.contains blockRoot
        · rw [Store.onBlock_known root known] at added
          cases added
          exact ih
        simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
          Bool.false_eq_true] at added
        unfold Store.addBlock at added
        simp only [bind_ok_iff] at added
        obtain ⟨state, _, head, _, voted, vote, recorded, record, boosted, boost, added⟩ := added
        obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
        have recordedP : P recorded := by
          unfold Store.recordBlockTimeliness at record
          simp only [bind_ok_iff, pure, Except.pure] at record
          obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
          split at record
          · simp only [bind_ok_iff, Except.ok.injEq] at record
            obtain ⟨_, _, rfl⟩ := record
            exact ih
          · cases record
            exact ih
        have boostedP : P boosted := by
          unfold Store.updateProposerBoostRoot at boost
          split at boost
          rotate_left
          · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
          simp only [bind_ok_iff, pure_bind] at boost
          obtain ⟨_, _, _, _, _, _, boost⟩ := boost
          split at boost <;> cases Except.ok.inj boost <;> exact recordedP
        exact pull (update _ _ _ boostedP) added
    | attestation before attested ih =>
      unfold Store.onAttestation at attested
      simp only [bind_ok_iff] at attested
      obtain ⟨_, _, cached, caching, _, _, _, _, _, _, _, _, attested⟩ := attested
      have kept : P cached := by
        unfold Store.storeTargetCheckpointState at caching
        split at caching
        · cases Except.ok.inj caching
          exact ih
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at caching
          obtain ⟨_, _, rfl⟩ := caching
          exact ih
      split at attested
      · cases Except.ok.inj attested
        exact kept
      · cases attested
    | attesterSlashing before slashed ih =>
      unfold Store.onAttesterSlashing at slashed
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
      obtain ⟨_, _, rfl⟩ := slashed
      exact ih
    | payloadAttestation before voted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
      exact ih
    | envelope before accepted ih =>
      obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
      obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
      exact ih
    | inclusionList before accepted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
      exact ih
  exact invariant

private theorem justified_zero {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) {anchorRoot : Root}
    (rooted : SszType.hashTreeRoot anchorBlock = .ok anchorRoot)
    {checkpoint : Checkpoint} (justified : store.Justified checkpoint)
    (zero : checkpoint.epoch = 0) :
    checkpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ := by
  have invariant := (checkpoint_fields reachable rooted
    (fun checkpoint => checkpoint.epoch = 0 →
      checkpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩) (fun _ => rfl)
    (fun _ _ _ later eq => (UInt64.not_lt_zero (eq ▸ later)).elim)).1
  rcases justified with rfl | rfl | ⟨positive, _⟩
  · exact invariant.1 zero
  · exact invariant.2 zero
  · rw [zero] at positive
    exact (UInt64.not_lt_zero positive).elim

omit [DecidablePred (· ∈ J)] in
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
  classical
  by_cases fault : e.AccountableFault history horizon limit ∨ e.HashFault history limit
  · exact .inr fault
  left
  intro u honestU w honestW n k boundedN boundedK first second justFirst justSecond sameEpoch high
  have reach := e.reachable (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun v member => by rw [start v member]; exact .anchor anchored)
  obtain ⟨anchorRoot, rooted, _, _, _, _, _, _⟩ := getForkchoiceStore_anchor anchored
  by_cases zero : first.epoch = 0
  · exact (justified_zero (reach n u honestU) rooted justFirst zero).trans
      (justified_zero (reach k w honestW) rooted justSecond (sameEpoch ▸ zero)).symm
  have anchorHeld : e.HeldState limit anchorState := by
    obtain ⟨root, _, found⟩ := (reach n u honestU).anchor_known
    obtain ⟨state, stored, initial, _⟩ := (reach n u honestU).blockStatesFromParents found
    exact ⟨u, honestU, n, root, boundedN, initial rfl ▸ stored⟩
  have anchorNonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0 := by
    intro zeroRoot
    apply fault
    right
    refine ⟨anchorState, anchorState, .nil, .nil, .realized, .realized,
      anchorHeld, anchorHeld, .inr ⟨.state ⟨fork, anchorState⟩, ?_, ?_⟩⟩
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (endpoint_hashObject history)))))
    · simp only [HashObject.root, anchor_stateRoot anchored, zeroRoot, Except.toOption]
  have anchorCase {v : ValidatorIndex} (honest : v ∈ J) {m : ℕ} {root : Root}
      {state : BeaconState preset fork}
      (stored : ((e.world m).state v).blockStates[root]? = some state)
      (view : TerminalView ⟨fork, state⟩) {checkpoint : Checkpoint}
      (field : checkpoint = view.state.currentJustifiedCheckpoint)
      (epoch : checkpoint.epoch = getCurrentEpoch anchorState)
      (positive : checkpoint.epoch ≠ 0) :
      checkpoint = (⟨getCurrentEpoch anchorState, anchorRoot⟩ : Checkpoint) := by
    have later : 0 < (getCurrentEpoch anchorState).toNat := by
      have nonzero := epoch ▸ positive
      have ne : (getCurrentEpoch anchorState).toNat ≠ 0 := by
        intro eq
        exact nonzero (UInt64.toNat_inj.mp eq)
      omega
    have fixed := e.epochRootFixed_of_blockState anchored sound (by have := parameters.roots; omega)
      anchorSlot anchorAtBoundary later anchorNonzero rooted honest (start v honest) stored
    have rootEq : checkpoint.root = anchorRoot := by
      cases view with
      | realized => exact field ▸ fixed.1 (field ▸ epoch)
      | pulled after computed =>
        exact field ▸ (fixed.of_processJustificationAndFinalization computed).1 (field ▸ epoch)
    cases checkpoint
    simp_all only
  rcases justified_origin (reach n u honestU) forkWindow.1 justFirst with
      ⟨rootA, rootOkA, anchorA⟩ | ⟨rootA, stateA, va, storedA, fieldA⟩
  · rw [rooted, Except.ok.injEq] at rootOkA
    subst rootA
    rcases justified_origin (reach k w honestW) forkWindow.1 justSecond with
        ⟨rootB, rootOkB, anchorB⟩ | ⟨rootB, stateB, vb, storedB, fieldB⟩
    · rw [rooted, Except.ok.injEq] at rootOkB
      subst rootB
      exact anchorA.trans anchorB.symm
    · exact anchorA.trans (anchorCase honestW storedB vb fieldB
        (sameEpoch.symm.trans (congrArg Checkpoint.epoch anchorA))
        (fun h => zero (sameEpoch.trans h))).symm
  · rcases justified_origin (reach k w honestW) forkWindow.1 justSecond with
        ⟨rootB, rootOkB, anchorB⟩ | ⟨rootB, stateB, vb, storedB, fieldB⟩
    · rw [rooted, Except.ok.injEq] at rootOkB
      subst rootB
      exact (anchorCase honestU storedA va fieldA
        (sameEpoch.trans (congrArg Checkpoint.epoch anchorB)) zero).trans anchorB.symm
    · obtain ⟨left, enoughA, terminalA, _⟩ := held_run_enough anchored start anchorSlot slots
        parameters genesis history forkWindow inHorizon historyEnough large honestU boundedN storedA
      obtain ⟨right, enoughB, terminalB, _⟩ := held_run_enough anchored start anchorSlot slots
        parameters genesis history forkWindow inHorizon historyEnough large honestW boundedK storedB
      have heldA : e.HeldState limit stateA := ⟨u, honestU, n, rootA, boundedN, storedA⟩
      have heldB : e.HeldState limit stateB := ⟨w, honestW, k, rootB, boundedK, storedB⟩
      have noHash (evidence : HashEvidence ((history.append left).hashObjects ++
          (history.append right).hashObjects ++ va.hashObjects ++ vb.hashObjects)) : False := by
        apply fault
        right
        refine ⟨stateA, stateB, left, right, va, vb, heldA, heldB, ?_⟩
        exact hash_evidence_mono (fun _ member =>
          List.mem_append_left _ (List.mem_append_left _ member)) evidence
      by_cases starts : anchorState.slot.toNat ≤ first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat
      · rcases accountable_terminal_justified_unique history left right va vb parameters genesis
          forkWindow.1 forkWindow.1 enoughA enoughB (terminalA va) (terminalB vb) first second
          (.inr fieldA) (.inr fieldB) sameEpoch starts with same | accountable | hashes
        · exact same
        · exact (fault (.inl ⟨stateA, stateB, left, right, va, vb, first, heldA, heldB,
            .inr (.inl fieldA), high, .inl accountable⟩)).elim
        · exact (noHash hashes).elim
      · have genesisSlot : g.state.slot = 0 := by
          obtain ⟨_, _, _, initialized⟩ := genesis
          exact (initializeBeaconStateFromEth1_checkpoints initialized).1
        rcases accountable_terminal_justified_unique Run.nil (history.append left)
            (history.append right) va vb parameters genesis forkWindow.1 forkWindow.1
            (by simpa only [nil_append_run] using enoughA)
            (by simpa only [nil_append_run] using enoughB) (terminalA va) (terminalB vb)
            first second (.inr fieldA) (.inr fieldB) sameEpoch
            (by rw [genesisSlot]; exact Nat.zero_le _)
          with same | accountable | hashes
        · exact same
        · exact (fault (.inl ⟨stateA, stateB, left, right, va, vb, first, heldA, heldB,
            .inr (.inl fieldA), high, .inr accountable⟩)).elim
        · exact (noHash (by simpa only [nil_append_run] using hashes)).elim

omit [DecidablePred (· ∈ J)] in
/-- Honest stores agree on the block at each shared root, or two held states show a hash fault.

It reads two equal block roots through `DirectSafety.block_binding`, before Gloas. -/
theorem Execution.oneBlockPerRoot_or_fault {anchor : Store preset fork}
    [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
    [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (epochSlots : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g : ForkedBeaconState preset} (history : Run config checks g ⟨fork, anchorState⟩)
    {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon) :
    OneBlockPerRoot e limit ∨ e.HashFault history limit := by
  classical
  -- Select the actual block input, except for the anchor, which is supplied separately.
  have select {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
      (bounded : (e.world k).time ≤ limit) {root : Root} {block : BeaconBlock preset fork}
      (found : ((e.world k).state w).blocks[root]? = some block) :
      ∃ (state : BeaconState preset fork)
        (run : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩),
        ((e.world k).state w).blockStates[root]? = some state ∧
        HashObject.block fork block ∈
          (history.append run).hashObjects ++ [HashObject.block fork anchorBlock] := by
    have reached := e.reachable
      (fun v hv => (start v hv) ▸ Store.Reachable.anchor anchored) k w honest
    obtain ⟨state, stored, initial, -⟩ := reached.blockStatesFromParents found
    by_cases same : block = anchorBlock
    · have equal := initial same
      subst state
      exact ⟨anchorState, .nil, stored, List.mem_append_right _ (by simp [same])⟩
    · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
        e.exists_transition_of_nonanchor_block anchored honest (start w honest) found stored same
      have before := e.heldBlocks_before_nextFork anchored start anchorSlot slots epochSlots
        inHorizon forkWindow.2 honest bounded
      obtain ⟨pre⟩ := e.exists_run_of_blockState anchored honest (start w honest) before parentFound
      have across : stateTransitionAcross config checks sources.engine ⟨fork, parent⟩ signed true =
          .ok state := by
        rw [stateTransitionAcross_of_before (by simpa only [message] using before root block found)]
        exact transitioned
      obtain ⟨advanced, slotRun, due, applied, -, -, -⟩ :=
        Run.stateTransition sources.engine signed across
      refine ⟨state, pre.append (slotRun.snoc (.block sources.engine signed due applied)),
        stored, List.mem_append_left _ ?_⟩
      apply List.mem_append_right
      unfold Step.hashObjects
      simp [message]
  by_cases fault : e.HashFault history limit
  · exact .inr fault
  left
  intro v honestV u honestU n k boundedN boundedK root a b foundA foundB
  obtain ⟨stateA, left, storedA, memberA⟩ := select honestV boundedN foundA
  obtain ⟨stateB, right, storedB, memberB⟩ := select honestU boundedK foundB
  have reachedA := e.reachable
    (fun w hw => (start w hw) ▸ Store.Reachable.anchor anchored) n v honestV
  have reachedB := e.reachable
    (fun w hw => (start w hw) ▸ Store.Reachable.anchor anchored) k u honestU
  let objects := (history.append left).hashObjects ++ (history.append right).hashObjects ++
    (TerminalView.realized (a := ⟨fork, stateA⟩)).hashObjects ++
    (TerminalView.realized (a := ⟨fork, stateB⟩)).hashObjects ++
    (blockHeader anchorBlock).toList.map HashObject.header ++ [HashObject.block fork anchorBlock]
  have one : HashObject.block fork a ∈ objects := by
    simp only [objects, List.mem_append, List.mem_singleton] at memberA ⊢
    tauto
  have two : HashObject.block fork b ∈ objects := by
    simp only [objects, List.mem_append, List.mem_singleton] at memberB ⊢
    tauto
  rcases DirectSafety.block_binding forkWindow.1 objects a b one two root
      (reachedA.root foundA) (reachedB.root foundB) with same | evidence
  · exact same
  · exact (fault ⟨stateA, stateB, left, right, .realized, .realized,
      ⟨v, honestV, n, root, boundedN, storedA⟩,
      ⟨u, honestU, k, root, boundedK, storedB⟩, evidence⟩).elim

omit [DecidablePred (· ∈ J)] in
/-- Each block of an honest store has a nonzero state root, or a held state shows a hash fault.

A zero state root of a held block is the root of a state among the hash inputs. -/
theorem Execution.nonzero_or_fault {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (epochSlots : 0 < preset.SLOTS_PER_EPOCH.toNat)
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
  classical
  by_cases fault : e.HashFault history limit
  · exact .inr fault
  left
  intro w honest k bounded root block found zero
  have reached := (e.forwardReachable
    (fun v hv => (start v hv) ▸ Store.ForwardReachable.anchor anchored) k w honest).reachable
  obtain ⟨state, stored, initial, -⟩ := reached.blockStatesFromParents found
  have rooted : SszType.hashTreeRoot state = .ok block.stateRoot := by
    by_cases same : block = anchorBlock
    · rw [initial same, same]
      exact anchor_stateRoot anchored
    · exact (reached.blockState_header found stored same).2.1
  obtain ⟨run⟩ := e.exists_run_of_blockState anchored honest (start w honest)
    (e.heldBlocks_before_nextFork anchored start anchorSlot slots epochSlots inHorizon
      forkWindow.2 honest bounded) stored
  have held : e.HeldState limit state := ⟨w, honest, k, root, bounded, stored⟩
  have endpoint {first last : ForkedBeaconState preset} (path : Run config checks first last) :
      HashObject.state last ∈ path.hashObjects := by
    cases path with
    | nil => simp [Run.hashObjects]
    | snoc pre step =>
      apply List.mem_append_right
      unfold Step.hashObjects
      exact List.mem_append_left _ (by simp)
  apply fault
  -- A zero-root fault can use the same held state and run on both sides.
  refine ⟨state, state, run, run, .realized, .realized, held, held, Or.inr ?_⟩
  refine ⟨.state ⟨fork, state⟩, ?_, ?_⟩
  · simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (endpoint (history.append run))))))
  · change (SszType.hashTreeRoot state).toOption = some (Vector.replicate 32 0)
    rw [rooted, zero]
    rfl

private theorem state_checkpoint_read {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (early : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    CheckpointsSatisfy (fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      ∃ boundary block, store.blocks[root]? = some block ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  obtain ⟨post, postOk, initial, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · rw [initial same]
    have bound := UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState)
    exact ⟨.inl (UInt64.le_trans sound.ordered.2 bound), .inl bound,
      .inl (UInt64.le_trans sound.ordered.1 (UInt64.le_trans sound.ordered.2 bound))⟩
  · obtain ⟨parent, checks, engine, signed, message, parentFound, transitioned⟩ := produced same
    obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok transitioned
    have prior := state_checkpoint_read reachable sound early positive window aligned
      nonzero parentFound
    obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
    have parentLe := reachable.blockState_slot_le aligned parentKnown parentFound
    have parentLt : parent.slot < block.slot := by
      simpa only [message] using (stateTransition_slot transitioned).1
    have parentBlockLt := UInt64.lt_of_le_of_lt parentLe parentLt
    have inherit (checkpoint : Checkpoint)
        (holds : checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
          ∃ boundary b, store.blocks[block.parentRoot]? = some b ∧
            computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ b.slot ∧
            store.getCheckpointBlock block.parentRoot checkpoint.epoch = .ok checkpoint.root) :
        checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
          ∃ boundary b, store.blocks[root]? = some b ∧
            computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ b.slot ∧
            store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root := by
      rcases holds with old | ⟨boundary, b, known, boundaryOk, below, read⟩
      · exact .inl old
      have eq := Option.some.inj (known.symm.trans parentKnown)
      subst b
      have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) early found
        (UInt64.not_le.mpr (UInt64.lt_of_le_of_lt below parentBlockLt)) parentKnown parentBlockLt
      refine .inr ⟨boundary, block, found, boundaryOk,
        UInt64.le_trans below (UInt64.le_of_lt parentBlockLt), ?_⟩
      simpa [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind, step]
        using read
    have lifted : CheckpointsSatisfy (fun checkpoint =>
        checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
          ∃ boundary b, store.blocks[root]? = some b ∧
            computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ b.slot ∧
            store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) parent :=
      ⟨inherit _ prior.1, inherit _ prior.2.1, inherit _ prior.2.2⟩
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, run⟩ := slotsOk
    apply (CheckpointsSatisfy.advanceSlots (state := parent) lifted ?_ run).of_frame
      (frame_processBlock blockOk)
    intro i bounded middle cached advanced cachedOk checkpoint recent read
    by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
    · exact .inl old
    have recent' : checkpoint.epoch = getPreviousEpoch middle ∨
        checkpoint.epoch = getCurrentEpoch middle := by
      simpa only [getPreviousEpoch, getCurrentEpoch, processSlot_slot cachedOk] using recent
    rw [getBlockRoot_processSlot_of_recent_epoch positive window cachedOk recent'] at read
    obtain ⟨boundary, boundaryOk, read⟩ := getBlockRoot_ok_iff.mp read
    have later : anchorState.slot ≤ boundary := by
      have epochLt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp old)
      rw [getCurrentEpoch_toNat] at epochLt
      have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
      have eq := (Base.Uint64.mulChecked_ok_iff.mp boundaryOk).2
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have path : (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ boundary =
        .ok checkpoint.root := by
      cases i with
      | zero =>
        cases Except.ok.inj advanced
        exact reachable.blockState_history_ancestor aligned nonzero parentFound read later .pending
      | succ i =>
        have atSlot := advanceSlots_slot (i + 1) advanced
        have greater : parent.slot < middle.slot := UInt64.lt_iff_toNat_lt.mpr (by omega)
        have computed : processSlots config checks parent middle.slot = .ok middle := by
          simp only [processSlots, bind_ok_iff, ensure_ok_iff]
          refine ⟨(), greater, ?_⟩
          have countEq : middle.slot.toNat - parent.slot.toNat = i + 1 := by omega
          simpa only [countEq] using advanced
        obtain ⟨readBlock, known, _⟩ := reachable.processSlots_history_slot_le nonzero
          ⟨root, block, found, same⟩ parentFound computed read later (UInt64.le_trans aligned later)
        have ahead : lookaheadState config checks parent middle.slot = .ok middle := by
          simp [lookaheadState, greater, computed, Except.mapError]
        exact reachable.lookahead_history_ancestor aligned nonzero parentFound known ahead read
          later .pending
    have checkpointRead : store.getCheckpointBlock block.parentRoot checkpoint.epoch =
        .ok checkpoint.root := by
      simpa [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind,
        Functor.map, Except.map, pure, Except.pure] using path
    have middleLt : middle.slot < block.slot := by
      have atSlot := advanceSlots_slot i advanced
      rw [message] at bounded
      have low := UInt64.lt_iff_toNat_lt.mp parentLt
      exact UInt64.lt_iff_toNat_lt.mpr (by omega)
    have boundaryLt : boundary < block.slot := UInt64.lt_trans
      (UInt64.lt_iff_toNat_lt.mpr (getBlockRootAtSlot_ok_iff.mp read).1) middleLt
    have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) early found
      (UInt64.not_le.mpr boundaryLt) parentKnown parentBlockLt
    refine .inr ⟨boundary, block, found, boundaryOk, UInt64.le_of_lt boundaryLt, ?_⟩
    simpa [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind, step]
      using checkpointRead
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

private theorem view_checkpoint_read {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (early : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) (view : TerminalView ⟨fork, state⟩) :
    CheckpointsSatisfy (fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      ∃ boundary block, store.blocks[root]? = some block ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) view.state := by
  have holds := state_checkpoint_read reachable sound early positive window aligned nonzero stored
  cases view with
  | realized => exact holds
  | pulled after computed =>
    apply holds.processJustification ?_ computed
    intro checkpoint _ read
    by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
    · exact .inl old
    obtain ⟨boundary, boundaryOk, read⟩ := getBlockRoot_ok_iff.mp read
    have later : anchorState.slot ≤ boundary := by
      have epochLt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp old)
      rw [getCurrentEpoch_toNat] at epochLt
      have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
      have eq := (Base.Uint64.mulChecked_ok_iff.mp boundaryOk).2
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have path := reachable.blockState_history_ancestor aligned nonzero stored read later .pending
    obtain ⟨block, found⟩ := reachable.known_of_blockState stored
    have notAnchor : block ≠ anchorBlock := by
      intro same
      obtain ⟨post, postOk, initial, _⟩ := reachable.blockStatesFromParents found
      rw [stored, Option.some.injEq] at postOk
      subst post
      rw [initial same] at read
      have lt := (getBlockRootAtSlot_ok_iff.mp read).1
      have le := UInt64.le_iff_toNat_le.mp later
      omega
    have below : boundary ≤ block.slot := by
      rw [← (reachable.blockState_header found stored notAnchor).1]
      exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (getBlockRootAtSlot_ok_iff.mp read).1)
    refine .inr ⟨boundary, block, found, boundaryOk, below, ?_⟩
    simpa [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure] using path

omit [DecidablePred (· ∈ J)] in
private theorem anchor_checkpoint_read {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (early : fork < .glamsterdam) {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block) :
    ((e.world k).state w).getCheckpointBlock root anchor.finalizedCheckpoint.epoch =
      .ok anchor.finalizedCheckpoint.root := by
  have reached := e.reachable
    (fun v member => (start v member) ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨anchorRoot, rooted, _, _, _, final, _, _⟩ := getForkchoiceStore_anchor anchored
  obtain ⟨other, hashed, found⟩ := reached.anchor_known
  rw [rooted, Except.ok.injEq] at hashed
  subst other
  have boundaryOk : computeStartSlotAtEpoch preset anchor.finalizedCheckpoint.epoch =
      .ok anchorBlock.slot := by
    have aligned : (getCurrentEpoch anchorState).toNat * preset.SLOTS_PER_EPOCH.toNat =
        anchorBlock.slot.toNat := by
      rw [getCurrentEpoch, ← anchorSlot]
      exact anchor_boundary anchorBoundary
    apply computeStartSlotAtEpoch_ok_iff.mpr
    rw [final]
    constructor
    · rw [aligned]
      exact anchorBlock.slot.toNat_lt
    · exact aligned.symm
  have descends := e.isAncestor_anchor_of_known anchored start honest known
  rw [final] at descends
  have path := Store.getAncestor_of_isAncestor_of_lt early found descends
  unfold Store.getCheckpointBlock
  rw [boundaryOk]
  simp only [Except.mapError, bind, Except.bind,
    path, pure, Except.pure, final]

private theorem checkpoint_read_down {store : Store preset fork}
    (early : fork < .glamsterdam) {root middle checkpoint : Root} {epoch prior : Epoch}
    {boundary earlier : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (earlierOk : computeStartSlotAtEpoch preset prior = .ok earlier)
    (ordered : prior ≤ epoch)
    (read : store.getCheckpointBlock root epoch = .ok middle)
    (lower : store.getCheckpointBlock root prior = .ok checkpoint) :
    store.getCheckpointBlock middle prior = .ok checkpoint := by
  have below : earlier ≤ boundary := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [(computeStartSlotAtEpoch_ok_iff.mp earlierOk).2,
      (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp ordered)
  unfold Store.getCheckpointBlock at read lower ⊢
  simp only [boundaryOk, earlierOk, Except.mapError, bind, Except.bind] at read lower ⊢
  cases walked : store.getAncestor ⟨root, .pending⟩ boundary with
  | error err => simp [walked] at read
  | ok node =>
    have pending := Store.getAncestor_pending_of_lt early rfl walked
    simp only [walked, pure, Except.pure, Except.ok.injEq] at read
    have nodeEq : node = ⟨middle, .pending⟩ := by
      cases node
      simp_all
    subst node
    rwa [Store.getAncestor_trans below walked] at lower

omit [DecidablePred (· ∈ J)] in
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
  classical
  by_cases fault : e.AccountableFault history horizon limit ∨ e.HashFault history limit
  · exact .inr fault
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤
      preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by have := parameters.roots; omega
  obtain nonzero | hashes := e.nonzero_or_fault anchored start anchorSlot slots positive
    history forkWindow inHorizon
  · obtain unique | faults := e.oneJustifiedPerEpoch_or_fault anchored sound start anchorSlot
      anchorAtBoundary slots parameters genesis history forkWindow inHorizon historyEnough large
    · left
      intro u honestU w honestW n k boundedN boundedK checkpoint justified ordered high
      have reach := e.reachable (anchorState := anchorState) (anchorBlock := anchorBlock)
        (fun v member => by rw [start v member]; exact .anchor anchored)
      obtain ⟨anchorRoot, rooted, anchorKnown, _, anchorJust, anchorFinal, _, _⟩ :=
        getForkchoiceStore_anchor anchored
      have finalCases := (checkpoint_fields (reach n u honestU) rooted
        (fun c => c = (⟨getCurrentEpoch anchorState, anchorRoot⟩ : Checkpoint) ∨
          getCurrentEpoch anchorState < c.epoch) (.inl rfl) (by
            intro old next prior later
            right
            rcases prior with rfl | prior
            · exact later
            · exact UInt64.lt_trans prior later)).2.1
      have anchorLe : getCurrentEpoch anchorState ≤
          ((e.world n).state u).finalizedCheckpoint.epoch := by
        rcases finalCases with same | later
        · rw [same]
          exact UInt64.le_refl _
        · exact UInt64.le_of_lt later
      by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
      · have sameEpoch : checkpoint.epoch = getCurrentEpoch anchorState :=
          UInt64.le_antisymm old (UInt64.le_trans anchorLe ordered)
        have initial : ((e.world 0).state w).Justified anchor.justifiedCheckpoint := by
          change (e.start w).Justified anchor.justifiedCheckpoint
          rw [start w honestW]
          exact .inl rfl
        have same := unique w honestW w honestW k 0 boundedK
          ((e.monotone_time (Nat.zero_le k)).trans boundedK)
          checkpoint anchor.justifiedCheckpoint justified initial
          (by simpa only [anchorJust] using sameEpoch) high
        have finalSame : ((e.world n).state u).finalizedCheckpoint =
            anchor.finalizedCheckpoint := by
          rcases finalCases with same | later
          · exact same.trans anchorFinal.symm
          · exact ((UInt64.not_le.mpr later) (UInt64.le_trans ordered old)).elim
        rw [finalSame, same, anchorJust]
        have known := (reach k w honestW).anchor_known
        obtain ⟨root, rootOk, found⟩ := known
        rw [rooted, Except.ok.injEq] at rootOk
        subst root
        exact anchor_checkpoint_read anchored start anchorSlot anchorAtBoundary forkWindow.1
          honestW found
      · have laterJ := UInt64.not_le.mp old
        obtain ⟨rootB, stateB, vb, storedB, fieldB⟩ :
            ∃ (root : Root) (state : BeaconState preset fork) (view : TerminalView ⟨fork, state⟩),
              ((e.world k).state w).blockStates[root]? = some state ∧
                checkpoint = view.state.currentJustifiedCheckpoint := by
          rcases justified_origin (reach k w honestW) forkWindow.1 justified with
              ⟨root, _, same⟩ | terminal
          · exact (UInt64.ne_of_lt laterJ (congrArg Checkpoint.epoch same).symm).elim
          · exact terminal
        have checkpointOrigin := fieldB ▸ (view_checkpoint_read (reach k w honestW) sound
          forkWindow.1 positive window (UInt64.le_of_eq anchorSlot)
          (nonzero w honestW k boundedK) storedB vb).2.1
        rcases checkpointOrigin with earlier | ⟨boundaryB, blockB, knownB, boundaryOkB, _, readB⟩
        · exact (old earlier).elim
        obtain ⟨_, checkpointBlock, _, checkpointKnown, _, _⟩ :=
          Store.isAncestor_of_getCheckpointBlock forkWindow.1 readB
        rcases finalCases with finalSame | laterF
        · rw [finalSame, ← anchorFinal]
          exact anchor_checkpoint_read anchored start anchorSlot anchorAtBoundary forkWindow.1
            honestW checkpointKnown
        · obtain ⟨rootA, stateA, va, storedA, fieldA⟩ :
              ∃ (root : Root) (state : BeaconState preset fork) (view : TerminalView ⟨fork, state⟩),
                ((e.world n).state u).blockStates[root]? = some state ∧
                  ((e.world n).state u).finalizedCheckpoint = view.state.finalizedCheckpoint := by
            rcases (reach n u honestU).finalized_origins _ (.inl rfl) with
                ⟨root, _, same⟩ | ⟨root, state, held, field⟩ |
                ⟨root, state, pulled, held, computed, field⟩
            · exact (UInt64.ne_of_lt laterF (congrArg Checkpoint.epoch same).symm).elim
            · exact ⟨root, state, .realized, held, field⟩
            · exact ⟨root, state, .pulled pulled computed, held, field⟩
          have finalOrigin := fieldA ▸ (view_checkpoint_read (reach n u honestU) sound
            forkWindow.1 positive window (UInt64.le_of_eq anchorSlot)
            (nonzero u honestU n boundedN) storedA va).2.2
          rcases finalOrigin with earlier | ⟨boundaryA, blockA, knownA, boundaryOkA, _, readA⟩
          · exact ((UInt64.not_le.mpr laterF) earlier).elim
          obtain ⟨left, enoughA, terminalA, readsA⟩ := held_run_enough anchored start anchorSlot
            slots parameters genesis history forkWindow inHorizon historyEnough large
            honestU boundedN storedA
          obtain ⟨right, enoughB, terminalB, readsB⟩ := held_run_enough anchored start anchorSlot
            slots parameters genesis history forkWindow inHorizon historyEnough large
            honestW boundedK storedB
          have above := e.anchorSlot_le_finalized_boundary anchored anchorSlot anchorAtBoundary
            (start u honestU) boundaryOkA
          have starts : anchorState.slot.toNat ≤
              va.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
            rw [← fieldA, ← (computeStartSlotAtEpoch_ok_iff.mp boundaryOkA).2, ← anchorSlot]
            exact UInt64.le_iff_toNat_le.mp above
          rcases accountable_terminal_finalized_prefix history left right va vb parameters genesis
              forkWindow.1 forkWindow.1 enoughA enoughB (terminalA va) (terminalB vb)
              checkpoint (.inr fieldB) (fieldA ▸ ordered) starts with paths | accountable | hashes
          · rw [← fieldA] at paths
            have tails : left.checkpointPath ((e.world n).state u).finalizedCheckpoint.epoch =
                right.checkpointPath ((e.world n).state u).finalizedCheckpoint.epoch := by
              simp only [Run.checkpointPath, headers_append, List.filter_append] at paths
              exact List.append_cancel_left paths
            have sameRead := (readsB _ _ boundaryOkA above).trans
              ((congrArg (fun path : List BeaconBlockHeader =>
                (path.getLast?.map SszType.hashTreeRoot |>.getD
                  (SszType.hashTreeRoot anchorBlock)).mapError ForkChoiceError.ssz)
                tails.symm).trans ((readsA _ _ boundaryOkA above).symm.trans readA))
            exact checkpoint_read_down forkWindow.1 boundaryOkB boundaryOkA ordered readB sameRead
          · exact (fault (.inl ⟨stateA, stateB, left, right, va, vb, checkpoint,
              ⟨u, honestU, n, rootA, boundedN, storedA⟩,
              ⟨w, honestW, k, rootB, boundedK, storedB⟩,
              .inr (.inr (.inr fieldB)), high, .inl accountable⟩)).elim
          · apply (fault (.inr ?_)).elim
            refine ⟨stateA, stateB, left, right, va, vb,
              ⟨u, honestU, n, rootA, boundedN, storedA⟩,
              ⟨w, honestW, k, rootB, boundedK, storedB⟩, ?_⟩
            exact hash_evidence_mono (fun _ member =>
              List.mem_append_left _ (List.mem_append_left _ member)) hashes
    · exact (fault faults).elim
  · exact (fault (.inr hashes)).elim

omit [DecidablePred (· ∈ J)] in
/-- The blocks that an honest store holds are before the next fork. -/
private theorem blocks_before_fork {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat) {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  have forward := e.forwardReachable (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun v member => by rw [start v member]; exact .anchor anchored) k w honest
  obtain ⟨current, currentOk, blocks, -⟩ := forward.slots_le_current slots
    (by rw [anchorSlot]; exact UInt64.le_refl _)
  have currentEpoch : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp only [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have high := UInt64.le_iff_toNat_le.mp (inHorizon w honest k _ bounded currentEpoch)
  simp only [computeEpochAtSlot, UInt64.toNat_div] at high
  intro root block found next scheduled
  have blockLe := UInt64.le_iff_toNat_le.mp (blocks root block found)
  have nextLt := forkWindow.2 next scheduled
  have positive := parameters.slots
  have currentLt : current.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
  omega

omit [DecidablePred (· ∈ J)] in
/-- The stake that leaves the active set between a source checkpoint state and a head state.

The source is the state of a checkpoint of one honest store.

The head state is a block state of another, and the chain of the head holds the checkpoint block.

The registry of the head state is read at an epoch within two epochs of the source.

Its validators that are active in the source and inactive there fit the reserve of the source. -/
theorem Execution.exitsHead_of_oneBlock {limit : ℕ} {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {g : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (history : Run config checks g ⟨fork, anchorState⟩) {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    (historyEnough : EnoughStake history)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (oneBlock : OneBlockPerRoot e limit)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat) (long : 1 < preset.SLOTS_PER_EPOCH) :
    ∀ u ∈ J, ∀ n (c : Checkpoint) (source : BeaconState preset fork),
      (e.world n).time ≤ limit → ((e.world n).state u).checkpointState c = .ok source →
      ∀ w ∈ J, ∀ k (head : Root) (hs : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).blockStates[head]? = some hs →
      ((e.world k).state w).getCheckpointBlock head c.epoch = .ok c.root →
      ∀ epoch : Epoch, c.epoch ≤ epoch → epoch.toNat ≤ c.epoch.toNat + 2 → epoch ≤ horizon →
      epoch.toNat ≤ (getCurrentEpoch hs).toNat + 1 →
      stake (fun v => balanceAt source v.toNat)
          {v ∈ activeVoters source | isActiveAt hs epoch v.toNat = false} ≤
        exitReserve config source := by
  intro u hu n c source bn sourceOk w hw k head hs bk stored read epoch cle near ehor recent
  have early := forkWindow.1
  have positive : 0 < preset.SLOTS_PER_EPOCH := UInt64.lt_trans (by decide) long
  have longNat : 2 ≤ preset.SLOTS_PER_EPOCH.toNat := UInt64.lt_iff_toNat_lt.mp long
  have reachU : Store.Reachable config anchorState anchorBlock ((e.world n).state u) :=
    e.reachable (fun v hv => (start v hv).symm ▸ Store.Reachable.anchor anchored) n u hu
  have reachW : Store.Reachable config anchorState anchorBlock ((e.world k).state w) :=
    e.reachable (fun v hv => (start v hv).symm ▸ Store.Reachable.anchor anchored) k w hw
  obtain ⟨headBlock, headFound⟩ := reachW.known_of_blockState stored
  obtain ⟨base, boundary, storedBaseU, boundaryOk, bridgeU⟩ :=
    e.checkpointState_fromBlock anchored start hu sourceOk
  obtain ⟨boundary', aBlock, boundaryOk', aFound, aLe, descends⟩ :=
    Store.isAncestor_of_getCheckpointBlock early read
  have sameBoundary : boundary' = boundary := Except.ok.inj (boundaryOk'.symm.trans boundaryOk)
  subst boundary'
  obtain ⟨sa, storedA⟩ : ∃ sa, ((e.world k).state w).blockStates[c.root]? = some sa := by
    obtain ⟨post, postOk, -⟩ := reachW.blockStatesFromParents aFound
    exact ⟨post, postOk⟩
  have baseEq : base = sa := e.blockStates_eq anchored hu hw (start u hu) (start w hw)
    (oneBlock u hu w hw n k bn bk) storedBaseU storedA
  subst baseEq
  have aSlot : base.slot = aBlock.slot := blockState_slot_eq reachW anchorSlot aFound storedA
  have bridge : (base.slot = boundary ∧ source = base) ∨
      (base.slot < boundary ∧ processSlots config checks base boundary = .ok source) := by
    rcases bridgeU with ⟨le, same⟩ | ran
    · exact .inl ⟨UInt64.le_antisymm (aSlot ▸ aLe) le, same⟩
    · exact .inr ran
  have clearC := clear_of_getCheckpointBlock early boundaryOk read aFound
  have before := blocks_before_fork anchored start anchorSlot slots parameters forkWindow
    inHorizon hw bk
  have cEpoch : computeEpochAtSlot preset boundary = c.epoch :=
    computeEpochAtSlot_computeStartSlotAtEpoch positive boundaryOk
  have boundaryNat := computeStartSlotAtEpoch_ok_iff.mp boundaryOk
  have cle' : c.epoch.toNat ≤ epoch.toNat := UInt64.le_iff_toNat_le.mp cle
  have ehor' : epoch.toNat ≤ horizon.toNat := UInt64.le_iff_toNat_le.mp ehor
  have boundaryBefore : ∀ next ∈ config.nextFork fork,
      boundary.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    intro next member
    have below := forkWindow.2 next member
    rw [boundaryNat.2]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have bounded : epoch.toNat < 2 ^ 64 - 1 := by
    have fits := boundaryNat.1
    have double : c.epoch.toNat * 2 ≤ c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
      Nat.mul_le_mul_left _ longNat
    omega
  -- The run from genesis to the source.
  obtain ⟨sourceRun⟩ : Nonempty (Run config checks ⟨fork, base⟩ ⟨fork, source⟩) := by
    rcases bridge with ⟨_, rfl⟩ | ⟨_, ran⟩
    · exact ⟨.nil⟩
    · exact run_of_processSlots ran boundaryBefore
  obtain ⟨headRun, -, -, -⟩ := held_run_enough anchored start anchorSlot slots parameters
    genesis history forkWindow inHorizon historyEnough large hw bk storedA
  have sourceSlot : source.slot = boundary := by
    rcases bridge with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have sourceEpoch : getCurrentEpoch source = c.epoch := by
    simp only [getCurrentEpoch, sourceSlot]
    exact cEpoch
  -- The run from the source to a state whose registry at the epoch is the one of the head state.
  obtain ⟨y, ⟨tail⟩, yLe, registry⟩ : ∃ y : BeaconState preset fork,
      Nonempty (Run config checks ⟨fork, source⟩ ⟨fork, y⟩) ∧ getCurrentEpoch y ≤ epoch ∧
      ∀ position, isActiveAt y epoch position = isActiveAt hs epoch position := by
    by_cases cur : getCurrentEpoch hs ≤ epoch
    · exact run_to_epoch_early anchored early anchorSlot lookahead hw (start w hw) before aFound
        storedA bridge headFound stored descends clearC (cEpoch ▸ cle) boundaryBefore bounded
        recent cur
    · have later : epoch < getCurrentEpoch hs := UInt64.not_le.mp cur
      have headSlot : hs.slot = headBlock.slot :=
        blockState_slot_eq reachW anchorSlot headFound stored
      have above : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
        have step : epoch.toNat + 1 ≤ hs.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp later
          simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at this
          omega
        have := (Nat.le_div_iff_mul_le (by omega)).mp step
        have := hs.slot.toNat_lt
        nlinarith
      obtain ⟨S, SOk⟩ : ∃ S, computeStartSlotAtEpoch preset epoch = .ok S :=
        ⟨UInt64.ofNat (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat),
          computeStartSlotAtEpoch_ok_iff.mpr ⟨above, by
            rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt above]⟩⟩
      have SNat := (computeStartSlotAtEpoch_ok_iff.mp SOk).2
      have boundaryLe : boundary ≤ S := by
        rw [UInt64.le_iff_toNat_le, boundaryNat.2, SNat]
        exact Nat.mul_le_mul_right _ cle'
      have beforeS : ∀ next ∈ config.nextFork fork,
          S.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
        intro next member
        have below := forkWindow.2 next member
        rw [SNat]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      have anchorLe : anchorBlock.slot ≤ S :=
        UInt64.le_trans (reachW.anchorSlot_le_block aFound) (UInt64.le_trans aLe boundaryLe)
      obtain ⟨bE, readE⟩ := e.exists_getCheckpointBlock_of_held anchored start anchorSlot early
        anchorParent hw bk headFound SOk anchorLe
      exact run_to_epoch_late anchored early anchorSlot positive hw (start w hw) before aFound
        storedA bridge headFound stored descends clearC SOk boundaryLe beforeS bounded readE later
  have bound := exitStake_le_exitReserve_epoch genesis ((history.append headRun).append sourceRun)
    tail lookahead early yLe (by rw [sourceEpoch]; exact near)
  simp only [registry] at bound
  exact bound

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
    [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
    [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
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
      ActiveStakeAtMost stakeCapGwei state)
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
  rcases e.oneBlockPerRoot_or_fault anchored start anchorSlot slots
      (by have := parameters.slots; omega) history forkWindow
      inHorizon with oneBlock | fault
  rotate_left
  · exact .inr (.inr fault)
  rcases e.nonzero_or_fault anchored start anchorSlot slots
      (by have := parameters.slots; omega) history forkWindow inHorizon with
    nonzero | fault
  rotate_left
  · exact .inr (.inr fault)
  exact .inl (e.safeAt_confirmedRoot sync half boost slots long window lookahead votes fits prompt
    committees follows forkWindow.1 oneBlock admitted included anchored sound anchorSlot
    anchorAtBoundary start noVotes _syncStart maxAligned increment chain unique byzantine
    unslashed supply
    (e.exitsHead_of_oneBlock anchored start anchorSlot slots parameters genesis history forkWindow
      historyEnough inHorizon large anchorParent oneBlock lookahead.2.1 long)
    positive enough large nonzero headDrifts caller upToDate lower atSlots ran
    bounds inHorizon anchorParent lastCall slotOk nextOk followingOk nonempty)

end EthLib.Consensus.Models.Network
