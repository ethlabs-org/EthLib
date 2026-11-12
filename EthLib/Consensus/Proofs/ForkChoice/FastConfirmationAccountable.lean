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
    ∃ run : Run config checks ⟨fork, state⟩ ⟨fork, after⟩, EnoughStake run := by
  induction count generalizing state with
  | zero =>
    cases advanced
    refine ⟨.nil, ?_⟩
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
    obtain ⟨tail, enough⟩ := ih ((Run.nil.snoc (.slot across)).unique unique) rest
      (fun i current small run => large (i + 1) current (by omega)
        (by simp only [advanceSlots, stepped, bind, Except.bind]; exact run))
    exact ⟨(Run.nil.snoc (.slot across)).append tail,
      enough_append (enough_slot early unique across (large 0 state (by omega) rfl)) enough⟩

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
    ∃ run : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩, EnoughStake run := by
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
    refine ⟨.nil, ?_⟩
    rintro ⟨_, _, _, member, _⟩
    cases member
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored same
    obtain ⟨pre, preEnough⟩ :=
      run_enough_of_blockState anchored unique early honest start before large parentFound
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
    obtain ⟨tail, tailEnough⟩ := run_enough_of_advanceSlots _ early (pre.unique unique)
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
    refine ⟨pre.append (tail.snoc (.block sources.engine signed due applied)), ?_⟩
    apply enough_append preEnough
    intro call
    rcases call with ⟨before, after, advanced, member, boundary, cached, weighed,
      cachedOk, weighedOk, later⟩
    cases member with
    | earlier member =>
      exact tailEnough ⟨before, after, advanced, member, boundary, cached, weighed,
        cachedOk, weighedOk, later⟩
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
      EnoughStake (history.append run) ∧ ∀ view : TerminalView ⟨fork, state⟩, view.enough := by
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
  obtain ⟨run, enough⟩ := run_enough_of_blockState anchored
    (history.unique (genesis_unique genesis)) forkWindow.1 honest (start w honest)
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
  refine ⟨run, enough_append historyEnough enough, ?_⟩
  intro view
  cases view with
  | realized => trivial
  | pulled after computed =>
    intro _
    rw [active_weight_eq_stake forkWindow.1 ((history.append run).unique (genesis_unique genesis))]
    exact countLarge state ⟨root, state, stored, .inl rfl⟩

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

private theorem justified_zero {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) {anchorRoot : Root}
    (rooted : SszType.hashTreeRoot anchorBlock = .ok anchorRoot)
    {checkpoint : Checkpoint} (justified : store.Justified checkpoint)
    (zero : checkpoint.epoch = 0) :
    checkpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ := by
  let P := fun (s : Store preset fork) =>
    (s.justifiedCheckpoint.epoch = 0 →
      s.justifiedCheckpoint = (⟨getCurrentEpoch anchorState, anchorRoot⟩ : Checkpoint)) ∧
    (s.unrealizedJustifiedCheckpoint.epoch = 0 →
      s.unrealizedJustifiedCheckpoint = (⟨getCurrentEpoch anchorState, anchorRoot⟩ : Checkpoint))
  have update (s : Store preset fork) j f (old : P s) : P (s.updateCheckpoints j f) := by
    unfold Store.updateCheckpoints
    split
    · rename_i later
      have nonzero : j.epoch ≠ 0 := by
        intro eq
        rw [eq] at later
        exact UInt64.not_lt_zero later
      dsimp only
      split <;> exact ⟨fun eq => (nonzero eq).elim, old.2⟩
    · dsimp only
      split <;> exact old
  have pending (s : Store preset fork) j f (old : P s) : P (s.updateUnrealizedCheckpoints j f) := by
    unfold Store.updateUnrealizedCheckpoints
    split
    · rename_i later
      have nonzero : j.epoch ≠ 0 := by
        intro eq
        rw [eq] at later
        exact UInt64.not_lt_zero later
      dsimp only
      split <;> exact ⟨old.1, fun eq => (nonzero eq).elim⟩
    · dsimp only
      split <;> exact old
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
    clear justified
    induction reachable with
    | anchor made =>
      obtain ⟨root, rootOk, _, _, real, _, unrealized, _⟩ := getForkchoiceStore_anchor made
      rw [rooted, Except.ok.injEq] at rootOk
      subst root
      exact ⟨fun _ => real, fun _ => unrealized⟩
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
    · obtain ⟨left, enoughA, terminalA⟩ := held_run_enough anchored start anchorSlot slots
        parameters genesis history forkWindow inHorizon historyEnough large honestU boundedN storedA
      obtain ⟨right, enoughB, terminalB⟩ := held_run_enough anchored start anchorSlot slots
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
  exact .inl (e.safeAt_confirmedRoot sync half slots long window lookahead votes fits prompt
    committees follows forkWindow.1 oneBlock admitted included anchored sound anchorSlot
    anchorAtBoundary start noVotes _syncStart maxAligned increment chain unique byzantine
    unslashed supply positive enough large nonzero headDrifts caller upToDate lower atSlots ran
    bounds inHorizon anchorParent lastCall slotOk nextOk followingOk nonempty)

end EthLib.Consensus.Models.Network
