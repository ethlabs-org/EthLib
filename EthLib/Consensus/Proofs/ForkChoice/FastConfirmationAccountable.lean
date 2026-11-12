module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety
public import EthLib.Consensus.Proofs.ForkChoice.AccountableCheckpoints
public import EthLib.Consensus.Proofs.DirectSafety.TerminalSafety

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

open Base Uint64 Models DirectSafety

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

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

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
