module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints

/-!
# Statements: a block that the rule confirms stays in the filtered tree of each honest store

This file states step 6 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

The fork choice of a store filters out a block when no leaf above it has a recent voting source.

The rule confirms a block after checks on the checkpoints of its head, and this file names them.

The first statement reads those checks off a call of the rule.

The second bounds the count that the rule makes for the target of its epoch.

Honest validators hold that count: each has voted for the target or has still to vote.

It reads the store of the caller alone, and takes no safety of the target.

The third gives the result, for each honest store at a later time.

It holds the confirmed block in its filtered tree, or its justified block is above that block.

The third statement takes the facts of Casper FFG as hypotheses, with a horizon and a margin.

An honest validator that has still to vote signs the target of its head at its own slot.

Before the later time the block is safe, so that target is on the chain of the block.

So a checkpoint that an honest third signs cannot conflict with the block.

It also takes Assumption 3 of the paper, in the form that `TargetIncluded` gives it here.

The result is a theorem of [verified-fast-confirmation][vfc].

It is `Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

There one registry weighs each count, so a third of the stake is the same in each state.

Here the margin covers the change of the balances between the states of two counts.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The checks that the rule has passed when it confirms a block after the one it starts from.

The start is in the current epoch or the one before.

A block of the current epoch after a start of the epoch before needs the target to be justified.

Away from the start of the epoch, such a block needs more.

The unrealized justification of the head must be recent.

A block of the epoch before needs a recent voting source.

That source is the one of the block, or the one of the head of the slot before.

In the second case the block is on the chain of that head.

Away from the start of the epoch, it also needs that no conflicting checkpoint can be justified.

Then the head, or the head of the slot before, has a recent unrealized justification. -/
def Checked (store : Store preset fork) (config : Config) (fcr : FastConfirmationStore)
    (head start root : Root) : Prop :=
  ∃ epoch slot rootEpoch startEpoch,
    store.getCurrentStoreEpoch config = .ok epoch ∧ store.getCurrentSlot config = .ok slot ∧
    store.getBlockEpoch root = .ok rootEpoch ∧ store.getBlockEpoch start = .ok startEpoch ∧
    epoch.toNat ≤ startEpoch.toNat + 1 ∧
    ((startEpoch.toNat + 1 = epoch.toNat ∧ rootEpoch ≠ epoch ∧
      (∃ source, store.getVotingSource config fcr.previousSlotHead = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2 ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨root, .pending⟩ = .ok true) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
        ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
          store.unrealizedJustification tip = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1)) ∨
      ((isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      (rootEpoch = epoch → startEpoch ≠ epoch →
        store.willCurrentTargetBeJustified config head = .ok true) ∧
      (rootEpoch ≠ epoch →
        (∃ source, store.getVotingSource config root = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2) ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true))))

/-- Step 6, the checks: the latest confirmed block is a start, or has passed the checks.

The start is the block stored before, the finalized block or the observed justified block.

Each known block must sit at a later slot than its known parent.

The proof reads the two walks of the rule, as `findLatestConfirmedDescendant_eq_or` does.

Two witnesses of [verified-fast-confirmation][vfc] hold the same checks.

They are `PreviousSelectedEntryWitness` and `TentativeSelectedResultWitness`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem getLatestConfirmed_checked {fcr : FastConfirmationStore} {head root : Root}
    (lower : store.ParentsBelow)
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ start, (start = fcr.confirmedRoot ∨ start = store.finalizedCheckpoint.root ∨
        start = fcr.currentEpochObservedJustifiedCheckpoint.root) ∧
      (root = start ∨ store.Checked config fcr head start root) := by
  sorry

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- Honest validators hold the count that the rule makes for the target of a head, with a margin.

The store is that of a validator at an event, and the head is a block of it.

The rule counts the honest votes that the target of the current epoch will get, at the least.

Some honest validators are active in the pulled-up state of the head.

Each has signed a vote with that target, or is in no committee of the epoch so far.

Three times their stake is at least three times the count plus the margin.

The stake is read in the pulled-up state of the head.

In [verified-fast-confirmation][vfc], `noConflict_arithmeticBranch_oneThird` gives this set.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def HonestTargetVotes
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (margin : ℕ) (u : ValidatorIndex) (n : ℕ) (head : Root) : Prop :=
  ∀ state support target slot epochStart lastSlot participants,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    ((e.world n).state u).computeHonestFfgSupportForCurrentTarget config head = .ok support →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
    subChecked slot 1 = .ok lastSlot →
    ((e.world n).state u).getCommitteesBetweenSlots head epochStart lastSlot = .ok participants →
    ∃ voters : Finset ValidatorIndex,
      (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
        (SignsTarget e v target ∨ v ∉ participants)) ∧
      3 * support.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters

/-- Assumption 3 of the paper: a target with an honest quorum is included within an epoch.

An honest store counts honest votes for the checkpoint of an epoch on the chain of a block.

Two thirds of the active balance of the pulled-up state of a head sign that target.

The block is safe from a first time on.

Take an honest store that is up to date at that time or later.

Its epoch is two epochs after the target or later.

It holds a block above the given one, of an epoch before that, with the target included.

Included means that the unrealized justification of that block is not before the target.

In [verified-fast-confirmation][vfc], this is `EventualCheckpointInclusion.included`.

Its conclusion there is `A32IncludedAtTip`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetIncluded
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ u ∈ J, ∀ n head state total root rootEpoch target, ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
    rootEpoch ≤ target.epoch →
    ((e.world n).state u).getCheckpointBlock root target.epoch = .ok target.root →
    (∀ v ∈ voters, v ∈ J ∧ SignsTarget e v target) →
    2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k current, (e.world n).time ≤ (e.world k).time →
      (∀ time, (e.world n).time ≤ time → time < (e.world k).time → SafeAt e time root) →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
      target.epoch.toNat + 2 ≤ current.toNat →
      ∃ (seed : Root) (seedBlock : BeaconBlock preset fork) (justification : Checkpoint),
        ((e.world k).state w).blocks[seed]? = some seedBlock ∧
        ((e.world k).state w).isAncestor ⟨seed, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
        (computeEpochAtSlot preset seedBlock.slot).toNat < target.epoch.toNat + 2 ∧
        ((e.world k).state w).unrealizedJustifications[seed]? = some justification ∧
        target.epoch.toNat ≤ justification.epoch.toNat

/-- A block extends an origin whose target the rule checked in the block's epoch.

The origin and the block have the same epoch, which can precede the current epoch.

The anchor is an origin without a target check.

For any other origin, an earlier up-to-date call checked a head above that origin.

There the rule found that the target of the epoch will be justified.

Honest validators held the count of the rule for that target, with the margin.

The origin is safe from that event to the later one.

A later block need not have existed at the event that checked the origin.

A call of the rule makes that check only when it enters the epoch.

A later call that starts from a block of the epoch relies on the earlier check.

In [verified-fast-confirmation][vfc], `AcceptedHistoricalA32CurrentLineageAt` holds this record.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetChecked
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (margin : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (epoch : Epoch) (root : Root) : Prop :=
  ∃ k ≤ n, ∃ origin,
    ((e.world n).state u).getBlockEpoch root = .ok epoch ∧
    ((e.world n).state u).getBlockEpoch origin = .ok epoch ∧
    ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
    (origin = anchorRoot ∨ ∃ head,
      UpToDate config checks sources (e.world k).time ((e.world k).view u) ((e.world k).state u) ∧
      ((e.world k).state u).getCurrentStoreEpoch config = .ok epoch ∧
      ((e.world k).state u).getHead config = .ok head ∧
      ((e.world k).state u).willCurrentTargetBeJustified config head.root = .ok true ∧
      ((e.world k).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
      HonestTargetVotes e margin u k head.root) ∧
    ∀ time, (e.world k).time ≤ time → time ≤ (e.world n).time → SafeAt e time origin

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

/-- Step 6, the count: honest validators hold the count of the rule for the target, with a margin.

The caller is an honest validator, and each honest store starts from the store of the anchor.

Each latest vote of an honest validator in the store of the caller is a vote that it signed.

The Byzantine validators hold at most β of the committees of the epoch so far, Assumption 2.

So the votes for the target less the weight of the adversary are honest votes.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

The stake is read in the pulled-up state of the head.

The statement reads the store of the caller alone, and takes no safety of the target.

The proof follows two lemmas of [verified-fast-confirmation][vfc].

The first is `noConflict_arithmeticBranch_oneThird`.

The second is `currentTarget_remaining_honest_le_future_weight`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honestTargetVotes_of_byzantineStakeAtMost {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (committees : CommitteesFollow e) {margin : ℕ}
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    {head : Root} {state : BeaconState preset fork}
    {slot epochStart lastSlot : Slot} {total soFar : Gwei}
    {participants : Std.TreeSet ValidatorIndex}
    (headOk : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (totalOk : getTotalActiveBalance state = .ok total)
    (aligned : EffectiveBalancesAligned state)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (startOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (soFarOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head state epochStart
      lastSlot = .ok soFar)
    (participantsOk : ((e.world n).state u).getCommitteesBetweenSlots head epochStart lastSlot =
      .ok participants)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      (Store.activeMembers state participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (dishonest : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J)
    (remaining : 3 * ((total.toNat - soFar.toNat) / 100 *
        (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat)) + margin ≤
      3 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∉ participants ∧ v ∈ J}) :
    HonestTargetVotes e margin u n head := by
  sorry

/-- Step 6, the result: a block that passed the checks is not filtered out at a later time.

The caller is an honest validator whose store is up to date, and its rule passed the checks.

The block is on the chain of the head of the caller.

The head of the slot before, as the rule tracks it, was a head of the store of the caller.

Honest validators hold the count of the rule for the target of the head, with the margin.

Each has voted for that target or has still to vote in the epoch.

A start of the current epoch is the block of the anchor, or the rule checked its target before.

From the call to just before the later time, the block is safe.

The start of the rule is safe from the call to the later time.

Up to the horizon, two justified checkpoints of one epoch are the same.

An honest third, with the margin, signs each justified checkpoint of its epoch.

Each justified checkpoint after the anchor, up to the horizon, has an honest vote.

Slots last a positive time, so an honest validator signs one target in an epoch.

A target with an honest quorum is included within an epoch, Assumption 3.

Each honest store up to the later time is in an epoch at most the horizon.

Then each honest store at the later time holds the block in its filtered tree.

Otherwise its justified block is above the block.

The proof follows a theorem of [verified-fast-confirmation][vfc] and the lemmas under it.

It is `Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.coveredOrViableAt_of_checked {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (oneBlock : OneBlockPerRoot e)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e)
    {horizon anchorEpoch : Epoch} {margin : ℕ}
    (unique : OneJustifiedPerEpoch e horizon) (pins : HonestThirdPins e anchorEpoch horizon margin)
    (voted : JustifiedByHonestVote e anchorEpoch horizon) (included : TargetIncluded e)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (onChain : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true)
    (atStart : ∀ slot rootEpoch epoch,
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok true →
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
      rootEpoch = epoch → root = ((e.world n).state u).finalizedCheckpoint.root)
    (previousHead : fcr.previousSlotHead = anchor.finalizedCheckpoint.root ∨
      ∃ k < n, ∃ previous previousSlot currentSlot,
        UpToDate config checks sources (e.world k).time ((e.world k).view u)
          ((e.world k).state u) ∧
        ((e.world k).state u).getHead config = .ok previous ∧
        previous.root = fcr.previousSlotHead ∧
        ((e.world k).state u).getCurrentSlot config = .ok previousSlot ∧
        ((e.world n).state u).getCurrentSlot config = .ok currentSlot ∧
        addChecked previousSlot 1 = .ok currentSlot)
    (targetVotes : HonestTargetVotes e margin u n head.root)
    (lineage : ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getBlockEpoch start = .ok epoch →
      TargetChecked e margin anchor.finalizedCheckpoint.root u n epoch start)
    (previousLineage : ∀ epoch previous slot,
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok true → addChecked previous 1 = .ok epoch →
      ((e.world n).state u).getBlockEpoch start = .ok previous →
      TargetChecked e margin anchor.finalizedCheckpoint.root u n previous start ∨
        (((e.world n).state u).unrealizedJustification head.root =
          .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
          start = fcr.currentEpochObservedJustifiedCheckpoint.root))
    {time : ℕ} (later : (e.world n).time ≤ time)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (startSafe : ∀ earlier, (e.world n).time ≤ earlier → earlier ≤ time → SafeAt e earlier start)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    (known : ∀ w ∈ J, ∀ k, (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ∃ block, ((e.world k).state w).blocks[root]? = some block) :
    CoveredOrViableAt e time root := by
  sorry

end Models.Network

end EthLib.Consensus
