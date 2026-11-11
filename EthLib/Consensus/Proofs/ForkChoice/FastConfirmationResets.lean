module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCheckpoints

/-!
# Statements: the blocks that the fast confirmation rule falls back to are safe

This file states step 7 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

A call of the rule starts from one of three blocks.

They are the block stored before, the finalized block and the observed justified block.

The block stored before needs no statement here.

The induction of step 8 keeps it safe from one call to the next.

The finalized block of an honest store is safe one delay after the store holds it.

By then each honest store holds a justified checkpoint of that epoch or a later one.

The finalized block is on the chain of that checkpoint, and the head is above it.

So the finalized block is not safe at the call itself.

The rule confirms a later block only after a recent start.

A finalized checkpoint after that of the anchor is two epochs old, so its block is not recent.

Then the start is the block of the anchor, which is safe at each time.

The observed justified block is safe from the call that falls back to it.

The call is at the start of an epoch.

The checkpoint was the unrealized justification of the caller one delay before.

By the call, each honest store holds a justified checkpoint of that epoch or a later one.

At the same epoch the two checkpoints are the same.

A later one has the vote of an honest validator, of a time after the call.

That validator had the observed block on the chain of its head, by induction on the time.

Its target is then above the observed block, since that block is of the epoch before.

The statements take the facts of Casper FFG as hypotheses, with a horizon.

They also take three facts on the blocks of honest stores, which `BlocksArrive` holds.

Six lemmas of [verified-fast-confirmation][vfc] give these results.

The first is `finalized_epoch_le_voter_justified_of_receiver_slot_le`.

The second is `finalizedReset_safeFrom_of_nextSlotSynchrony`.

The third is `finalizedResetCandidateInput_safeFrom_anchor_of_recent`.

The fourth is `deadline_justified_epoch_le_of_carrier`.

The fifth is `ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`.

The sixth is `trustedAnchor_safeFrom_of_acceptedGlobalTrajectory`.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The facts on blocks that let a block of an honest store reach each honest store.

They are the hypotheses of `Execution.blocks_of_synchronous`, for each pair of honest stores.

No statement of this plan proves them. -/
structure BlocksArrive
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (Δ : ℕ) : Prop where
  /-- Two honest stores hold the same block at a root that both hold. -/
  sameBlocks : ∀ v ∈ J, ∀ u ∈ J, ∀ n k (root : Root) left right,
    ((e.world n).state v).blocks[root]? = some left →
    ((e.world k).state u).blocks[root]? = some right → left = right
  /-- An honest store takes a signed block of its view that passes the checks of a new block. -/
  accepts : ∀ u ∈ J, ∀ k signedBlock blockRoot state, .block signedBlock ∈ (e.world k).view u →
    SszType.hashTreeRoot signedBlock.message = .ok blockRoot →
    ((e.world k).state u).validateOnBlock config checks sources signedBlock blockRoot =
      .ok state →
    ∃ after, ((e.world k).state u).onBlockWithVotes config checks sources signedBlock = .ok after
  /-- From Gloas, an up-to-date honest store has verified each payload verified a delay before. -/
  payloads : ∀ gloas : .glamsterdam ≤ fork, ∀ v ∈ J, ∀ u ∈ J, ∀ n k parent,
    (e.world n).time + Δ ≤ (e.world k).time →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    ((e.world n).state v).isPayloadVerified gloas parent = true →
    ((e.world k).state u).isPayloadVerified gloas parent = true

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- The block of the anchor is safe at each time.

Each honest store starts as the store of the anchor.

Each block of such a store is the block of the anchor or is above it. -/
theorem Execution.safeAt_anchor {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (time : ℕ) :
    SafeAt e time anchor.finalizedCheckpoint.root := by
  sorry

/-- The finalized checkpoint of an honest store is that of the anchor, or is two epochs old.

No checkpoint of the state of the anchor is of a later epoch than that state.

A state finalizes a checkpoint of the epoch before its own at the latest.

The store takes that checkpoint from a block of an epoch before its own. -/
theorem Execution.finalizedCheckpoint_eq_or_add_two_le {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : CheckpointsNotAhead anchorState)
    {u : ValidatorIndex} (honest : u ∈ J) (start : e.start u = anchor) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint ∨
      ((e.world n).state u).finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat := by
  sorry

/-- Step 7, the recent start: the rule confirms a block after the finalized one of the anchor only.

The rule has passed its checks from the finalized block of an honest store to a later block.

The checks ask for a start of the current epoch or the one before.

A finalized checkpoint after that of the anchor is two epochs old, and its block is older.

So the finalized checkpoint of the store is that of the anchor. -/
theorem Execution.finalizedCheckpoint_eq_of_checked {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : CheckpointsNotAhead anchorState)
    {u : ValidatorIndex} (honest : u ∈ J) (start : e.start u = anchor) {n : ℕ}
    {fcr : FastConfirmationStore} {head root : Root}
    (checked : ((e.world n).state u).Checked config fcr head
      ((e.world n).state u).finalizedCheckpoint.root root) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint := by
  sorry

/-- A delay later, each honest store has justified the epoch that an honest store finalized.

The first store is that of an honest validator at an event, in an epoch at most the horizon.

The receiver is an honest validator whose store is up to date one delay later or more.

The first store took its finalized checkpoint from a block that it holds.

The receiver holds that block, when its own finalized checkpoint is on the chain of the block.

Otherwise its finalized checkpoint is of a later epoch, and so is its justified one.

The proof uses the finalized chain to place the finalized checkpoint of the receiver. -/
theorem Execution.finalized_epoch_le_justified_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (arrive : BlocksArrive e Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : CheckpointsNotAhead anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) :
    ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  sorry

/-- Step 7, the finalized block: it is safe from one delay after an honest store holds it.

The store is that of an honest validator at an event.

Each honest store up to the last time is in an epoch at most the horizon.

A delay later, each honest store has justified the finalized epoch or a later one.

The finalized block is on the chain of that justified block, by the finalized chain.

The head of a store is above its justified block. -/
theorem Execution.safeAt_finalized {Δ : ℕ} (sync : e.Synchronous Δ)
    (arrive : BlocksArrive e Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : CheckpointsNotAhead anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time + Δ ≤ time → time ≤ limit →
      SafeAt e time ((e.world n).state u).finalizedCheckpoint.root := by
  sorry

/-- In the next epoch, each honest store has justified what an honest store saw as justified.

The first store is that of an honest validator at an event, in an epoch at most the horizon.

Its unrealized justified checkpoint is the one that the rule records at the end of an epoch.

The receiver is an honest validator whose store is up to date one delay later or more.

The receiver is in a later epoch than the first store.

The first store took the checkpoint from a block that it holds, of its epoch or before.

The receiver holds that block, when its own finalized checkpoint is on the chain of the block.

In a later epoch the receiver takes the unrealized justification of the block as justified.

Otherwise its finalized checkpoint is of a later epoch than the checkpoint. -/
theorem Execution.unrealized_epoch_le_justified_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (arrive : BlocksArrive e Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : CheckpointsNotAhead anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch later : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (laterOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok later)
    (next : epoch < later) :
    ((e.world n).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  sorry

/-- Step 7, the observed justified block: it is safe from the start of the epoch after it.

The caller is an honest validator, at an event of the start of the first slot of an epoch.

At an earlier event, in the epoch before, its store held an unrealized justified checkpoint.

That event is one delay before the call or more.

The rule records that checkpoint at the last slot of an epoch, and reads it at the next call.

The block of the checkpoint is of the epoch before that of the call.

Up to the horizon, the facts of Casper FFG hold.

The finalized block of an honest store is on the chain of each later justified checkpoint.

Two justified checkpoints of one epoch are the same.

Each justified checkpoint after the anchor has an honest vote.

Each honest store up to the last time is in an epoch at most the horizon.

Then the block of the checkpoint is safe from the call to the last time.

The rule also asks that the checkpoint is the unrealized justification of its head.

The statement does not take that fact. -/
theorem Execution.safeAt_observed {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (votes : Votes e.startTime e)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e)
    (arrive : BlocksArrive e Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : CheckpointsNotAhead anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    (unique : OneJustifiedPerEpoch e horizon)
    (voted : JustifiedByHonestVote e anchor.justifiedCheckpoint.epoch horizon)
    {u : ValidatorIndex} (caller : u ∈ J) {m n : ℕ}
    (recorded : (e.world m).time + Δ ≤ (e.world n).time)
    {previous epoch : Epoch} {slot : Slot} {begin : UInt64}
    {observedBlock : BeaconBlock preset fork}
    (previousOk : ((e.world m).state u).getCurrentStoreEpoch config = .ok previous)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (next : addChecked previous 1 = .ok epoch)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (isStart : isStartSlotAtEpoch preset slot = .ok true)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atStart : (e.world n).time = begin.toNat)
    (found : ((e.world n).state u).block
      ((e.world m).state u).unrealizedJustifiedCheckpoint.root = .ok observedBlock)
    (blockEpoch : addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch)
    {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time ((e.world m).state u).unrealizedJustifiedCheckpoint.root := by
  sorry

end EthLib.Consensus.Models.Network
