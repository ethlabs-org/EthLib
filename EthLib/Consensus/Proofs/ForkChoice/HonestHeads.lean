module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport

/-!
# The head of an honest store

The store of an honest validator computes a head at each event up to a last time.

Before Gloas the head computation reads the cached state of the justified checkpoint.

It reads the filtered block tree, the tally of the latest votes in that state, and the boost.

Each read succeeds in a store that honest moves build from an anchor.

The justified checkpoint state is cached, because an honest store imports a block together with
its votes, and each vote caches the state of its target.

Every walk down the parents of a block stops at or above the anchor.

A held block has its parent held, at a lower slot, and the anchor's parent is not held.

The sums of balances stay below `2^64` because each checkpoint state that an honest store reads
has at most `stakeCapGwei` of active stake.

The boost is at most a committee's weight, because its percentage is at most 100.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The boost of a timely block fits below the cap when the active stake does.

The total that the boost reads is that of the unslashed active validators, or one increment.

The active stake bounds the first, and the increment is at most the cap.

At least two slots split the total, and the percentage of the boost is at most 100. -/
theorem computeProposerScore_le_stakeCap {state : BeaconState preset fork}
    (stakeLe : ActiveStakeAtMost stakeCapGwei state)
    (floor : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCapGwei)
    (long : 1 < preset.SLOTS_PER_EPOCH) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100) :
    ∃ score, computeProposerScore config state = .ok score ∧ score.toNat ≤ stakeCapGwei := by
  sorry

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- An honest store holds the block of its justified checkpoint, up to a last time.

The checkpoint is the anchor's, or the root that a held state records for its epoch.

That root is the root of a held block, the latest of that chain at or before the first slot.

A nonzero state root fills the header of each held block only once. -/
theorem Execution.justifiedRoot_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ block, ((e.world k).state w).blocks[((e.world k).state w).justifiedCheckpoint.root]? =
      some block := by
  sorry

/-- An honest store caches the state of its justified checkpoint, and can count with it.

The anchor's checkpoint is cached when the store is built.

A later justified checkpoint has an epoch above the anchor's, so a vote of a held block targets it.

The store imported that block with its votes, and each vote cached the state of its target.

The state is that of the checkpoint block, or its slots up to a held child, so the store counts
with it.

A positive increment makes the count of a justified checkpoint positive. -/
theorem Execution.exists_justified_checkpointState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ state, ((e.world k).state w).checkpointState
        ((e.world k).state w).justifiedCheckpoint = .ok state ∧
      ((e.world k).state w).Counts config state := by
  sorry

/-- An honest store reads whether one held block descends from another.

The walk goes down the parents of the first block while they are above the second one's slot.

Each parent is held and at a lower slot, and the anchor's parent is not held. -/
theorem Execution.exists_isAncestor_of_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {root ancestor : Root} {block ancestorBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    (ancestorKnown : ((e.world k).state w).blocks[ancestor]? = some ancestorBlock) :
    ∃ result, ((e.world k).state w).isAncestor ⟨root, .pending⟩ ⟨ancestor, .pending⟩ =
      .ok result := by
  sorry

/-- An honest store reads the checkpoint block of a held block at an epoch after the anchor's slot.

The walk stops at the first slot of the epoch, at or above the anchor. -/
theorem Execution.exists_getCheckpointBlock_of_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    {epoch : Epoch} {first : Slot} (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (above : anchorBlock.slot ≤ first) :
    ∃ checkpointRoot, ((e.world k).state w).getCheckpointBlock root epoch = .ok checkpointRoot := by
  sorry

/-- An honest store reads its filtered block tree, up to a last time.

Each leaf has a voting source, from the state or the unrealized justification of its block.

The source epoch is at most the current epoch, which two more epochs leave within 64 bits.

Each leaf reads its checkpoint block at the finalized epoch, at or above the anchor. -/
theorem Execution.exists_getFilteredNodeTree {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ nodes, ((e.world k).state w).getFilteredNodeTree config = .ok nodes := by
  sorry

/-- An honest store counts the latest votes for a held block in a state with capped stake.

Before Gloas each vote supports the pending node of its block, which the store holds.

The sum is that of active validators, so it stays within the cap. -/
theorem Execution.exists_scoreFromTally {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {state : BeaconState preset fork} (stakeLe : ActiveStakeAtMost stakeCapGwei state)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block) :
    ∃ score, ((e.world k).state w).scoreFromTally (((e.world k).state w).tallyVotes state)
      ⟨root, .pending⟩ = .ok score ∧ score.toNat ≤ stakeCapGwei := by
  sorry

/-- The store of an honest validator computes a head at each event up to a last time.

The justified checkpoint state is cached and counts, so its active stake is at most the cap.

The bound on counting states then puts one increment below the cap too.

The filtered tree, each tally and the boost are then read, and each weight fits in 64 bits.

The boosted block, when there is one, is held. -/
theorem Execution.exists_getHead {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100) {limit : ℕ} {horizon : Epoch}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ head, ((e.world k).state w).getHead config = .ok head := by
  sorry

end EthLib.Consensus.Models.Network
