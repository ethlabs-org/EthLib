module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCheckpoints

/-!
# Late coverage of a block of the call's own epoch

A call of the rule in epoch `E` that confirms a block of epoch `E` makes it safe until later.

A store that is two or more epochs after the block holds it in its filtered tree.

Otherwise its justified block is above the block.

The counted honest voters sign the target before the next epoch, and Assumption 3 includes them.

Their votes reach a leaf above the block, which then has a voting source of epoch `E`.

`Execution.coveredOrViableAt_of_checked` takes this as its hypothesis `currentLate`. -/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J} [DecidablePred (· ∈ J)]

/-- A block of the call's own epoch stays covered or viable for each later receiver.

The receiver is two or more epochs after the block, and its justified block is below it.

The hypotheses are those of `Execution.coveredOrViableAt_of_checked`. -/
theorem Execution.coveredOrViableAt_late_current {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (oneBlock : OneBlockPerRoot e time)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (committees : CommitteesFollow e time)
    (follows : HeadFollowsSupport e time)
    {horizon anchorEpoch : Epoch} {margin : ℕ}
    (chain : FinalizedPrefix e horizon time)
    (unique : OneJustifiedPerEpoch e horizon time)
    (pins : HonestThirdPins e anchorEpoch horizon margin time)
    (voted : JustifiedByHonestVote e anchorEpoch horizon time) (included : TargetIncluded e time)
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
    (atSlot : ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
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
    (targetVotes : ∀ slot, ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false → ∀ state target anc,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u n head.root)
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
    (later : (e.world n).time ≤ time)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    (quorumDrifts : ∀ u ∈ J, ∀ n (head : Root) (pulled anc : BeaconState preset fork)
        (target : Checkpoint),
      (e.world n).time ≤ time →
      ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
      ((e.world n).state u).getCurrentTarget config head = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      ∀ w ∈ J, ∀ k (root : Root) (rootState state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).blockStates[root]? = some rootState →
      ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
      (state = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok state) →
      target.epoch ≤ getCurrentEpoch state →
      (getCurrentEpoch state).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch state ≤ horizon →
      ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
      (∀ v ∈ voters, v ∈ activeVoters pulled ∧ NotSlashed state v) →
      getTotalActiveBalance state = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
      2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
        2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
          quorumReserve config pulled anc)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (long : 1 < preset.SLOTS_PER_EPOCH) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    (startSafe : ∀ earlier, (e.world n).time ≤ earlier → earlier ≤ time → SafeAt e earlier start)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    (known : ∀ w ∈ J, ∀ k, (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ∃ block, ((e.world k).state w).blocks[root]? = some block)
    (realized : ((e.world n).state u).RealizedRecent [root])
    (rootRecent : ∀ epoch block, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).blocks[root]? = some block →
      epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (realizedHead : ∀ epoch block, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).blocks[root]? = some block →
      computeEpochAtSlot preset block.slot < epoch →
      ∃ headState, ((e.world n).state u).blockStates[head.root]? = some headState ∧
        ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true ∧
        computeEpochAtSlot preset block.slot ≤ headState.currentJustifiedCheckpoint.epoch)
    (sourceLe : ∀ w ∈ J, ∀ k (tip : Root) (source : Checkpoint), (e.world k).time = time →
      getCurrentEpoch anchorState ≤ ((e.world k).state w).justifiedCheckpoint.epoch →
      ((e.world k).state w).getVotingSource config tip = .ok source →
      source.epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch)
    (genesis : ∀ w ∈ J, ∀ i, ((e.world i).state w).genesisTimeMs = genesisTimeMs) :
    ∀ w ∈ J, ∀ k nodes (rootBlock : BeaconBlock preset fork) (slot current : Slot),
      (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
      ((e.world n).state u).blocks[root]? = some rootBlock →
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      computeEpochAtSlot preset rootBlock.slot = computeEpochAtSlot preset slot →
      ((e.world k).state w).getCurrentSlot config = .ok current →
      (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
        (computeEpochAtSlot preset current).toNat →
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true →
      ((e.world k).state w).isAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
        (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes := by
  sorry

end Models.Network

end EthLib.Consensus
