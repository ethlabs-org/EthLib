module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationDuties
public import EthLib.Consensus.Proofs.ForkChoice.PendingCommittees
public import EthLib.Consensus.Proofs.ForkChoice.TargetJustification

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

omit [DecidablePred (· ∈ J)] in
/-- A root of the call's own epoch has a target check of that epoch at or before the call.

Its start is of the epoch before, and the call itself checked the target.

Or its start is of the same epoch, and the record of the start serves for the root above it. -/
private theorem late_root_checked {anchorRoot : Root} {margin : ℕ}
    (preGloas : fork < .glamsterdam) {u : ValidatorIndex} {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (onChain : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true)
    {slot : Slot} {begin : UInt64} {epoch : Epoch}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (rootEpochOk : ((e.world n).state u).getBlockEpoch root = .ok epoch)
    (targetVotes : ∀ state target anc,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u n head.root)
    (lineage : ((e.world n).state u).getBlockEpoch start = .ok epoch →
      TargetChecked e margin anchorRoot u n epoch start)
    (rootAboveStart : ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨start, .pending⟩ =
      .ok true)
    (rootSafe : SafeAt e (e.world n).time root) :
    TargetChecked e margin anchorRoot u n epoch root := by
  obtain ⟨readEpoch, readSlot, rootEpoch, startEpoch, readEpochOk, _, readRootOk, startEpochOk,
    _, branches⟩ := checked
  cases Except.ok.inj (readEpochOk.symm.trans epochOk)
  cases Except.ok.inj (readRootOk.symm.trans rootEpochOk)
  by_cases sameStart : startEpoch = epoch
  · subst sameStart
    obtain ⟨k, kLe, origin, _, originEpoch, startAbove, record, originSafe⟩ :=
      lineage startEpochOk
    have startRead := rootAboveStart
    unfold Store.isAncestor at startRead
    obtain ⟨startBlockRead, startBlockOk, _⟩ := bind_ok_iff.mp startRead
    have originRead := startAbove
    unfold Store.isAncestor at originRead
    obtain ⟨originBlockRead, originBlockOk, _⟩ := bind_ok_iff.mp originRead
    exact ⟨k, kLe, origin, rootEpochOk, originEpoch,
      Store.isAncestor_trans_of_lt preGloas (Store.block_ok_iff.mp startBlockOk)
        (Store.block_ok_iff.mp originBlockOk) rootAboveStart startAbove, record, originSafe⟩
  rcases branches with old | current
  · exact absurd rfl old.2.1
  have check := current.2.1 rfl sameStart
  have rootRead := onChain
  unfold Store.isAncestor at rootRead
  obtain ⟨rootBlockRead, rootBlockOk, _⟩ := bind_ok_iff.mp rootRead
  refine ⟨n, le_rfl, root, rootEpochOk, rootEpochOk,
    Store.isAncestor_self (node := ⟨root, .pending⟩) (Store.block_ok_iff.mp rootBlockOk),
    .inr ⟨head, upToDate, epochOk, headOk, check, onChain, targetVotes, slot, begin, slotOk,
      beginOk, atSlot⟩, fun time lower upper => ?_⟩
  have same : time = (e.world n).time := Nat.le_antisymm upper lower
  exact same ▸ rootSafe

omit [DecidablePred (· ∈ J)] in
/-- A target check with the count of the rule names an honest quorum with its surplus.

The check reads two thirds of the active balance in the honest support of the target.

The count adds the margin and the quorum reserve of the target state on top of that support. -/
private theorem late_quorum_of_record {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {u : ValidatorIndex} (caller : u ∈ J) {q margin : ℕ} {head : Root}
    (check : ((e.world q).state u).willCurrentTargetBeJustified config head = .ok true)
    (count : ∀ state target anc,
      ((e.world q).state u).getPulledUpHeadState config head = .ok state →
      ((e.world q).state u).getCurrentTarget config head = .ok target →
      ((e.world q).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u q head) :
    ∃ (state anc : BeaconState preset fork) (total : Gwei) (target : Checkpoint)
      (slot first last : Slot) (participants : Std.TreeSet ValidatorIndex)
      (voters : Finset ValidatorIndex),
      ((e.world q).state u).getPulledUpHeadState config head = .ok state ∧
      getTotalActiveBalance state = .ok total ∧
      ((e.world q).state u).getCurrentTarget config head = .ok target ∧
      ((e.world q).state u).blockStates[target.root]? = some anc ∧
      ((e.world q).state u).getCurrentSlot config = .ok slot ∧
      ((e.world q).state u).getCurrentStoreEpoch config = .ok target.epoch ∧
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first ∧
      subChecked slot 1 = .ok last ∧
      ((e.world q).state u).getCommitteesBetweenSlots head first last = .ok participants ∧
      ((e.world q).state u).getCheckpointBlock head target.epoch = .ok target.root ∧
      (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
        (SignsTarget e v target (e.world q).time ∨ v ∉ participants)) ∧
      2 * total.toNat + (margin + quorumReserve config state anc) ≤
        3 * stake (fun v => balanceAt state v.toNat) voters := by
  have checked := check
  simp only [Store.willCurrentTargetBeJustified, bind_ok_iff, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at checked
  obtain ⟨state, stateOk, total, totalOk, support, supportOk, doubled, doubledOk,
    tripled, tripledOk, bound⟩ := checked
  have two := (mulChecked_ok_iff.mp doubledOk).2
  have three := (mulChecked_ok_iff.mp tripledOk).2
  have le := UInt64.le_iff_toNat_le.mp (of_decide_eq_true bound)
  have enough : 2 * total.toNat ≤ 3 * support.toNat := by
    simpa only [two, three, UInt64.toNat_ofNat] using le
  have reachable := e.reachable
    (fun a ha => (anchored a ha) ▸ Store.Reachable.anchor anchorStore) q u caller
  obtain ⟨target, targetOk⟩ : ∃ target,
      ((e.world q).state u).getCurrentTarget config head = .ok target := by
    have score := supportOk
    unfold Store.computeHonestFfgSupportForCurrentTarget at score
    simp only [bind_ok_iff, mapError_ok_iff] at score
    obtain ⟨_, _, _, _, _, _, scoreValue, scoreOk, _⟩ := score
    unfold Store.getCurrentTargetScore at scoreOk
    obtain ⟨target, targetOk, _⟩ := bind_ok_iff.mp scoreOk
    exact ⟨target, targetOk⟩
  obtain ⟨epoch, checkpoint, _, read, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  obtain ⟨_, block, _, held, _, _⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
  obtain ⟨anc, stored, _⟩ := reachable.blockStatesFromParents held
  obtain ⟨readTarget, slot, first, last, participants, voters, readTargetOk, slotOk, epochOk,
    firstOk, lastOk, participantsOk, targetRead, members, counted⟩ :=
    coverage_quorum_of_count (count state ⟨epoch, checkpoint⟩ anc stateOk targetOk stored)
      stateOk supportOk
  have same := Except.ok.inj (readTargetOk.symm.trans targetOk)
  subst same
  exact ⟨state, anc, total, ⟨epoch, checkpoint⟩, slot, first, last, participants, voters,
    stateOk, totalOk, targetOk, stored, slotOk, epochOk, firstOk, lastOk, participantsOk,
    targetRead, members, by omega⟩

omit [DecidablePred (· ∈ J)] in
/-- An ancestry that one honest store reads holds in another store that holds the descendant. -/
private theorem late_copy_ancestor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {a b : Root} {aBlock bBlock : BeaconBlock preset fork}
    (bKnown : ((e.world n).state u).blocks[b]? = some bBlock)
    (above : ((e.world n).state u).isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true)
    (aReceived : ((e.world k).state w).blocks[a]? = some aBlock) :
    ((e.world k).state w).isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true := by
  have reached := e.reachable
    (fun x hx => (anchored x hx) ▸ Store.Reachable.anchor anchorStore) n u caller
  have received := e.reachable
    (fun x hx => (anchored x hx) ▸ Store.Reachable.anchor anchorStore) k w receiver
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas bKnown above
  have copied := Store.getAncestor_of_same_blocks received
    (oneBlock u caller w receiver n k nBound kBound) (reached.anchorSlot_le_block bKnown)
    ⟨aBlock, aReceived⟩ walk
  obtain ⟨other, otherHeld, _⟩ := Store.getAncestor_le copied
  have same := oneBlock w receiver u caller k n kBound nBound b other bBlock otherHeld bKnown
  subst same
  simp [Store.isAncestor, Store.block_ok_iff.mpr otherHeld, copied, bind, Except.bind, pure,
    Except.pure]

omit [DecidablePred (· ∈ J)] in
/-- Safety of a block protects each ancestor that an honest store reads below it. -/
private theorem late_safe_ancestor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (nBound : (e.world n).time ≤ limit)
    {root origin : Root} {originBlock : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    (descends : ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ =
      .ok true)
    {time : ℕ} (bounded : time ≤ limit) (safe : SafeAt e time root) :
    SafeAt e time origin := by
  intro w receiver k head atTime ready headOk
  have kBound : (e.world k).time ≤ limit := atTime ▸ bounded
  have supports := safe w receiver k head atTime ready headOk
  have rootRead := supports
  unfold Store.isAncestor at rootRead
  obtain ⟨rootBlock, rootBlockOk, _⟩ := bind_ok_iff.mp rootRead
  have rootHeld := Store.block_ok_iff.mp rootBlockOk
  have ancestry := late_copy_ancestor anchorStore anchored preGloas oneBlock caller receiver
    nBound kBound originKnown descends rootHeld
  have originRead := ancestry
  unfold Store.isAncestor at originRead
  obtain ⟨heldBlock, heldBlockOk, _⟩ := bind_ok_iff.mp originRead
  exact Store.isAncestor_trans_of_lt preGloas rootHeld (Store.block_ok_iff.mp heldBlockOk)
    supports ancestry

/-- The boundary of the epoch after an epoch reads at a later slot two epochs on. -/
private theorem late_next_boundary {epoch : Epoch} {current : Slot} {currentBegin : UInt64}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (late : epoch.toNat + 1 < (computeEpochAtSlot preset current).toNat)
    (currentBeginOk : computeTimeAtSlotMs config genesisTimeMs current = .ok currentBegin) :
    ∃ (next : Epoch) (boundary : Slot) (begin : UInt64),
      addChecked epoch 1 = .ok next ∧ computeStartSlotAtEpoch preset next = .ok boundary ∧
      computeTimeAtSlotMs config genesisTimeMs boundary = .ok begin ∧ boundary < current ∧
      begin ≤ currentBegin := by
  have curNat : (computeEpochAtSlot preset current).toNat =
      current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  rw [curNat] at late
  have twoBelow : (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat ≤ current.toNat :=
    (Nat.le_div_iff_mul_le positive).mp (by omega)
  have split : (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat =
      (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    ring
  have fits : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat < current.toNat := by omega
  have currentFits := current.toNat_lt
  have nextFits : epoch.toNat + 1 < 2 ^ 64 := by
    have := Nat.le_mul_of_pos_right (epoch.toNat + 1) positive
    omega
  have nextNat : (epoch + 1).toNat = epoch.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt nextFits
  have nextOk : addChecked epoch 1 = .ok (epoch + 1) :=
    addChecked_ok_iff.mpr ⟨by rw [UInt64.toNat_one]; exact nextFits,
      by rw [nextNat, UInt64.toNat_one]⟩
  have boundaryNat : (UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)).toNat =
      (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have boundaryOk : computeStartSlotAtEpoch preset (epoch + 1) =
      .ok (UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)) :=
    computeStartSlotAtEpoch_ok_iff.mpr ⟨by rw [nextNat]; omega, by rw [boundaryNat, nextNat]⟩
  have boundaryLt : UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) < current :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [boundaryNat]; exact fits)
  obtain ⟨begin, beginOk, _, beginLe⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt boundaryLt) currentBeginOk
  exact ⟨epoch + 1, _, begin, nextOk, boundaryOk, beginOk, boundaryLt, beginLe⟩

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
    (genesis : ∀ w ∈ J, ∀ i, ((e.world i).state w).genesisTimeMs = genesisTimeMs)
    (rootAfterStart : ∀ rootBlock startBlock,
      ((e.world n).state u).blocks[root]? = some rootBlock →
      ((e.world n).state u).blocks[start]? = some startBlock → startBlock.slot < rootBlock.slot) :
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
  intro w receiver k nodes rootBlock slot current atTime ready tree rootKnown slotOk sameEpoch
    currentOk lateEpoch descends
  have pending : head = (⟨head.root, .pending⟩ : ForkChoiceNode) := by
    have p := Store.getHead_pending preGloas headOk
    cases head
    simp_all
  -- The root is above the start of the walk.
  have startHead := startSafe _ le_rfl later u caller n head rfl upToDate headOk
  have startRead := startHead
  unfold Store.isAncestor at startRead
  obtain ⟨startBlock, startBlockOk, _⟩ := bind_ok_iff.mp startRead
  have startKnown := Store.block_ok_iff.mp startBlockOk
  have rootHead : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true := by
    rw [pending]
    exact onChain
  have rootAboveStart : ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨start, .pending⟩ =
      .ok true := by
    rcases coverage_ancestors_comparable preGloas rootKnown startKnown rootHead startHead with
      above | below
    · exact above
    · obtain ⟨startNodeBlock, startNodeKnown, le⟩ := Store.slot_le_of_isAncestor rootKnown below
      have same := Option.some.inj (startNodeKnown.symm.trans startKnown)
      subst same
      exact absurd (rootAfterStart rootBlock startNodeBlock rootKnown startKnown)
        (UInt64.not_lt.mpr le)
  -- The receiver is at a later time than the call, so the root is safe at the call.
  have callerSlot := mapError_ok_iff.mp slotOk
  have receiverSlot := mapError_ok_iff.mp currentOk
  change computeSlotAtTimeMs config ((e.world n).state u).genesisTimeMs
    ((e.world n).state u).timeMs = .ok slot at callerSlot
  change computeSlotAtTimeMs config ((e.world k).state w).genesisTimeMs
    ((e.world k).state w).timeMs = .ok current at receiverSlot
  rw [genesis u caller n] at callerSlot
  rw [genesis w receiver k] at receiverSlot
  have afterCall : (e.world n).time < time := by
    rcases Nat.lt_or_eq_of_le later with lt | eq
    · exact lt
    exfalso
    have sameMs : ((e.world n).state u).timeMs = ((e.world k).state w).timeMs :=
      UInt64.toNat_inj.mp (by rw [upToDate.1, ready.1, atTime, eq])
    rw [sameMs, receiverSlot, Except.ok.injEq] at callerSlot
    subst callerSlot
    rw [sameEpoch] at lateEpoch
    omega
  have rootSafe := safe _ le_rfl afterCall
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlot
  have slotEq := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst slotEq
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  have rootEpochOk : ((e.world n).state u).getBlockEpoch root =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr rootKnown, sameEpoch, bind, Except.bind,
      pure, Except.pure]
  by_cases atBoundary : isStartSlotAtEpoch preset callSlot = .ok false
  swap
  -- A root of the call's own epoch at an epoch start is the finalized root.
  · sorry
  -- The quorum record of the root's epoch.
  have record := late_root_checked preGloas upToDate headOk checked onChain callSlotOk
    callBeginOk atCall epochOk rootEpochOk
    (targetVotes callSlot callSlotOk atBoundary)
    (lineage _ epochOk) rootAboveStart rootSafe
  obtain ⟨q, qLe, origin, _, originEpoch, rootAboveOrigin, arm, originSafe⟩ := record
  rcases arm with anchorOrigin | ⟨headQ, readyQ, epochQ, headQOk, checkQ, originBelowHeadQ,
    countQ, slotQ, beginQ, slotQOk, beginQOk, atQ⟩
  -- An origin at the anchor carries no target check: held for fradamt's decision.
  · sorry
  obtain ⟨stateQ, ancQ, totalQ, target, slotQ', firstQ, lastQ, participantsQ, voters, stateQOk,
    totalQOk, targetQOk, ancQStored, slotQOk', targetEpochQ, firstQOk, lastQOk, participantsQOk,
    targetReadQ, members, quorum⟩ :=
    late_quorum_of_record anchorStore anchored preGloas caller checkQ countQ
  -- The target of the record is of the call's epoch, and so is the origin.
  have slotQEq := Except.ok.inj (slotQOk'.symm.trans slotQOk)
  rw [slotQEq] at firstQOk lastQOk
  have targetEpoch : target.epoch = computeEpochAtSlot preset callSlot :=
    Except.ok.inj (targetEpochQ.symm.trans epochQ)
  have firstOk : computeStartSlotAtEpoch preset target.epoch = .ok firstQ := by
    have slotEpoch : computeEpochAtSlot preset slotQ = target.epoch := by
      simpa [Store.getCurrentStoreEpoch, slotQOk, bind, Except.bind, pure, Except.pure]
        using targetEpochQ
    rw [← slotEpoch]
    exact firstQOk
  have originRead := originBelowHeadQ
  unfold Store.isAncestor at originRead
  obtain ⟨originBlock, originBlockOk, _⟩ := bind_ok_iff.mp originRead
  have originHeldQ := Store.block_ok_iff.mp originBlockOk
  have originHeldN := e.blocks_of_le qLe originHeldQ
  have originEpochEq : computeEpochAtSlot preset originBlock.slot = target.epoch := by
    rw [targetEpoch]
    simpa [Store.getBlockEpoch, Store.block_ok_iff.mpr originHeldN, bind, Except.bind, pure,
      Except.pure] using originEpoch
  -- The boundary of the next epoch is before the receiver.
  obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
    exists_slot_start_of_current_slot receiverSlot
  have currentBeginBound : currentBegin.toNat ≤ time := by
    rw [← atTime, ← ready.1]
    exact UInt64.le_iff_toNat_le.mp currentBeginLe
  have lateNat : (computeEpochAtSlot preset callSlot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat := by
    simpa only [sameEpoch] using lateEpoch
  obtain ⟨nextEpoch, boundary, begin, nextOk, boundaryOk, beginOk, boundaryLt, _⟩ :=
    late_next_boundary positive lateNat currentBeginOk
  rw [← targetEpoch] at nextOk
  have beginBefore : begin.toNat < time := by
    have := coverage_delay_before_later_slot fits boundaryLt beginOk currentBeginOk
    omega
  have qBound : (e.world q).time ≤ time := (e.monotone_time qLe).trans later
  -- The origin stays safe through the boundary: recorded before the call, then below the root.
  have originSafe' : ∀ t, (e.world q).time ≤ t → t ≤ begin.toNat → SafeAt e t origin := by
    intro t low high
    by_cases early : t ≤ (e.world n).time
    · exact originSafe t low early
    · exact late_safe_ancestor anchorStore anchored preGloas oneBlock caller later originHeldN
        rootAboveOrigin (by omega) (safe t (Nat.le_of_lt (Nat.lt_of_not_ge early)) (by omega))
  -- Each counted honest voter signs the target before the next epoch.
  have signed := e.signsTarget_by_boundary anchorStore sound anchored anchorSlot anchorAtBoundary
    slots positive long window preGloas boost oneBlock prompt committees follows retained votes
    fits nonzero anchorParent inHorizon large supply caller readyQ headQOk stateQOk targetQOk
    targetEpochQ slotQOk beginQOk atQ firstOk lastQOk participantsQOk originHeldQ originEpochEq
    originBelowHeadQ nextOk boundaryOk beginOk (Nat.le_of_lt beginBefore) originSafe' members
  -- The receiver reads the target as the checkpoint of the root.
  obtain ⟨receivedRoot, receivedRootHeld⟩ := known w receiver k atTime ready
  have rootAboveOriginReceiver := late_copy_ancestor anchorStore anchored preGloas oneBlock
    caller receiver later atTime.le originHeldN rootAboveOrigin receivedRootHeld
  have rootRead := coverage_target_read anchorStore anchored preGloas oneBlock caller receiver
    qBound atTime.le targetReadQ originHeldQ originBelowHeadQ originEpochEq
    rootAboveOriginReceiver
  have sameRoot := oneBlock u caller w receiver n k later atTime.le root rootBlock receivedRoot
    rootKnown receivedRootHeld
  subst sameRoot
  have rootEpochReceiver : ((e.world k).state w).getBlockEpoch root = .ok target.epoch := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr receivedRootHeld, sameEpoch, targetEpoch,
      bind, Except.bind, pure, Except.pure]
  have receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  -- Assumption 3: a seed above the root carries the voters' target votes.
  obtain ⟨seed, seedBlock, seedState, seedHeld, seedStored, seedAbove, seedLower, seedUpper,
      seedRead, seedVotes⟩ :=
    included u caller q n qLe later headQ stateQ totalQ target voters headQOk stateQOk targetQOk
      totalQOk targetEpochQ (by rw [targetEpoch]; exact epochOk) (by omega) nextEpoch boundary
      begin nextOk boundaryOk beginOk (fun v member => ⟨(members v member).1, signed v member⟩)
      w receiver k (computeEpochAtSlot preset current) atTime.le (by rw [atTime]; exact later)
      ready receiverEpochOk (by rw [targetEpoch]; omega) root target.epoch rootEpochReceiver
      (UInt64.le_refl _) rootRead (fun t low high => safe t low (by rw [← atTime]; exact high))
  sorry

end Models.Network

end EthLib.Consensus
