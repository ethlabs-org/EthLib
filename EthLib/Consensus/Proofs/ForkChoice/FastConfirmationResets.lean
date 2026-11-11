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

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

private theorem ancestor_pending_of_walk {store : Store preset fork}
    {node : ForkChoiceNode} {root : Root} {block : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (walk : ∃ ancestor, store.getAncestor node block.slot = .ok ancestor ∧
      ancestor.root = root ∧ (fork < .glamsterdam → ancestor.payloadStatus = .pending)) :
    store.isAncestor node ⟨root, .pending⟩ = .ok true := by
  obtain ⟨ancestor, walked, rootEq, pending⟩ := walk
  by_cases gloas : .glamsterdam ≤ fork
  · simp [Store.isAncestor, Store.block_ok_iff.mpr known, walked, gloas, rootEq,
      bind, Except.bind, pure, Except.pure]
  · have status := pending (Nat.lt_of_not_le gloas)
    have eq : ancestor = ⟨root, .pending⟩ := by cases ancestor; simp_all
    simp [Store.isAncestor, Store.block_ok_iff.mpr known, walked, gloas, eq,
      bind, Except.bind, pure, Except.pure]

/-- Every known block has the anchor in its chain, including when the anchor slots differ. -/
private theorem anchor_walk_of_reachable {store anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.blocks[anchor.finalizedCheckpoint.root]? = some anchorBlock ∧
      ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
        store.blocks[node.root]? = some block →
        (fork < .glamsterdam → node.payloadStatus = .pending) →
        anchorBlock.slot ≤ block.slot ∧ ∃ ancestor,
          store.getAncestor node anchorBlock.slot = .ok ancestor ∧
          ancestor.root = anchor.finalizedCheckpoint.root ∧
          (fork < .glamsterdam → ancestor.payloadStatus = .pending) := by
  obtain ⟨anchorRoot, hashed, -, -, -, finalEq, -⟩ := getForkchoiceStore_anchor anchored
  rw [finalEq]
  dsimp only
  have transfer {s t : Store preset fork}
      (maps : ∀ {r : Root} {b : BeaconBlock preset fork},
        s.blocks[r]? = some b → t.blocks[r]? = some b)
      (h : s.blocks[anchorRoot]? = some anchorBlock ∧
        ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
          s.blocks[node.root]? = some block →
          (fork < .glamsterdam → node.payloadStatus = .pending) →
          anchorBlock.slot ≤ block.slot ∧ ∃ ancestor,
            s.getAncestor node anchorBlock.slot = .ok ancestor ∧ ancestor.root = anchorRoot ∧
            (fork < .glamsterdam → ancestor.payloadStatus = .pending))
      {node : ForkChoiceNode} {block : BeaconBlock preset fork}
      (found : s.blocks[node.root]? = some block)
      (pending : fork < .glamsterdam → node.payloadStatus = .pending) :
      anchorBlock.slot ≤ block.slot ∧ ∃ ancestor,
        t.getAncestor node anchorBlock.slot = .ok ancestor ∧ ancestor.root = anchorRoot ∧
        (fork < .glamsterdam → ancestor.payloadStatus = .pending) := by
    obtain ⟨le, ancestor, walk, rest⟩ := h.2 node block found pending
    exact ⟨le, ancestor, Store.getAncestor_of_blocks maps walk, rest⟩
  induction reachable with
  | anchor made =>
    obtain ⟨r, hash, blocks, -⟩ := getForkchoiceStore_maps made
    rw [hashed, Except.ok.injEq] at hash
    subst r
    constructor
    · simp [blocks]
    · intro node block found pending
      rw [blocks, getElem?_insert_root] at found
      split at found
      · rename_i eq
        simp only [Option.some.injEq] at found
        subst block
        exact ⟨UInt64.le_refl _, node,
          Store.getAncestor_of_le (by simp [blocks, eq]) (UInt64.le_refl _),
          eq.symm, pending⟩
      · simp at found
  | @block before after checks sources signed reached added ih =>
    rcases Store.onBlock_same_or_insert added with same | ⟨r, hash, fresh, blocks,
      pre, post, preFound, transition, states⟩
    · exact same ▸ ih
    have maps {r : Root} {b : BeaconBlock preset fork}
        (found : before.blocks[r]? = some b) : after.blocks[r]? = some b :=
      Store.onBlock_blocks_of_found added found
    refine ⟨maps ih.1, ?_⟩
    intro node block found pending
    rw [blocks, getElem?_insert_root] at found
    split at found
    · rename_i eq
      simp only [Option.some.injEq] at found
      subst block
      obtain ⟨parent, parentFound⟩ := reached.known_of_blockState preFound
      have lower : parent.slot < signed.message.slot := by
        by_cases same : parent = anchorBlock
        -- The anchor state need not have its block's slot; the finalized walk bounds that block.
        · obtain ⟨-, ⟨finalSlot, start, afterFinal⟩, checkpoint⟩ := Store.onBlock_checks hash
            (by simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]) added
          unfold Store.getCheckpointBlock at checkpoint
          rw [bind_ok_iff] at checkpoint
          obtain ⟨slot, slotOk, checkpoint⟩ := checkpoint
          have slotEq := Except.ok.inj ((mapError_ok_iff.mp slotOk).symm.trans start)
          cases slotEq
          rw [bind_ok_iff] at checkpoint
          obtain ⟨ancestor, walk, -⟩ := checkpoint
          obtain ⟨b, known, le⟩ := Store.getAncestor_le walk
          have minSlot := (ih.2 ⟨ancestor.root, .pending⟩ b known (fun _ => rfl)).1
          rw [same]
          exact UInt64.lt_of_le_of_lt (UInt64.le_trans minSlot le) afterFinal
        -- Every other block has the slot of its stored state, before the child's transition.
        · have slotEq := (reached.blockState_header parentFound preFound same).1
          rw [← slotEq]
          exact (stateTransition_slot transition).1
      obtain ⟨minSlot, ancestor, walk, rootEq, status⟩ := ih.2
        ⟨signed.message.parentRoot, Store.parentPayloadStatus signed.message parent⟩ parent
        parentFound (fun before => Store.parentPayloadStatus_of_lt before)
      refine ⟨UInt64.le_trans minSlot (UInt64.le_of_lt lower), ancestor, ?_, rootEq, status⟩
      rw [Store.getAncestor_step (by simp [blocks, eq])
        (UInt64.not_le.mpr (UInt64.lt_of_le_of_lt minSlot lower)) (maps parentFound) lower]
      exact Store.getAncestor_of_blocks maps walk
    · exact transfer maps ih found pending
  | tick _ ticked ih =>
    have blocks := (Store.onTick_frame ticked).2.2.1
    exact ⟨blocks ▸ ih.1, fun n b f p => transfer (fun h => blocks ▸ h) ih (blocks ▸ f) p⟩
  | attestation _ attested ih =>
    have blocks := (Store.onAttestation_frame attested).2.1
    exact ⟨blocks ▸ ih.1, fun n b f p => transfer (fun h => blocks ▸ h) ih (blocks ▸ f) p⟩
  | attesterSlashing _ slashed ih =>
    have blocks := (Store.onAttesterSlashing_frame slashed).2.1
    exact ⟨blocks ▸ ih.1, fun n b f p => transfer (fun h => blocks ▸ h) ih (blocks ▸ f) p⟩
  | payloadAttestation _ voted ih =>
    have blocks := (Store.onPayloadAttestationMessage_onlyPtcVotes voted).frame.2.1
    exact ⟨blocks ▸ ih.1, fun n b f p => transfer (fun h => blocks ▸ h) ih (blocks ▸ f) p⟩
  | envelope _ accepted ih =>
    have blocks := (Store.onExecutionPayloadEnvelope_frame accepted).2.1
    exact ⟨blocks ▸ ih.1, fun n b f p => transfer (fun h => blocks ▸ h) ih (blocks ▸ f) p⟩
  | inclusionList _ accepted ih =>
    have blocks := (Store.onInclusionList_frame accepted).2.1
    exact ⟨blocks ▸ ih.1, fun n b f p => transfer (fun h => blocks ▸ h) ih (blocks ▸ f) p⟩

/-- The block of the anchor is safe at each time.

Each honest store starts as the store of the anchor.

Each block of such a store is the block of the anchor or is above it. -/
theorem Execution.safeAt_anchor {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (time : ℕ) :
    SafeAt e time anchor.finalizedCheckpoint.root := by
  intro w honest k head _ _ headOk
  have reached := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨known, walks⟩ := anchor_walk_of_reachable anchored reached
  have descends := Store.isAncestor_getHead headOk
  have justifiedKnown : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).justifiedCheckpoint.root]? = some b := by
    unfold Store.isAncestor at descends
    rw [bind_ok_iff] at descends
    obtain ⟨b, found, -⟩ := descends
    exact ⟨b, Store.block_ok_iff.mp found⟩
  obtain ⟨b, found⟩ := justifiedKnown
  obtain ⟨block, headFound, -⟩ := Store.slot_le_of_isAncestor found descends
  exact ancestor_pending_of_walk known
    (walks head block headFound (fun before => Store.getHead_pending before headOk)).2

/-- The finalized checkpoint of an honest store is that of the anchor, or is two epochs old.

No checkpoint of the state of the anchor is of a later epoch than that state.

A state finalizes a checkpoint of the epoch before its own at the latest.

The store takes that checkpoint from a block of an epoch before its own. -/
theorem Execution.finalizedCheckpoint_eq_or_add_two_le {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
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
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (honest : u ∈ J) (start : e.start u = anchor) {n : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state u).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
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
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (nonzero : ∀ v ∈ J, ∀ k', (e.world k').time ≤ (e.world k).time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k').state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
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
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) {limit : ℕ}
    (nonzero : ∀ v ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
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
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch later : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (nonzero : ∀ v ∈ J, ∀ k', (e.world k').time ≤ (e.world k).time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k').state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
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
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
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
    (nonzero : ∀ v ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time ((e.world m).state u).unrealizedJustifiedCheckpoint.root := by
  sorry

end EthLib.Consensus.Models.Network
