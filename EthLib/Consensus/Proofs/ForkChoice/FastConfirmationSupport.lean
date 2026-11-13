module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSets
public import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedOrigins
public import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
public import EthLib.Consensus.Proofs.Transition.RunKept
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.Transition.RewardReads
import EthLib.Consensus.Proofs.ForkChoice.BlockStates

/-!
# Statements: the honest support of a confirmed block reaches each honest store

This file states steps 4 and 5 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs of step 5 are placeholders, and each statement of step 5 may still change.

Step 4 joins two proved bounds on a one-confirmed block, and its proof is complete.

Count the honest supporters of the block twice, and add the honest voters for its parent.

The sum exceeds the weight of the committees of the block plus the boost.

Step 5 carries that bound from the store of the caller to each honest store at a later time.

An honest vote that the caller holds reaches each honest store before the next slot.

While the block is on the chain of each honest head, each new honest vote supports it.

So the bound holds in each honest store, with the committees of the slots since.

The head of such a store then descends from the block, when the store has not filtered it out.

That last step is the store form of Lemma 2 of the paper, and this file takes it as a hypothesis.

In [verified-fast-confirmation][vfc], step 5 is `safeFrom_of_headStep_at` with its lemmas.

There the set of validators and their balances are fixed, and one function gives the committees.

Here each store reads committees and balances from its own states.

So step 5 asks that they agree.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- Step 4: the honest support of a one-confirmed block, without the discount of the rule.

The honest voters for the parent come from the committees between the parent and the block.

Each of the two ranges of committees has at most β of its stake Byzantine, Assumption 2.

The other hypotheses are those of the two bounds that the proof joins. -/
theorem lt_honest_parentVotersOf_add_two_mul_supportersOf_of_isOneConfirmed
    {J : Set ValidatorIndex} [DecidablePred (· ∈ J)] {head root : Root}
    {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot startSlot beforeBlock : Slot}
    {block parentBlock : BeaconBlock preset fork}
    {participants parentParticipants : Std.TreeSet ValidatorIndex}
    {proposerScore maximumSupport discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (participantsOk : store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants)
    (parentParticipantsOk :
      store.getCommitteesBetweenSlots head firstSlot beforeBlock = .ok parentParticipants)
    (confirmed : store.isOneConfirmed config head balanceSource (store.tallyVotes balanceSource)
      root = .ok true)
    (supportersIn : ∀ v ∈ store.supportersOf balanceSource ⟨root, .pending⟩, v ∈ participants)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (activeMembers balanceSource participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (parentByzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (activeMembers balanceSource parentParticipants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      stake (fun v => balanceAt balanceSource v.toNat)
          {v ∈ store.parentVotersOf balanceSource parentParticipants block parentBlock | v ∈ J} +
        2 * stake (fun v => balanceAt balanceSource v.toNat)
          {v ∈ store.supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} := by
  have support := lt_two_mul_honest_supportersOf_of_isOneConfirmed within slotOk blockOk parentOk
    boostOk firstOk lastOk maximumOk discountOk adversaryOk rangeOk participantsOk confirmed
    supportersIn aligned increment dishonest byzantine
  have parent := le_honest_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
    firstOk beforeOk parentParticipantsOk discountOk aligned increment dishonest parentByzantine
  omega

/-- Before Gloas, an ancestor test is the exact walk to the ancestor's slot. -/
theorem getAncestor_of_isAncestor_of_lt {node ancestor : ForkChoiceNode}
    {block : BeaconBlock preset fork} (before : fork < .glamsterdam)
    (known : store.blocks[ancestor.root]? = some block)
    (descends : store.isAncestor node ancestor = .ok true) :
    store.getAncestor node block.slot = .ok ancestor := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [isAncestor, block_ok_iff.mpr known, notGloas, ↓reduceIte,
    bind, Except.bind] at descends
  cases walk : store.getAncestor node block.slot with
  | error error => simp [walk] at descends
  | ok found =>
    simp only [walk, pure, Except.pure, Except.ok.injEq, beq_iff_eq] at descends
    exact congrArg Except.ok descends

/-- Before Gloas, descent composes through a known intermediate block. -/
theorem isAncestor_trans_of_lt {node middle ancestor : ForkChoiceNode}
    {middleBlock ancestorBlock : BeaconBlock preset fork}
    (before : fork < .glamsterdam)
    (middleKnown : store.blocks[middle.root]? = some middleBlock)
    (ancestorKnown : store.blocks[ancestor.root]? = some ancestorBlock)
    (upper : store.isAncestor node middle = .ok true)
    (lower : store.isAncestor middle ancestor = .ok true) :
    store.isAncestor node ancestor = .ok true := by
  have upperWalk := getAncestor_of_isAncestor_of_lt before middleKnown upper
  have lowerWalk := getAncestor_of_isAncestor_of_lt before ancestorKnown lower
  obtain ⟨block, found, le⟩ := slot_le_of_isAncestor ancestorKnown lower
  rw [middleKnown, Option.some.injEq] at found
  subst block
  have walk := (getAncestor_trans le upperWalk).trans lowerWalk
  simp [isAncestor, block_ok_iff.mpr ancestorKnown, walk,
    bind, Except.bind, pure, Except.pure]

/-- A reachable receiver holding the tip agrees on its ancestor walk above the anchor slot. -/
theorem getAncestor_of_same_blocks {receiver : Store preset fork}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock receiver)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {node ancestor : ForkChoiceNode} {slot : Slot}
    (aboveAnchor : anchorBlock.slot ≤ slot)
    (known : ∃ block, receiver.blocks[node.root]? = some block)
    (walk : store.getAncestor node slot = .ok ancestor) :
    receiver.getAncestor node slot = .ok ancestor := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    obtain ⟨other, held⟩ := known
    have eq := same _ _ _ found held
    subst other
    rw [getAncestor_of_le found le] at walk
    exact (getAncestor_of_le held le).trans walk
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst b
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    obtain ⟨other, held⟩ := known
    have eq := same _ _ _ found held
    subst other
    have notAnchor : block ≠ anchorBlock := by
      intro eq
      exact above (eq ▸ aboveAnchor)
    obtain ⟨state, _, _, provenance⟩ := reachable.blockStatesFromParents held
    obtain ⟨parentState, _, _, _, _, parentStateFound, _⟩ := provenance notAnchor
    obtain ⟨receiverParent, receiverParentFound⟩ := reachable.known_of_blockState parentStateFound
    have eq := same _ _ _ parentFound receiverParentFound
    subst receiverParent
    rw [getAncestor_step found above parentFound lower] at walk
    rw [getAncestor_step held above receiverParentFound lower]
    exact ih ⟨parent, receiverParentFound⟩ walk
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst b
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p eq
        rw [parentFound, Option.some.injEq] at eq
        subst p
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- Ancestor tests agree across reachable stores holding the tip and ancestor above the anchor. -/
theorem isAncestor_of_same_blocks {receiver : Store preset fork}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock receiver)
    (before : fork < .glamsterdam)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {node ancestor : ForkChoiceNode} {block : BeaconBlock preset fork}
    (sourceKnown : store.blocks[ancestor.root]? = some block)
    (targetKnown : receiver.blocks[ancestor.root]? = some block)
    (aboveAnchor : anchorBlock.slot ≤ block.slot)
    (known : ∃ tip, receiver.blocks[node.root]? = some tip)
    (descends : store.isAncestor node ancestor = .ok true) :
    receiver.isAncestor node ancestor = .ok true := by
  have walk := getAncestor_of_isAncestor_of_lt before sourceKnown descends
  have transferred := getAncestor_of_same_blocks reachable same aboveAnchor known walk
  simp [isAncestor, block_ok_iff.mpr targetKnown,
    transferred, bind, Except.bind, pure, Except.pure]

/-- Checkpoint reads agree across reachable stores holding the tip above the anchor boundary. -/
theorem getCheckpointBlock_of_same_blocks {receiver : Store preset fork}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock receiver)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {root checkpoint : Root} {epoch : Epoch} {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (aboveAnchor : anchorBlock.slot ≤ boundary)
    (known : ∃ block, receiver.blocks[root]? = some block)
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    receiver.getCheckpointBlock root epoch = .ok checkpoint := by
  simp only [getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind] at read ⊢
  cases walk : store.getAncestor ⟨root, .pending⟩ boundary with
  | error error => simp [walk] at read
  | ok ancestor =>
    rw [getAncestor_of_same_blocks reachable same aboveAnchor known walk]
    simpa [walk] using read

/-- Descent through a block carries its checkpoint read to the descendant at an earlier boundary. -/
theorem getCheckpointBlock_of_isAncestor {node : ForkChoiceNode} {root checkpoint : Root}
    {block : BeaconBlock preset fork} {epoch : Epoch} {boundary : Slot}
    (before : fork < .glamsterdam)
    (known : store.blocks[root]? = some block)
    (descends : store.isAncestor node ⟨root, .pending⟩ = .ok true)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (earlier : boundary ≤ block.slot)
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    store.getCheckpointBlock node.root epoch = .ok checkpoint := by
  have walk := getAncestor_of_isAncestor_of_lt before known descends
  have through := getAncestor_trans earlier walk
  have rootWalk := getAncestor_root (store := store) node .pending boundary
  simp only [getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind] at read ⊢
  change ((fun x => x.root) <$> store.getAncestor ⟨node.root, .pending⟩ boundary) =
    .ok checkpoint
  rw [← rootWalk, through]
  exact read

/-- A descendant reads the checkpoint of an ancestor that is no earlier than the boundary. -/
theorem getCheckpointBlock_of_isAncestor_below {node ancestor : ForkChoiceNode}
    {checkpoint : Root} {block : BeaconBlock preset fork} {epoch : Epoch} {boundary : Slot}
    (before : fork < .glamsterdam)
    (known : store.blocks[ancestor.root]? = some block)
    (descends : store.isAncestor node ancestor = .ok true)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (earlier : boundary ≤ block.slot)
    (read : store.getCheckpointBlock node.root epoch = .ok checkpoint) :
    store.getCheckpointBlock ancestor.root epoch = .ok checkpoint := by
  have walk := getAncestor_of_isAncestor_of_lt before known descends
  have through := getAncestor_trans earlier walk
  have nodeWalk := getAncestor_root (store := store) node .pending boundary
  have ancestorWalk := getAncestor_root (store := store) ancestor .pending boundary
  simp only [getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind] at read ⊢
  change ((fun x => x.root) <$> store.getAncestor ⟨ancestor.root, .pending⟩ boundary) =
    .ok checkpoint
  rw [← ancestorWalk, ← through, nodeWalk]
  exact read

/-- Before Gloas, a walk starting at a pending node returns a pending node. -/
theorem getAncestor_pending_of_lt {node ancestor : ForkChoiceNode} {slot : Slot}
    (before : fork < .glamsterdam) (pending : node.payloadStatus = .pending)
    (walk : store.getAncestor node slot = .ok ancestor) :
    ancestor.payloadStatus = .pending := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [getAncestor_of_le found le] at walk
    cases walk
    exact pending
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst b
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    rw [getAncestor_step found above parentFound lower] at walk
    exact ih (parentPayloadStatus_of_lt before) walk
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst b
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p eq
        rw [parentFound, Option.some.injEq] at eq
        subst p
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- A successful checkpoint read names a held ancestor, at or before its epoch boundary. -/
theorem isAncestor_of_getCheckpointBlock {root checkpoint : Root} {epoch : Epoch}
    (before : fork < .glamsterdam)
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ boundary block, computeStartSlotAtEpoch preset epoch = .ok boundary ∧
      store.blocks[checkpoint]? = some block ∧ block.slot ≤ boundary ∧
      store.isAncestor ⟨root, .pending⟩ ⟨checkpoint, .pending⟩ = .ok true := by
  unfold getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨boundary, boundaryOk, ancestor, walk, rootEq⟩ := read
  obtain ⟨block, held, le⟩ := getAncestor_le walk
  have pending := getAncestor_pending_of_lt before rfl walk
  have same : ancestor = ⟨checkpoint, .pending⟩ := by
    cases ancestor
    simp_all
  subst ancestor
  have through := getAncestor_trans le walk
  have atBlock := getAncestor_of_le (node := ⟨checkpoint, .pending⟩) held (UInt64.le_refl _)
  have walk' := through.trans atBlock
  refine ⟨boundary, block, mapError_ok_iff.mp boundaryOk, held, le, ?_⟩
  simp [isAncestor, block_ok_iff.mpr held, walk', bind, Except.bind, pure, Except.pure]

/-- A computable target state can be cached, or the store can read its existing entry. -/
theorem exists_storeTargetCheckpointState {checks : SignatureChecks} {target : Checkpoint}
    {state : BeaconState preset fork}
    (computed : store.computeCheckpointState config checks target = .ok state) :
    ∃ withTarget targetState,
      store.storeTargetCheckpointState config checks target = .ok withTarget ∧
      withTarget.checkpointState target = .ok targetState := by
  by_cases cached : store.checkpointStates.contains target
  · have member := Std.TreeMap.contains_iff_mem.mp cached
    have present := Std.TreeMap.mem_iff_isSome_getElem?.mp member
    obtain ⟨targetState, found⟩ := Option.isSome_iff_exists.mp present
    refine ⟨store, targetState, ?_, checkpointState_ok_iff.mpr found⟩
    simp [storeTargetCheckpointState, cached, pure, Except.pure]
  · refine ⟨{ store with checkpointStates := store.checkpointStates.insert target state },
      state, ?_, checkpointState_ok_iff.mpr (by simp)⟩
    simp [storeTargetCheckpointState, cached, computed, bind, Except.bind, pure, Except.pure]

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- A block is safe at a time: it is on the chain of the head of each honest store then.

The store is that of an honest validator at an event of that time, and is up to date.

The time is in milliseconds. -/
def SafeAt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (time : ℕ) (root : Root) : Prop :=
  ∀ w ∈ J, ∀ k head, (e.world k).time = time →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true

/-- At a time, each honest store holds a block in its filtered tree or below its justified block.

The store is that of an honest validator at an event of that time, and is up to date.

Below means that the block is on the chain of the justified block of the store. -/
def CoveredOrViableAt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (time : ℕ) (root : Root) : Prop :=
  ∀ w ∈ J, ∀ k nodes, (e.world k).time = time →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
    ((e.world k).state w).isAncestor ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true ∨ (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes

variable (fork) in
/-- The delay fits in a slot: a vote cast at its deadline arrives before the next slot starts. -/
def DelayFits (config : Config) (genesisTimeMs : UInt64) (Δ : ℕ) : Prop :=
  (∃ due, getAttestationDueMs config fork = .ok due) ∧
  ∀ slot next start due following, addChecked slot 1 = .ok next →
    computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    getAttestationDueMs config fork = .ok due →
    computeTimeAtSlotMs config genesisTimeMs next = .ok following →
    start.toNat + due.toNat + Δ < following.toNat

/-- Each honest validator processes messages before and at each slot boundary up to `last`.

The slots are those that start at the start of the execution or later, and at `last` or earlier.

A theorem about times up to `last` needs no processing after it, so a finite execution can meet it.

Pre-boundary processing admits delivered blocks before the next tick can change finality.

Boundary processing admits votes after their slot has ended.

This is a processing hypothesis, not a consequence of receipt in a network view.

It makes explicit the processing needed in addition to the network bound of
arXiv 2405.00549v4, Section 2. -/
def Prompt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (last : ℕ) : Prop :=
  ∀ w ∈ J, ∀ slot start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    e.startTime ≤ start.toNat → start.toNat ≤ last →
    (∃ k, (e.world k).time = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w)) ∧
    (e.startTime < start.toNat → ∃ k, (e.world k).time + 1 = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w))

/-- Processing up to a time gives processing up to every earlier time. -/
theorem Prompt.of_le {last later : ℕ} (prompt : Prompt e later) (le : last ≤ later) :
    Prompt e last :=
  fun w honest slot start startOk started bounded =>
    prompt w honest slot start startOk started (bounded.trans le)

/-- The committees that an honest store reads for a range of slots are those of the assignment.

An honest validator is in the committees of the range when the assignment gives it a slot there.

The agreement is restricted to actual heads and past ranges.

For a target-state comparison, a common state supplies the hypotheses of `RunKept.committeesKept`.

The assignment link remains separate: a free assignment is not determined by a transition. -/
structure CommitteesFollow
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (limit : ℕ) : Prop where
  /-- Honest duties use the actual head's committees for the past slots read by the rule.

  The head state still holds the RANDAO mix that the seed of the first epoch of the range reads.

  This is the retention bound of `RunKept.committeesKept`; agreement beyond it is not derived. -/
  assigned : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit → ∀ head current first last participants,
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).getCurrentSlot config = .ok current → last < current →
    (∀ headState, ((e.world k).state w).blockState head.root = .ok headState →
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        (computeEpochAtSlot preset first).toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok participants →
    ∀ v ∈ J, v ∈ participants ↔
      ∃ slot committeeIndex, first ≤ slot ∧ slot ≤ last ∧
        assignment.committee v slot = some committeeIndex
  /-- The common-state witnesses for the target and head committee comparison. -/
  common : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
    ∀ head headState current v attestation targetState,
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).blockState head.root = .ok headState →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
    attestation.data.target.epoch.toNat ≤ current.toNat →
    current.toNat ≤ attestation.data.target.epoch.toNat + 1 →
    ((e.world k).state w).VoteOrigin config v attestation →
    ((e.world k).state w).checkpointStates[attestation.data.target]? = some targetState →
    ∃ common : BeaconState preset fork,
      RunKept common headState ∧ RunKept common targetState ∧
      attestation.data.target.epoch.toNat ≤
        (getCurrentEpoch common).toNat + preset.MIN_SEED_LOOKAHEAD.toNat ∧
      attestation.data.target.epoch ≤ activityFixedEpoch common ∧
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        attestation.data.target.epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
      (getCurrentEpoch targetState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        attestation.data.target.epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat

/-- Committees that follow up to a time follow up to every earlier time. -/
theorem CommitteesFollow.of_le {last later : ℕ} (committees : CommitteesFollow e later)
    (le : last ≤ later) : CommitteesFollow e last :=
  ⟨fun w honest k bounded => committees.assigned w honest k (bounded.trans le),
    fun w honest k bounded => committees.common w honest k (bounded.trans le)⟩

/-- The head of an honest store follows the honest support of a block, Lemma 2 in the store.

The store is up to date, and the parent of the block is on the chain of its head.

The block is in the filtered tree of the store.

The window is the committees of the head over the slots between the parent and the current slot.

The current epoch is at most two epochs after the epoch of the parent.

Each validator counted for a sibling of the block, or for the block, is in the window.

It is also active in the justified state of the store.

That containment is a premise, not part of this assumption.

`Execution.mem_activeMembers_of_sibling_vote` is to prove it.

Count the honest supporters of the block twice, and add the honest voters for its parent.

The sum exceeds the stake of the active members of the window plus the boost.

The balances are those of the justified state of the store.

Then the block is on the chain of the head.

This is the tree part of Lemma 2 in issue 1458, with the window as the cap on a sibling.

The reads field prevents a failed committee computation from making descent vacuous. -/
structure HeadFollowsSupport
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) [DecidablePred (· ∈ J)] (limit : ℕ) : Prop where
  /-- A head has the balance and committee reads needed for every past range. -/
  reads : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit → ∀ head,
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    ∃ state current score nodes,
      ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state ∧
      ((e.world k).state w).getCurrentSlot config = .ok current ∧
      computeProposerScore config state = .ok score ∧
      ((e.world k).state w).getFilteredNodeTree config = .ok nodes ∧
      ∀ first last, last < current → ∃ participants,
        ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok participants
  /-- Honest support above the sibling cap makes the head follow a viable child. -/
  follows : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
    ∀ head state root block parentBlock current epoch first last beforeBlock
    window score nodes parentParticipants,
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).block root = .ok block →
    ((e.world k).state w).block block.parentRoot = .ok parentBlock →
    ((e.world k).state w).getCurrentSlot config = .ok current →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch →
    epoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2 →
    addChecked parentBlock.slot 1 = .ok first → subChecked current 1 = .ok last →
    subChecked block.slot 1 = .ok beforeBlock →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok window →
    computeProposerScore config state = .ok score →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first beforeBlock =
      .ok parentParticipants →
    ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes →
    ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true →
    (∀ (c : ForkChoiceNode) (childBlock : BeaconBlock preset fork) (v : ValidatorIndex),
      ((e.world k).state w).blocks[c.root]? = some childBlock →
      childBlock.parentRoot = block.parentRoot →
      ((e.world k).state w).voteCountsFor c v = true →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ Store.activeMembers state window) →
    stake (fun v => balanceAt state v.toNat) (Store.activeMembers state window) + score.toNat <
      stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).parentVotersOf state parentParticipants block parentBlock |
            v ∈ J} +
        2 * stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} →
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true

/-- Two hundred million ether, in Gwei: a cap on the active stake of a state.

The active stake of the chain is far below it.

Theorem 1 assumes that every checkpoint state an honest store reads stays within it.

That keeps each sum of effective balances that the rule reads below 2^64.

It also keeps a percentage of the stake of one slot below 2^64 before it is divided by 100.

The cap is a premise about the supply of ether, not a check of the specification. -/
def stakeCapGwei : ℕ := 2 * 10 ^ 17

/-- The cap fits in 64 bits. -/
theorem stakeCapGwei_lt : stakeCapGwei < 2 ^ 64 := by
  unfold stakeCapGwei
  norm_num

/-- The stake that can leave the active set of a source of balances within two epochs.

The first term is the stake already scheduled to exit by two epochs after the source's epoch.

The second is what exits charged during the source's epoch can still add by then.

Those charges read the source's effective balances, so the churn of the source bounds them.

From Electra the exit and consolidation queues each add their churn and their churn left over.

Each also adds one maximum effective balance, for an exit that carries churn from earlier epochs.

Before Electra the exit queue counts validators, so it adds a churn of maximum balances.

A churn read that fails adds nothing, since a charge that reads it then fails too. -/
def exitReserve (config : Config) (source : BeaconState preset fork) : ℕ :=
  stake (fun v => balanceAt source v.toNat)
      {v ∈ activeVoters source | (source.validators.data[v.toNat]?).any fun validator =>
        validator.exitEpoch.toNat ≤ (getCurrentEpoch source).toNat + 2} +
    if electra : .pectra ≤ fork then
      ((exitChurnLimit config source).toOption.getD 0).toNat +
        (source.exitBalanceToConsume electra).toNat +
        ((getConsolidationChurnLimit config source).toOption.getD 0).toNat +
        (source.consolidationBalanceToConsume electra).toNat +
        2 * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    else max 1 (getValidatorChurnLimit config source).toNat * preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The stake by which the quorum of the call can drift from the reference state to a later state.

The state is the pulled-up head state of the call, and the ancestor is the state of its target root.

Every term reads the state, except the queue of partial withdrawals, which the ancestor holds.

Every read is a function on natural numbers of the fields of the state.

Each equals the executable read whenever that read succeeds, as the lemmas on the reads show.

The reserve is twice the gain plus three times the loss.

```text
gain  = joining + min headroom (crossing + (recipients + debited) * upwardBand
          + debited * creditMax + transfers + depositGain)
loss  = sum of fall + creditedP * (increment + 2 * downwardBand + syncPMax) + maskBudget
```

- The gain is the rise of the total active balance over the next epoch.
  Validators that join the active set count in full.
  A validator that stays active gains at most the credit that crosses the upward band.
  Validators that receive a transfer, or that a block of the epoch debits, gain one band more.
- The loss is the fall of the stake of the active validators.
  A validator falls by its penalties and the partial withdrawals that the ancestor queue pays.
  Validators credited on the branch of the state, other than by sync rewards, add a band.
  The partial withdrawals that those credits hide add the mask budget.
- The credits and penalties of an epoch are bounds on the rewards of its end.
  Altair pays a share of the base reward for each flag, scaled by the previous-to-current ratio.
  Before Altair the three components of the attestation rewards and the inclusion reward count.
- From Electra the deposit churn and the pending consolidations that come due add transfers.
  Before Electra the deposits of a block add a gain at the largest effective balance.
-/
def quorumReserve (config : Config) (state ancestor : BeaconState preset fork) : ℕ :=
  let epoch := getCurrentEpoch state
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let slots := preset.SLOTS_PER_EPOCH.toNat
  let p := parameters preset fork
  let positions := Finset.range state.validators.data.size
  let validator (i : ℕ) := state.validators.data[i]?
  let effective (i : ℕ) := balanceAt state i
  let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
  let cap (i : ℕ) :=
    ((validator i).map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0
  let capMax := if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    else preset.MAX_EFFECTIVE_BALANCE.toNat
  let current (i : ℕ) := isActiveAt state epoch i
  let upcoming (i : ℕ) := isActiveAt state (epoch + 1) i
  let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
  let recent (i : ℕ) := before i || current i
  let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
  let total := max inc (∑ i ∈ positions with current i, effective i)
  let root := (integerSquareroot (UInt64.ofNat total)).toNat
  let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
  let base (i : ℕ) := if .altair ≤ fork then effective i / inc * perIncrement
    else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
  let num := max 1 ((∑ i ∈ positions with before i, effective i) / inc)
  let den := max 1 (total / inc)
  let flagWeight := (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  let seatReward := if .altair ≤ fork then
      total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
        slots / preset.SYNC_COMMITTEE_SIZE.toNat
    else 0
  let seats (i : ℕ) := if altair : .altair ≤ fork then
      ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        (validator i).any (·.pubkey == key)).length
    else 0
  let sync (i : ℕ) := seats i * seatReward
  let depositChurn :=
    if .glamsterdam ≤ fork then
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat (limit - limit % inc)
    else
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (limit - limit % inc)
  let score (i : ℕ) := if altair : .altair ≤ fork then
      (((state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  let delay := (getPreviousEpoch state).toNat - state.finalizedCheckpoint.epoch.toNat
  let inactivity (i : ℕ) := if .altair ≤ fork then
      effective i * (score i + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
    else if preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY.toNat < delay then
      4 * base i + effective i * delay / p.INACTIVITY_PENALTY_QUOTIENT.toNat
    else 0
  let credit (i : ℕ) :=
    (if .altair ≤ fork then base i * flagWeight * num / (WEIGHT_DENOMINATOR.toNat * den)
     else 3 * (base i * max num den / den) + base i) + slots * sync i
  let penalty (i : ℕ) :=
    (if .altair ≤ fork then base i else 3 * base i) + inactivity i + slots * sync i
  let proposerCredit := ∑ i ∈ positions with recent i, base i
  let whistleblower := (∑ i ∈ positions with (validator i).any (fun v =>
      v.activationEpoch ≤ epoch && epoch < v.withdrawableEpoch), effective i) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let depositCredit := if electra : .pectra ≤ fork then
      (state.depositBalanceToConsume electra).toNat + depositChurn else 0
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let dueStake := (due.map fun c => effective c.sourceIndex.toNat).sum
  let proposers := if .altair ≤ fork then slots else 2 * slots
  let depositRecipients := if .pectra ≤ fork then preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
    else slots * preset.MAX_DEPOSITS.toNat
  let recipients := (if .pectra ≤ fork then depositRecipients else 0) + due.length + proposers
  let nP := state.slot.toNat - epoch.toNat * slots + 1
  let debited := ((if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
    (if .pectra ≤ fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) * nP
  let transfers := depositCredit + dueStake + proposerCredit + whistleblower
  let depositGain := if .pectra ≤ fork then 0 else depositRecipients * capMax
  let slashBack (i : ℕ) :=
    if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
  let syncP (i : ℕ) := nP * sync i
  let blockDeposits := if h : fork < .hegota then
      (if .pectra ≤ fork then 0
       else min (preset.MAX_DEPOSITS.toNat * nP) (state.eth1DepositIndex h).toNat)
    else 0
  let creditedP :=
    (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0 else nP) +
      blockDeposits
  let creditMax := positions.sup fun i => if upcoming i then credit i else 0
  let joining := ∑ i ∈ positions with current i = false ∧ upcoming i = true, effective i
  let crossing := ∑ i ∈ positions with upcoming i,
    if effective i < cap i then
      (let top := actual i + slashBack i + syncP i + credit i
       if effective i + preset.upwardBand < top then top - effective i else 0)
    else (if preset.upwardBand < credit i then credit i else 0)
  let headroom := ∑ i ∈ positions with upcoming i, (capMax - effective i)
  let gain := joining + min headroom (crossing + (recipients + debited) * preset.upwardBand +
    debited * creditMax + transfers + depositGain)
  let partials (i : ℕ) := if electra : .pectra ≤ fork then
      (((ancestor.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch ≤ epoch).map (·.amount.toNat)).sum
    else 0
  let fall (i : ℕ) :=
    let low := min (actual i - syncP i) (effective i) - (partials i + penalty i)
    if effective i ≤ low + preset.downwardBand then 0 else effective i - (low - low % inc)
  let syncPMax := positions.sup fun i => if current i then syncP i else 0
  let whistleblowerP :=
    (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let maskBudget := if .pectra ≤ fork then
      min (proposerCredit + whistleblowerP)
        (preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat *
          (capMax - preset.MIN_ACTIVATION_BALANCE.toNat))
    else 0
  let loss := (∑ i ∈ positions with current i, fall i) +
    creditedP * (inc + 2 * preset.downwardBand + syncPMax) + maskBudget
  2 * gain + 3 * loss

/-- The stores of the honest validators weigh a block as the caller of the rule does.

The caller weighs with the state of its observed justified checkpoint, the source of balances.

Each honest store from a first time to a last one has a bounded loss of support margin.

In each of them, the Byzantine validators hold at most β of each range of committees.

This is Assumption 2.

Here β is the threshold of the configuration, in percent.

No honest validator is a known equivocator of such a store.

The shift compares the same honest subsets and committee set in two balance states.

It bounds the loss of twice the supporters plus the parent voters, less committees and boost.

For each fixed subset pair, gains inside that pair can offset its losses.

The bound holds for every pair, so gains outside a losing subset cannot cancel its loss.

The caller must have that much extra margin; equality of all balances is not required. -/
structure WeightBounds
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) [DecidablePred (· ∈ J)] (balanceSource : BeaconState preset fork)
    (first last shift : ℕ) : Prop where
  /-- Counterfactual reads under the call's balances must succeed before margins can be compared.

  The transport reads the source maximum of the window before the call through this field. -/
  reads : ∀ w ∈ J, ∀ k head state current firstSlot lastSlot maximum,
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).getCurrentSlot config = .ok current → lastSlot < current →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state firstSlot lastSlot =
      .ok maximum →
    ∃ sourceMaximum sourceScore,
      ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root balanceSource
        firstSlot lastSlot = .ok sourceMaximum ∧
      computeProposerScore config balanceSource = .ok sourceScore
  /-- The exact adverse shift of each honest support margin, including the proposer boost. -/
  margin : ∀ w ∈ J, ∀ k head state score sourceScore firstSlot lastSlot maximum sourceMaximum,
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    computeProposerScore config state = .ok score →
    computeProposerScore config balanceSource = .ok sourceScore →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state firstSlot lastSlot =
      .ok maximum →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root balanceSource
      firstSlot lastSlot = .ok sourceMaximum →
    ∀ p q : Finset ValidatorIndex,
    (∀ v ∈ p, v ∈ J) → (∀ v ∈ q, v ∈ J) →
    let sourceWeight := fun v => if v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset
      then balanceAt balanceSource v.toNat else 0
    let receiverWeight := fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0
    2 * stake sourceWeight p + stake sourceWeight q + maximum.toNat + score.toNat ≤
      2 * stake receiverWeight p + stake receiverWeight q + sourceMaximum.toNat +
        sourceScore.toNat + shift
  /-- The call's balance source satisfies the bound on every committee range it reads.

  The range starts at or before its last slot; a range that starts after it has no members.

  The bound keeps half the exit reserve of the source free, in percent of the range.

  That reserve pays for the stake that leaves the active set before a receiver weighs.

  The reserve is read from the source alone, so the bound is exact for each call.

  As an illustration only, take a typical mainnet epoch with a reserve of about 5.5k ETH.

  One slot then holds about 1.06M ETH, so a threshold of 25% acts like about 24.7%.

  A rule that subtracted the reserve in its safety threshold would make this bound fixed. -/
  sourceReserve : ∀ w ∈ J, ∀ k head firstSlot lastSlot participants,
    (e.world k).time = first → firstSlot ≤ lastSlot →
    ((e.world k).state w).getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants →
    100 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ Store.activeMembers balanceSource participants | v ∉ J} +
      50 * exitReserve config balanceSource ≤
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
        stake (fun v => balanceAt balanceSource v.toNat)
          (Store.activeMembers balanceSource participants)
  /-- The Byzantine validators hold at most β of the stake of each range of committees. -/
  byzantine : ∀ w ∈ J, ∀ k head state firstSlot lastSlot participants,
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants →
    ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      (Store.activeMembers state participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100
  /-- No honest validator is a known equivocator of an honest store. -/
  dishonest : ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
    ∀ v ∈ ((e.world k).state w).equivocatingIndices, v ∉ J

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

/-- The reserved bound gives the plain bound of Assumption 2 on each range the caller reads.

A range that starts after it ends has no members, so the bound holds for it without the reserve. -/
theorem WeightBounds.sourceByzantine {balanceSource : BeaconState preset fork}
    {first last shift : ℕ} (weights : WeightBounds e balanceSource first last shift) :
    ∀ w ∈ J, ∀ k head firstSlot lastSlot participants,
      (e.world k).time = first →
      ((e.world k).state w).getCommitteesBetweenSlots head firstSlot lastSlot =
        .ok participants →
      ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
        (Store.activeMembers balanceSource participants) J
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 := by
  intro w honest k head firstSlot lastSlot participants time read
  by_cases ordered : firstSlot ≤ lastSlot
  · have reserved := weights.sourceReserve w honest k head firstSlot lastSlot participants time
      ordered read
    exact ⟨by decide, by omega⟩
  · rw [Store.getCommitteesBetweenSlots_of_gt (UInt64.not_le.mp ordered), Except.ok.injEq] at read
    subst read
    refine ByzantineStakeAtMost.of_subset _ (by decide) fun v member => ?_
    exact absurd (Store.mem_activeMembers.mp member).1 Std.TreeSet.not_mem_emptyc

/-- No held block precedes the anchor, even when the anchor state has a different slot. -/
theorem _root_.EthLib.Consensus.Store.Reachable.anchorSlot_le_block
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block) : anchorBlock.slot ≤ block.slot := by
  induction reachable generalizing root block with
  | anchor made =>
    obtain ⟨r, _, blocks, _⟩ := getForkchoiceStore_maps made
    rw [blocks, getElem?_insert_root] at known
    split at known
    · cases known; exact UInt64.le_refl _
    · simp at known
  | tick _ step ih => exact ih ((Store.onTick_frame step).2.2.1 ▸ known)
  | attestation _ step ih => exact ih ((Store.onAttestation_frame step).2.1 ▸ known)
  | attesterSlashing _ step ih => exact ih ((Store.onAttesterSlashing_frame step).2.1 ▸ known)
  | payloadAttestation _ step ih =>
    exact ih ((Store.onPayloadAttestationMessage_onlyPtcVotes step).frame.2.1 ▸ known)
  | envelope _ step ih => exact ih ((Store.onExecutionPayloadEnvelope_frame step).2.1 ▸ known)
  | inclusionList _ step ih => exact ih ((Store.onInclusionList_frame step).2.1 ▸ known)
  | @block before after checks sources signed reached step ih =>
    rcases Store.onBlock_same_or_insert step with same | ⟨r, hashed, fresh, blocks, _⟩
    · exact ih (same ▸ known)
    rw [blocks, getElem?_insert_root] at known
    split at known
    · cases known
      -- Admission walks to a held finalized block below the new block.
      obtain ⟨_, ⟨slot, slotOk, later⟩, checkpoint⟩ := Store.onBlock_checks hashed
        (by simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]) step
      unfold Store.getCheckpointBlock at checkpoint
      simp only [bind_ok_iff, mapError_ok_iff] at checkpoint
      obtain ⟨s, sOk, ancestor, walk, _⟩ := checkpoint
      rw [slotOk] at sOk
      cases sOk
      obtain ⟨b, found, lower⟩ := Store.getAncestor_le walk
      exact UInt64.le_trans (ih found) (UInt64.le_trans lower (UInt64.le_of_lt later))
    · exact ih known

/-- A successful ancestor walk reads blocks held by any reachable store with its first block. -/
theorem _root_.EthLib.Consensus.Store.Reachable.known_of_ancestor_walk
    {store receiver : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (received : Store.Reachable config anchorState anchorBlock receiver)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {node ancestor : ForkChoiceNode} {slot : Slot}
    (known : ∃ b, receiver.blocks[node.root]? = some b)
    (walk : store.getAncestor node slot = .ok ancestor) :
    ∃ b, receiver.blocks[ancestor.root]? = some b := by
  induction node using Store.getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [Store.getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [Store.getAncestor_of_le found le] at walk
    cases walk
    exact known
  | case3 node block found above parentFound =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst eq
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    obtain ⟨other, held⟩ := known
    have eq := same _ _ _ found held
    subst other
    -- A successful step cannot leave the anchor for a strictly lower held parent.
    have notAnchor : block ≠ anchorBlock := by
      intro eq
      have bound := reachable.anchorSlot_le_block parentFound
      rw [eq] at lower
      exact (UInt64.not_lt.mpr bound) lower
    obtain ⟨_, _, _, produced⟩ := received.blockStatesFromParents held
    obtain ⟨pre, _, _, _, _, preFound, _⟩ := produced notAnchor
    have parentKnown := received.known_of_blockState preFound
    rw [Store.getAncestor_step found above parentFound lower] at walk
    exact ih parentKnown walk
  | case5 node block found above parent parentFound notLower =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst eq
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p eq
        rw [parentFound, Option.some.injEq] at eq
        subst eq
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- A past slot's attestation deadline plus delay precedes the current clock. -/
theorem DelayFits.deadline_add_le {Δ time : ℕ} {slot current : Slot} {clock : UInt64}
    (fits : DelayFits fork config genesisTimeMs Δ)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time)
    (currentOk : computeSlotAtTimeMs config genesisTimeMs clock = .ok current)
    (past : slot < current) : time + Δ ≤ clock.toNat := by
  obtain ⟨start, due, startOk, dueOk, atTime⟩ := deadline
  unfold computeSlotAtTimeMs at currentOk
  simp only [bind_ok_iff] at currentOk
  obtain ⟨elapsed, elapsedOk, divided⟩ := currentOk
  obtain ⟨_, elapsedValue⟩ := subChecked_ok_iff.mp elapsedOk
  obtain ⟨_, currentValue⟩ := divChecked_ok_iff.mp divided
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  -- The current clock bounds both checked operations at the next slot boundary.
  have nextBound : slot.toNat + 1 < 2 ^ 64 := lt_of_le_of_lt
    (by omega : slot.toNat + 1 ≤ current.toNat) current.toNat_lt
  let next := UInt64.ofNat (slot.toNat + 1)
  have nextValue : next.toNat = slot.toNat + 1 := UInt64.toNat_ofNat_of_lt nextBound
  have nextOk : addChecked slot 1 = .ok next :=
    addChecked_ok_iff.mpr ⟨by simpa using nextBound, by simpa using nextValue⟩
  have productLe : next.toNat * config.SLOT_DURATION_MS.toNat ≤ elapsed.toNat := by
    calc
      _ ≤ current.toNat * config.SLOT_DURATION_MS.toNat :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ elapsed.toNat := by rw [currentValue]; exact Nat.div_mul_le_self _ _
  have offsetBound : next.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 :=
    lt_of_le_of_lt productLe elapsed.toNat_lt
  let offset := UInt64.ofNat (next.toNat * config.SLOT_DURATION_MS.toNat)
  have offsetValue : offset.toNat = next.toNat * config.SLOT_DURATION_MS.toNat :=
    UInt64.toNat_ofNat_of_lt offsetBound
  have offsetOk : mulChecked next config.SLOT_DURATION_MS = .ok offset :=
    mulChecked_ok_iff.mpr ⟨offsetBound, offsetValue⟩
  have followingLe : genesisTimeMs.toNat + offset.toNat ≤ clock.toNat := by omega
  have followingBound : genesisTimeMs.toNat + offset.toNat < 2 ^ 64 :=
    lt_of_le_of_lt followingLe clock.toNat_lt
  let following := UInt64.ofNat (genesisTimeMs.toNat + offset.toNat)
  have followingValue : following.toNat = genesisTimeMs.toNat + offset.toNat :=
    UInt64.toNat_ofNat_of_lt followingBound
  have followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following := by
    simp only [computeTimeAtSlotMs, offsetOk, bind, Except.bind]
    exact addChecked_ok_iff.mpr ⟨followingBound, followingValue⟩
  have before := fits.2 slot next start due following nextOk startOk dueOk followingOk
  omega

omit [DecidablePred (· ∈ J)] in
/-- An honest supporter held the voted head when it could sign the recorded vote.

The caller computes ancestry in its own store; this does not yet transport that ancestry. -/
theorem Execution.past_head_of_honest_supporter
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n : ℕ}
    {state : BeaconState preset fork} {root : Root}
    (supporter : v ∈ ((e.world n).state u).supportersOf state ⟨root, .pending⟩) :
    ∃ attestation : Attestation preset fork, ∃ m < n, ∃ head block supported,
      ((e.world n).state u).latestMessages[v]? =
        some (LatestMessage.ofAttestation attestation) ∧
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world m).time ((e.world m).view v) ((e.world m).state v) attestation.data ∧
      ((e.world m).state v).getHead config = .ok head ∧
      ((e.world m).state v).blocks[head.root]? = some block ∧
      attestation.data.beaconBlockRoot = head.root ∧
      ((e.world n).state u).getSupportedNode (LatestMessage.ofAttestation attestation) =
        .ok supported ∧
      ((e.world n).state u).isAncestor supported ⟨root, .pending⟩ = .ok true := by
  obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
    ((e.world n).state u).exists_of_voteCountsFor
      (Store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨attestation, m, earlier, rfl, maySign⟩ :=
    e.exists_maySign_of_latestMessages anchorStore anchored caller honest latest
  have ⟨_, _, _, _, _, honestData, _⟩ := maySign
  obtain ⟨head, block, headState, advanced, headOk, known, _, _, made⟩ := honestData
  have dataRoot := (getAttestationData_eq_ok_iff.mp made).2.2.2.1
  exact ⟨attestation, m, earlier, head, block, supported, latest, maySign, headOk,
    known, dataRoot, supportedOk, descends⟩

set_option linter.unusedSectionVars false in
/-- An honest recorded supporter already held the supported block before the delivery deadline.

The witness comes from the signer's past head, not safety at the receiving endpoint.

The recorded vote is from a past slot, so its attestation deadline plus delay is before this call.

Receiver admission and finalized-chain compatibility are separate obligations. -/
theorem Execution.past_block_of_honest_supporter {Δ : ℕ}
    (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u)) (bounded : (e.world n).time ≤ last)
    {state : BeaconState preset fork} (within : state.RegistryWithinLimit) {root : Root}
    (supporter : v ∈ ((e.world n).state u).supportersOf state ⟨root, .pending⟩) :
    ∃ m < n, ∃ block : BeaconBlock preset fork,
      ((e.world m).state v).blocks[root]? = some block ∧
      (e.world m).time + Δ ≤ (e.world n).time := by
  have _ := slots
  have _ := within
  -- Use one attestation witness for both the accepted slot and the signed data.
  obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
    ((e.world n).state u).exists_of_voteCountsFor
      (Store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨a, msg, seen, rfl, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller latest
  obtain ⟨m, earlier, maySign⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
  obtain ⟨_, _, deadline, genesis, _, honestData, _⟩ := maySign
  obtain ⟨head, block, _, _, _, held, _, _, made⟩ := honestData
  have dataRoot := (getAttestationData_eq_ok_iff.mp made).2.2.2.1
  have supportedRoot := Store.getSupportedNode_root supportedOk
  have reached (w : ValidatorIndex) (hw : w ∈ J) (i : ℕ) :=
    e.reachable (fun w hw => (anchored w hw) ▸ Store.Reachable.anchor anchorStore) i w hw
  have genesisEq : ((e.world n).state u).genesisTimeMs = genesisTimeMs := by
    rw [(e.clock_bounds u n).1, anchored u caller, ← anchored v honest,
      ← (e.clock_bounds v m).1, genesis]
  obtain ⟨current, currentOk, past⟩ := origin.past
  have currentTime : computeSlotAtTimeMs config genesisTimeMs
      ((e.world n).state u).timeMs = .ok current := by
    have computed := mapError_ok_iff.mp currentOk
    change computeSlotAtTimeMs config ((e.world n).state u).genesisTimeMs
      ((e.world n).state u).timeMs = .ok current at computed
    simpa only [genesisEq] using computed
  have late := fits.deadline_add_le deadline currentTime past
  rw [upToDate.1] at late
  have known : ∃ b, ((e.world m).state v).blocks[supported.root]? = some b := by
    rw [supportedRoot]
    exact ⟨block, by simpa only [LatestMessage.ofAttestation, dataRoot] using held⟩
  unfold Store.isAncestor at descends
  simp only [bind_ok_iff] at descends
  obtain ⟨target, _, ancestor, walk, same⟩ := descends
  have sameRoot : ancestor.root = root := by
    by_cases gloas : .glamsterdam ≤ fork <;>
      simp_all [pure, Except.pure]
  obtain ⟨b, held⟩ := (reached u caller n).known_of_ancestor_walk (reached v honest m)
    (oneBlock u caller v honest n m bounded ((e.monotone_time earlier.le).trans bounded)) known walk
  exact ⟨m, earlier, b, sameRoot ▸ held, late⟩

/-- A duty target remains recent at the next slot, including an epoch boundary. -/
theorem epoch_recent_at_next_slot {slot next : Slot}
    (nextOk : addChecked slot 1 = .ok next) :
    computeEpochAtSlot preset slot = computeEpochAtSlot preset next ∨
      computeEpochAtSlot preset slot = saturatingSub (computeEpochAtSlot preset next) 1 := by
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  have quotient : (slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat +
        if preset.SLOTS_PER_EPOCH.toNat ∣ slot.toNat + 1 then 1 else 0 := Nat.succ_div
  by_cases same : computeEpochAtSlot preset slot = computeEpochAtSlot preset next
  · exact Or.inl same
  · right
    have different : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≠
        next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      intro eq
      exact same (UInt64.toNat_inj.mp (by simpa [computeEpochAtSlot] using eq))
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [nextNat]
      rw [nextNat] at different
      split at quotient <;> omega
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, saturatingSub]
    by_cases h : (1 : UInt64) < next / preset.SLOTS_PER_EPOCH
    · simp only [h, ite_true]
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
      simp only [UInt64.toNat_div, UInt64.toNat_one]
      rw [step]
      exact (Nat.add_sub_cancel _ _).symm
    · simp only [h, ite_false, UInt64.toNat_zero, UInt64.toNat_div]
      have : (next / preset.SLOTS_PER_EPOCH).toNat ≤ 1 := by
        simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_one, not_lt] using h
      simp only [UInt64.toNat_div] at this
      rw [step] at this
      exact Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_right this)

/-- A pre-Gloas duty vote passes validation at the next slot once its chain is held. -/
theorem validate_duty_at_next_slot {store : Store preset fork}
    {attestation : Attestation preset fork} {next : Slot}
    (preGloas : fork < .glamsterdam)
    (nextOk : addChecked attestation.data.slot 1 = .ok next)
    (currentOk : store.getCurrentSlot config = .ok next)
    (epoch : attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot)
    {target voted : BeaconBlock preset fork}
    (targetKnown : store.blocks[attestation.data.target.root]? = some target)
    (votedKnown : store.blocks[attestation.data.beaconBlockRoot]? = some voted)
    (notFuture : voted.slot ≤ attestation.data.slot)
    (checkpoint : store.getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root) :
    store.validateOnAttestation config attestation false = .ok () := by
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have past : attestation.data.slot < next := UInt64.lt_iff_toNat_lt.mpr (by
    simp only [UInt64.toNat_one] at nextNat
    omega)
  exact Store.validateOnAttestation_of_facts currentOk
    (epoch ▸ epoch_recent_at_next_slot nextOk) epoch targetKnown votedKnown notFuture
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) checkpoint past

/-- A fitting delay leaves time to process a duty vote before the next slot boundary. -/
theorem DelayFits.before_boundary {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {start following : UInt64} {time : ℕ}
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) :
    time + Δ < following.toNat := by
  obtain ⟨start', due, startOk', dueOk, timeEq⟩ := deadline
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  rw [timeEq]
  exact fits.2 slot next start due following nextOk startOk dueOk followingOk

/-- A slot no later than a representable boundary has a representable start time. -/
theorem exists_timeAtSlotMs_of_le {slot last : Slot} {lastTime : UInt64}
    (le : slot ≤ last)
    (lastOk : computeTimeAtSlotMs config genesisTimeMs last = .ok lastTime) :
    ∃ start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
      start.toNat = genesisTimeMs.toNat + slot.toNat * config.SLOT_DURATION_MS.toNat ∧
      start ≤ lastTime := by
  unfold computeTimeAtSlotMs at lastOk ⊢
  simp only [bind_ok_iff] at lastOk
  obtain ⟨offset, multiplied, added⟩ := lastOk
  obtain ⟨bound, offsetEq⟩ := mulChecked_ok_iff.mp multiplied
  obtain ⟨timeBound, timeEq⟩ := addChecked_ok_iff.mp added
  have productLe := Nat.mul_le_mul_right config.SLOT_DURATION_MS.toNat
    (UInt64.le_iff_toNat_le.mp le)
  have productBound : slot.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 := by omega
  have productEq := mulChecked_of_lt productBound
  have productNat := (mulChecked_ok_iff.mp productEq).2
  have sumBound : genesisTimeMs.toNat +
      (slot * config.SLOT_DURATION_MS).toNat < 2 ^ 64 := by omega
  have sumEq := addChecked_of_lt sumBound
  have sumNat := (addChecked_ok_iff.mp sumEq).2
  refine ⟨genesisTimeMs + slot * config.SLOT_DURATION_MS,
    ?_, by omega, UInt64.le_iff_toNat_le.mpr (by omega)⟩
  simp only [productEq, bind, Except.bind, sumEq]

/-- A fitting delay places the attestation deadline inside each representable slot. -/
theorem DelayFits.due_lt_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {start following due : UInt64}
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (dueOk : getAttestationDueMs config fork = .ok due) :
    due < config.SLOT_DURATION_MS := by
  have before := fits.2 slot next start due following nextOk startOk dueOk followingOk
  obtain ⟨start', startOk', startNat, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_refl slot) startOk
  obtain ⟨following', followingOk', followingNat, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_refl next) followingOk
  rw [startOk, Except.ok.injEq] at startOk'
  rw [followingOk, Except.ok.injEq] at followingOk'
  subst start'
  subst following'
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  rw [nextNat, Nat.add_mul, Nat.one_mul] at followingNat
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

omit [DecidablePred (· ∈ J)] in
/-- Prompt processing supplies both delivery events for a duty whose deadline has started. -/
theorem Execution.exists_duty_boundaries {Δ : ℕ}
    {slot next : Slot} {start following : UInt64} {time : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e following.toNat)
    {w : ValidatorIndex} (receiver : w ∈ J)
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time)
    (started : e.startTime ≤ time) :
    (∃ k, (e.world k).time + 1 = following.toNat ∧
      time + Δ ≤ (e.world k).time ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w)) ∧
    (∃ k, (e.world k).time = following.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w)) := by
  have before := fits.before_boundary nextOk startOk followingOk deadline
  have startedBefore : e.startTime < following.toNat := by omega
  obtain ⟨boundary, preboundary⟩ :=
    prompt w receiver next following followingOk startedBefore.le (Nat.le_refl _)
  obtain ⟨k, atTime, current⟩ := preboundary startedBefore
  exact ⟨⟨k, atTime, by omega, current⟩, boundary⟩

omit [DecidablePred (· ∈ J)] in
/-- A duty inside a complete slot interval has a vote before the endpoint's delivery cutoff. -/
theorem Execution.exists_voteAt_of_duty_interval {Δ : ℕ} {first time : ℕ}
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    {begin last slot : Slot} {beginTime endTime : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endOk : computeTimeAtSlotMs config genesisTimeMs last = .ok endTime)
    (started : e.startTime ≤ first) (fresh : first ≤ beginTime.toNat)
    (complete : endTime.toNat ≤ time)
    {v : ValidatorIndex} (honest : v ∈ J) {committeeIndex : CommitteeIndex}
    (afterBegin : begin ≤ slot) (beforeEnd : slot < last)
    (duty : assignment.committee v slot = some committeeIndex) :
    ∃ next start following deadline n attestation indexed,
      addChecked slot 1 = .ok next ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
      computeTimeAtSlotMs config genesisTimeMs next = .ok following ∧
      IsAttestationDeadline fork config genesisTimeMs slot deadline ∧
      first ≤ deadline ∧ deadline + Δ < following.toNat ∧ following.toNat ≤ time ∧
      VoteAt e v slot committeeIndex deadline n attestation indexed := by
  have slotLt := UInt64.lt_iff_toNat_lt.mp beforeEnd
  have lastBound := last.toNat_lt
  have nextBound : slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by simp; omega
  have nextOk := addChecked_of_lt nextBound
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have nextLe : slot + 1 ≤ last := UInt64.le_iff_toNat_le.mpr (by
    simp only [UInt64.toNat_one] at nextNat; omega)
  obtain ⟨startTime, startOk, startNat, _⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt beforeEnd) endOk
  obtain ⟨following, followingOk, _, followingLe⟩ :=
    exists_timeAtSlotMs_of_le nextLe endOk
  obtain ⟨beginTime', beginOk', _, beginLe⟩ := exists_timeAtSlotMs_of_le afterBegin startOk
  rw [beginOk, Except.ok.injEq] at beginOk'
  subst beginTime'
  obtain ⟨due, dueOk⟩ := fits.1
  have deadline : IsAttestationDeadline fork config genesisTimeMs slot
      (startTime.toNat + due.toNat) := ⟨startTime, due, startOk, dueOk, rfl⟩
  have beginLe := UInt64.le_iff_toNat_le.mp beginLe
  have followingLe := UInt64.le_iff_toNat_le.mp followingLe
  have firstLe : first ≤ startTime.toNat + due.toNat := by omega
  obtain ⟨n, attestation, indexed, vote⟩ := votes v honest slot committeeIndex _ duty deadline
    (started.trans firstLe) (started.trans firstLe)
    (by have := fits.before_boundary nextOk startOk followingOk deadline; omega)
  exact ⟨slot + 1, startTime, following, _, n, attestation, indexed,
    nextOk, startOk, followingOk, deadline, firstLe,
    fits.before_boundary nextOk startOk followingOk deadline, by omega, vote⟩

omit [DecidablePred (· ∈ J)] in
/-- Prefix safety applies to the head actually used by a late duty vote. -/
theorem VoteAt.head_supports_of_safe {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (start : ∀ u ∈ J, e.start u = anchor)
    {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {deadline n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (due : IsAttestationDeadline fork config genesisTimeMs slot deadline)
    {dueMs : UInt64} (dueOk : getAttestationDueMs config fork = .ok dueMs)
    (inSlot : dueMs < config.SLOT_DURATION_MS)
    {first time : ℕ} {root : Root} (afterFirst : first ≤ deadline) (before : deadline < time)
    (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root) :
    ∃ head block, ((e.world n).state v).getHead config = .ok head ∧
      ((e.world n).state v).blocks[head.root]? = some block ∧
      attestation.data.beaconBlockRoot = head.root ∧ block.slot ≤ slot ∧
      ((e.world n).state v).isAncestor head ⟨root, .pending⟩ = .ok true := by
  obtain ⟨_, _, head, block, headOk, held, same, past⟩ :=
    vote.data_head anchored anchorSlot start honest due dueOk inSlot
  refine ⟨head, block, headOk, held, same, past, ?_⟩
  exact safe deadline afterFirst before v honest n head vote.atTime
    (vote.atTime.symm ▸ vote.upToDate) headOk

omit [DecidablePred (· ∈ J)] in
/-- A signed honest vote in the safe interval supports the root wherever its tip is held. -/
theorem Execution.isAncestor_of_maySign_of_safe {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    (preGloas : fork < .glamsterdam)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {n k : ℕ}
    {data : AttestationData}
    (signed : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world n).time ((e.world n).view v) ((e.world n).state v) data)
    {first time : ℕ} {root : Root} (afterFirst : first ≤ (e.world n).time)
    (before : (e.world n).time < time)
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root)
    {rootBlock tip : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (aboveAnchor : anchorBlock.slot ≤ rootBlock.slot)
    (tipKnown : ((e.world k).state w).blocks[data.beaconBlockRoot]? = some tip) :
    ((e.world k).state w).isAncestor ⟨data.beaconBlockRoot, .pending⟩
      ⟨root, .pending⟩ = .ok true := by
  obtain ⟨committee, _, _, _, upToDate, honestData, _⟩ := signed
  obtain ⟨head, block, headState, state, headOk, _, _, _, made⟩ := honestData
  obtain ⟨_, _, _, dataRoot, _, _⟩ := getAttestationData_eq_ok_iff.mp made
  have supported := safe _ afterFirst before v honest n head rfl upToDate headOk
  have sourceKnown : ∃ b, ((e.world n).state v).blocks[root]? = some b := by
    unfold Store.isAncestor at supported
    simp only [bind_ok_iff] at supported
    obtain ⟨b, found, _⟩ := supported
    exact ⟨b, Store.block_ok_iff.mp found⟩
  obtain ⟨sourceBlock, sourceKnown⟩ := sourceKnown
  have eq := oneBlock v honest w receiver n k nBound kBound root sourceBlock rootBlock sourceKnown
    known
  subst sourceBlock
  have reached := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) k w receiver
  have transferred := Store.isAncestor_of_same_blocks reached preGloas
    (oneBlock v honest w receiver n k nBound kBound) sourceKnown known aboveAnchor
    ⟨tip, dataRoot ▸ tipKnown⟩ supported
  have pending := Store.getHead_pending preGloas headOk
  have headEq : head = ⟨data.beaconBlockRoot, .pending⟩ := by
    cases head
    simp_all
  exact headEq ▸ transferred

omit [DecidablePred (· ∈ J)] in
/-- Joint vote provenance puts its signing time before the endpoint and after its target floor. -/
theorem Execution.signing_time_in_range {anchor : Store preset fork}
    (start : ∀ u ∈ J, e.start u = anchor)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (earlier : n < k) {attestation : Attestation preset fork}
    (signed : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world n).time ((e.world n).view v) ((e.world n).state v) attestation.data)
    (origin : ((e.world k).state w).VoteOrigin config v attestation)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {due : UInt64} (dueOk : getAttestationDueMs config fork = .ok due)
    (inSlot : due < config.SLOT_DURATION_MS)
    {epoch : Epoch} {begin : Slot} {beginTime : UInt64} {first : ℕ}
    (beginOk : computeStartSlotAtEpoch preset epoch = .ok begin)
    (beginTimeOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (fresh : first ≤ beginTime.toNat) (rank : epoch ≤ attestation.data.target.epoch) :
    first ≤ (e.world n).time ∧ (e.world n).time < (e.world k).time := by
  obtain ⟨committee, _, deadline, genesis, current, honestData, _⟩ := signed
  obtain ⟨startTime, due', startOk, dueOk', timeEq⟩ := deadline
  have dueEq := Except.ok.inj (dueOk'.symm.trans dueOk)
  subst due'
  obtain ⟨head, block, headState, state, _, _, _, _, made⟩ := honestData
  have epochEq := target_epoch_eq_of_getAttestationData made
  have beginLe : begin ≤ attestation.data.slot := by
    have floor := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (UInt64.le_iff_toNat_le.mp rank)
    rw [epochEq, computeEpochAtSlot, UInt64.toNat_div] at floor
    rw [UInt64.le_iff_toNat_le, (computeStartSlotAtEpoch_ok_iff.mp beginOk).2]
    exact floor.trans (Nat.div_mul_le_self _ _)
  obtain ⟨beginTime', beginOk', _, timeLe⟩ := exists_timeAtSlotMs_of_le beginLe startOk
  have same := Except.ok.inj (beginOk'.symm.trans beginTimeOk)
  subst beginTime'
  constructor
  · have timeLe := UInt64.le_iff_toNat_le.mp timeLe
    omega
  · have timeLe := e.monotone_time earlier.le
    apply lt_of_le_of_ne timeLe
    intro sameTime
    have genesisEq : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
      have left := (e.clock_bounds v n).1
      have right := (e.clock_bounds w k).1
      rw [start v honest] at left
      rw [start w receiver] at right
      exact right.trans (left.symm.trans genesis)
    have sameClock : ((e.world k).state w).timeMs = ((e.world n).state v).timeMs :=
      UInt64.toNat_inj.mp (upToDate.1.trans (sameTime.symm.trans current.1.symm))
    have slotOk : ((e.world k).state w).getCurrentSlot config =
        .ok attestation.data.slot := by
      unfold Store.getCurrentSlot
      rw [genesisEq, sameClock]
      exact mapError_ok_iff.mpr (computeSlotAtTimeMs_inside startOk
        (current.1.trans timeEq) inSlot)
    obtain ⟨slot, slotOk', past⟩ := origin.past
    have eq := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst slot
    exact (UInt64.lt_irrefl _ past)

omit [DecidablePred (· ∈ J)] in
/-- A latest honest vote signed in the safe interval contributes its endpoint tally balance. -/
theorem Execution.mem_supportersOf_of_signed_in_range {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    (preGloas : fork < .glamsterdam)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {n k : ℕ}
    {attestation : Attestation preset fork}
    (signed : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world n).time ((e.world n).view v) ((e.world n).state v) attestation.data)
    (latest : ((e.world k).state w).latestMessages[v]? =
      some (LatestMessage.ofAttestation attestation))
    (counted : v ∉ ((e.world k).state w).equivocatingIndices)
    {first time : ℕ} {root : Root} (afterFirst : first ≤ (e.world n).time)
    (before : (e.world n).time < time)
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root)
    {rootBlock tip : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (aboveAnchor : anchorBlock.slot ≤ rootBlock.slot)
    (tipKnown : ((e.world k).state w).blocks[attestation.data.beaconBlockRoot]? = some tip)
    {state : BeaconState preset fork}
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
  have descends := e.isAncestor_of_maySign_of_safe anchored start oneBlock preGloas
    honest receiver signed afterFirst before nBound kBound safe known aboveAnchor tipKnown
  have check : ((e.world k).state w).voteCountsFor ⟨root, .pending⟩ v = true := by
    apply Store.voteCountsFor_of_check _ latest (by simpa using counted)
    simpa only [Store.getSupportedNode_of_lt preGloas, bind, Except.bind,
      LatestMessage.ofAttestation] using descends
  simp only [List.mem_toFinset, List.mem_map] at active
  obtain ⟨entry, member, eq⟩ := active
  simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨entry, ⟨member, eq ▸ check⟩, eq⟩

omit [DecidablePred (· ∈ J)] in
/-- A sufficiently recent latest vote supports the safe prefix, using only endpoint balances. -/
theorem Execution.mem_supportersOf_of_latest_rank {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    (preGloas : fork < .glamsterdam)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k : ℕ}
    {message : LatestMessage fork}
    (latest : ((e.world k).state w).latestMessages[v]? = some message)
    (counted : v ∉ ((e.world k).state w).equivocatingIndices)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) (bounded : (e.world k).time ≤ last)
    {due : UInt64} (dueOk : getAttestationDueMs config fork = .ok due)
    (inSlot : due < config.SLOT_DURATION_MS)
    {epoch : Epoch} {begin : Slot} {beginTime : UInt64} {first : ℕ}
    (beginOk : computeStartSlotAtEpoch preset epoch = .ok begin)
    (beginTimeOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (fresh : first ≤ beginTime.toNat) (rank : epoch ≤ message.rank)
    {root : Root}
    (safe : ∀ earlier, first ≤ earlier → earlier < (e.world k).time → SafeAt e earlier root)
    {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (aboveAnchor : anchorBlock.slot ≤ rootBlock.slot)
    {state : BeaconState preset fork}
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
  obtain ⟨attestation, m, seen, rfl, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start receiver latest
  obtain ⟨n, earlier, duty⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent k w seen) signed honest
  have epochRank : epoch ≤ attestation.data.target.epoch := by
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  have range := e.signing_time_in_range start honest receiver earlier duty origin upToDate
    dueOk inSlot beginOk beginTimeOk fresh epochRank
  obtain ⟨tip, tipKnown, _⟩ := origin.voted
  exact e.mem_supportersOf_of_signed_in_range anchored start oneBlock preGloas honest receiver
    duty latest counted range.1 range.2
    ((e.monotone_time (Nat.le_of_lt earlier)).trans bounded) bounded safe known aboveAnchor tipKnown
    active

omit [DecidablePred (· ∈ J)] in
/-- Honest stores with the same blocks compute the same cached target state under fixed checks. -/
theorem Execution.checkpointStates_eq_of_oneBlock {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    {u w : ValidatorIndex} (first : u ∈ J) (second : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {checkpoint : Checkpoint} {left right : BeaconState preset fork}
    (leftFound : ((e.world n).state u).checkpointStates[checkpoint]? = some left)
    (rightFound : ((e.world k).state w).checkpointStates[checkpoint]? = some right) :
    left = right := by
  obtain ⟨leftBase, leftSlot, leftBaseFound, leftSlotOk, leftRun⟩ :=
    e.checkpointStates_fixedChecks anchored (start u first) leftFound
  obtain ⟨rightBase, rightSlot, rightBaseFound, rightSlotOk, rightRun⟩ :=
    e.checkpointStates_fixedChecks anchored (start w second) rightFound
  have baseEq := e.blockStates_eq anchored first second (start u first) (start w second)
    (oneBlock u first w second n k nBound kBound) leftBaseFound rightBaseFound
  have slotEq := Except.ok.inj (leftSlotOk.symm.trans rightSlotOk)
  subst rightBase
  subst rightSlot
  exact Except.ok.inj (leftRun.symm.trans rightRun)

omit [DecidablePred (· ∈ J)] in
/-- A target state read after caching has the same fixed-check origin as an already cached state. -/
theorem Execution.targetState_fixedChecks {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (start : e.start w = anchor) {k : ℕ}
    {target : Checkpoint} {withTarget : Store preset fork} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).storeTargetCheckpointState config checks target =
      .ok withTarget)
    (read : withTarget.checkpointState target = .ok state) :
    ∃ base slot, ((e.world k).state w).blockStates[target.root]? = some base ∧
      computeStartSlotAtEpoch preset target.epoch = .ok slot ∧
      lookaheadState config checks base slot = .ok state := by
  unfold Store.storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst withTarget
    exact e.checkpointStates_fixedChecks anchored start (Store.checkpointState_ok_iff.mp read)
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at stored
    obtain ⟨computed, computedOk, rfl⟩ := stored
    have eq : computed = state := by
      have found := Store.checkpointState_ok_iff.mp read
      simpa using found
    subst computed
    exact checkpointState_run_of_compute computedOk

omit [DecidablePred (· ∈ J)] in
/-- Target-state agreement also holds when either honest store has just computed its cache entry. -/
theorem Execution.targetStates_eq_of_oneBlock {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    {u w : ValidatorIndex} (first : u ∈ J) (second : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {target : Checkpoint} {leftStore rightStore : Store preset fork}
    {left right : BeaconState preset fork}
    (leftStored : ((e.world n).state u).storeTargetCheckpointState config checks target =
      .ok leftStore)
    (leftRead : leftStore.checkpointState target = .ok left)
    (rightStored : ((e.world k).state w).storeTargetCheckpointState config checks target =
      .ok rightStore)
    (rightRead : rightStore.checkpointState target = .ok right) :
    left = right := by
  obtain ⟨leftBase, leftSlot, leftFound, leftSlotOk, leftRun⟩ :=
    e.targetState_fixedChecks anchored (start u first) leftStored leftRead
  obtain ⟨rightBase, rightSlot, rightFound, rightSlotOk, rightRun⟩ :=
    e.targetState_fixedChecks anchored (start w second) rightStored rightRead
  have baseEq := e.blockStates_eq anchored first second (start u first) (start w second)
    (oneBlock u first w second n k nBound kBound) leftFound rightFound
  have slotEq := Except.ok.inj (leftSlotOk.symm.trans rightSlotOk)
  subst rightBase
  subst rightSlot
  exact Except.ok.inj (leftRun.symm.trans rightRun)

omit [DecidablePred (· ∈ J)] in
/-- A duty attestation is accepted once its target block is held and its time checks pass. -/
theorem VoteAt.accepted_of_target_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot : Slot} {committeeIndex : CommitteeIndex} {deadline n k : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {targetBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[attestation.data.target.root]? = some targetBlock)
    (valid : ((e.world k).state w).validateOnAttestation config attestation false = .ok ()) :
    (∃ after, ((e.world k).state w).onAttestation config checks attestation false = .ok after) ∧
      ReadsAttestation config checks ((e.world k).state w) attestation indexed := by
  obtain ⟨sourceStore, sourceState, sourceStored, sourceRead, indexedOk, signed⟩ := vote.reads
  obtain ⟨base, boundary, baseFound, boundaryOk, ran⟩ :=
    e.targetState_fixedChecks anchored (start v honest) sourceStored sourceRead
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w receiver
  obtain ⟨receiverBase, receiverBaseFound, _, _⟩ := reached.blockStatesFromParents known
  have baseEq := e.blockStates_eq anchored honest receiver (start v honest) (start w receiver)
    (oneBlock v honest w receiver n k nBound kBound) baseFound receiverBaseFound
  subst receiverBase
  have computed : ((e.world k).state w).computeCheckpointState config checks
      attestation.data.target = .ok sourceState := by
    simpa [Store.computeCheckpointState, Store.blockState_ok_iff.mpr receiverBaseFound,
      boundaryOk, lookaheadState, bind, Except.bind, Except.mapError] using ran
  obtain ⟨withTarget, targetState, stored, read⟩ :=
    Store.exists_storeTargetCheckpointState computed
  have stateEq := e.targetStates_eq_of_oneBlock anchored start oneBlock honest receiver nBound
    kBound
    sourceStored sourceRead stored read
  subst targetState
  have committees := vote.committees sourceStore sourceState sourceStored sourceRead
  exact ⟨⟨_, Store.onAttestation_of_reads valid stored read committees indexedOk signed⟩,
    ⟨withTarget, sourceState, stored, read, indexedOk, signed⟩⟩

omit [DecidablePred (· ∈ J)] in
/-- A delivered duty is recorded at its next slot boundary and retained at later events. -/
theorem VoteAt.recorded_at_next_slot {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot next : Slot} {committeeIndex : CommitteeIndex} {deadline n arrival endpoint : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (dataSlot : attestation.data.slot = slot)
    (epoch : attestation.data.target.epoch = computeEpochAtSlot preset slot)
    (nextOk : addChecked slot 1 = .ok next)
    (currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok next)
    (late : deadline + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view w) ((e.world arrival).state w))
    (counted : v ∉ ((e.world arrival).state w).equivocatingIndices)
    (later : arrival ≤ endpoint) (arrivalBound : (e.world arrival).time ≤ last)
    {voted : BeaconBlock preset fork}
    (votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some voted)
    (notFuture : voted.slot ≤ slot)
    (checkpoint : ((e.world arrival).state w).getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root) :
    ∃ message, ((e.world endpoint).state w).latestMessages[v]? = some message ∧
      attestation.data.target.epoch ≤ message.rank := by
  obtain ⟨_, target, _, targetKnown, _, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
  have valid := validate_duty_at_next_slot preGloas (dataSlot ▸ nextOk) currentOk
    (epoch.trans (congrArg (computeEpochAtSlot preset) dataSlot).symm)
    targetKnown votedKnown (dataSlot ▸ notFuture) checkpoint
  obtain ⟨⟨after, accepted⟩, reads⟩ := vote.accepted_of_target_known anchored start oneBlock
    honest receiver (by have := vote.atTime; omega) arrivalBound targetKnown valid
  obtain ⟨message, latest, rank⟩ := vote.recorded_of_le sync honest receiver late upToDate
    accepted reads counted later
  refine ⟨message, latest, ?_⟩
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank

omit [DecidablePred (· ∈ J)] in
/-- An endpoint checkpoint read admits a supporting head at an earlier delivery event.

The boundary is no later than the supported block, so the descendant shares its checkpoint.

The earlier receiver need not already hold the supported block. -/
theorem Execution.blocks_of_endpoint_checkpoint {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam)
    {last : ℕ} (oneBlock : OneBlockPerRoot e last) (admitted : BlocksAdmitted e 0 Δ last)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {n arrival endpoint : ℕ}
    (arrivalBound : (e.world arrival).time ≤ last) (endpointBound : (e.world endpoint).time ≤ last)
    (late : (e.world n).time + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view w) ((e.world arrival).state w))
    (finalizedKnown : ∃ block,
      ((e.world arrival).state w).blocks[((e.world arrival).state w).finalizedCheckpoint.root]? =
        some block)
    {head : ForkChoiceNode} {root : Root} {headBlock rootBlock : BeaconBlock preset fork}
    (headKnown : ((e.world n).state v).blocks[head.root]? = some headBlock)
    (sourceKnown : ((e.world n).state v).blocks[root]? = some rootBlock)
    (supports : ((e.world n).state v).isAncestor head ⟨root, .pending⟩ = .ok true)
    {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset
      ((e.world arrival).state w).finalizedCheckpoint.epoch = .ok boundary)
    (aboveAnchor : anchorBlock.slot ≤ boundary) (belowRoot : boundary ≤ rootBlock.slot)
    (checkpoint : ((e.world endpoint).state w).getCheckpointBlock root
      ((e.world arrival).state w).finalizedCheckpoint.epoch =
        .ok ((e.world arrival).state w).finalizedCheckpoint.root) :
    ((e.world arrival).state w).blocks[head.root]? = some headBlock := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) n v honest
  have sourceCheckpoint := Store.getCheckpointBlock_of_same_blocks reached
    (oneBlock w receiver v honest endpoint n endpointBound (by omega)) boundaryOk aboveAnchor
    ⟨rootBlock, sourceKnown⟩ checkpoint
  have headCheckpoint := Store.getCheckpointBlock_of_isAncestor preGloas sourceKnown
    supports boundaryOk belowRoot sourceCheckpoint
  exact (e.blocks_of_partiallySynchronous sync oneBlock admitted anchored start honest receiver
    (by simpa using late) arrivalBound upToDate finalizedKnown
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) headKnown headCheckpoint).1

omit [DecidablePred (· ∈ J)] in
/-- Prefix agreement makes the finalized root known within the current-epoch horizon. -/
theorem Execution.finalized_known_of_prefix {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ u ∈ J, e.start u = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {horizon : Epoch} {last : ℕ} (chain : FinalizedPrefix e horizon last)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ last)
    {epoch : Epoch}
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) :
    ∃ block, ((e.world k).state w).blocks[
      ((e.world k).state w).finalizedCheckpoint.root]? = some block := by
  have forward := e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) k w receiver
  have justifiedLe := (forward.justified_epoch_le_current sound slots
    (UInt64.le_of_eq anchorSlot) epochOk).1
  have checkpoint := chain w receiver w receiver k k bounded bounded
    ((e.world k).state w).justifiedCheckpoint (Or.inl rfl)
    (forward.reachable.finalized_le_justified sound) (UInt64.le_trans justifiedLe inHorizon)
  obtain ⟨_, block, _, held, _, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
  exact ⟨block, held⟩

omit [DecidablePred (· ∈ J)] in
/-- Coverage by an earlier finalized checkpoint gives coverage by endpoint justification. -/
theorem Execution.justified_covers_of_finalized_covers {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ u ∈ J, e.start u = anchor)
    (preGloas : fork < .glamsterdam)
    {horizon : Epoch} {last : ℕ} (chain : FinalizedPrefix e horizon last)
    {w : ValidatorIndex} (receiver : w ∈ J) {arrival endpoint : ℕ}
    (later : arrival ≤ endpoint) (bounded : (e.world endpoint).time ≤ last)
    (inHorizon : ((e.world endpoint).state w).justifiedCheckpoint.epoch ≤ horizon)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world endpoint).state w).blocks[root]? = some block)
    (covered : ((e.world endpoint).state w).isAncestor
      ⟨((e.world arrival).state w).finalizedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true) :
    ((e.world endpoint).state w).isAncestor
      ⟨((e.world endpoint).state w).justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) endpoint w receiver
  have le := UInt64.le_trans (e.epochsLe_of_le w later).2
    (reached.finalized_le_justified sound)
  have checkpoint := chain w receiver w receiver arrival endpoint
    ((e.monotone_time later).trans bounded) bounded
    ((e.world endpoint).state w).justifiedCheckpoint (Or.inl rfl) le inHorizon
  obtain ⟨_, finalized, _, held, _, descends⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
  exact Store.isAncestor_trans_of_lt preGloas held known descends covered

omit [DecidablePred (· ∈ J)] in
/-- Endpoint finality compatibility admits a delayed head or covers its root by justification. -/
theorem Execution.blocks_or_justified_covers {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam)
    {last : ℕ} (oneBlock : OneBlockPerRoot e last) (admitted : BlocksAdmitted e 0 Δ last)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ u ∈ J, e.start u = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon last)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {n arrival endpoint : ℕ} (later : arrival ≤ endpoint)
    (bounded : (e.world endpoint).time ≤ last)
    (late : (e.world n).time + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view w) ((e.world arrival).state w))
    {arrivalEpoch endpointEpoch : Epoch}
    (arrivalOk : ((e.world arrival).state w).getCurrentStoreEpoch config = .ok arrivalEpoch)
    (endpointOk : ((e.world endpoint).state w).getCurrentStoreEpoch config = .ok endpointEpoch)
    (arrivalHorizon : arrivalEpoch ≤ horizon) (endpointHorizon : endpointEpoch ≤ horizon)
    {head : ForkChoiceNode} {root : Root} {headBlock rootBlock : BeaconBlock preset fork}
    (headKnown : ((e.world n).state v).blocks[head.root]? = some headBlock)
    (sourceKnown : ((e.world n).state v).blocks[root]? = some rootBlock)
    (known : ((e.world endpoint).state w).blocks[root]? = some rootBlock)
    (supports : ((e.world n).state v).isAncestor head ⟨root, .pending⟩ = .ok true)
    (compatible : (∃ boundary,
      computeStartSlotAtEpoch preset ((e.world arrival).state w).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ rootBlock.slot ∧
      ((e.world endpoint).state w).getCheckpointBlock root
        ((e.world arrival).state w).finalizedCheckpoint.epoch =
          .ok ((e.world arrival).state w).finalizedCheckpoint.root) ∨
      ((e.world endpoint).state w).isAncestor
        ⟨((e.world arrival).state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) :
    ((e.world arrival).state w).blocks[head.root]? = some headBlock ∨
      ((e.world endpoint).state w).isAncestor
        ⟨((e.world endpoint).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
  rcases compatible with ⟨boundary, boundaryOk, belowRoot, checkpoint⟩ | covered
  · left
    have arrivalBound := (e.monotone_time later).trans bounded
    exact e.blocks_of_endpoint_checkpoint sync preGloas oneBlock admitted anchored start
      honest receiver arrivalBound bounded late upToDate
      (e.finalized_known_of_prefix anchored sound start slots anchorSlot preGloas chain
        receiver arrivalBound arrivalOk arrivalHorizon) headKnown sourceKnown supports boundaryOk
      (e.anchorSlot_le_finalized_boundary anchored anchorSlot anchorBoundary
        (start w receiver) boundaryOk) belowRoot checkpoint
  · right
    have forward := e.forwardReachable
      (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) endpoint w receiver
    have justifiedLe := (forward.justified_epoch_le_current sound slots
      (UInt64.le_of_eq anchorSlot) endpointOk).1
    exact e.justified_covers_of_finalized_covers anchored sound start preGloas chain receiver
      later bounded (UInt64.le_trans justifiedLe endpointHorizon) known covered

/-- A complete duty epoch gives honest support unless justification already covers the root.

The tally state may be old; no comparison with the caller's balances is used.

Finality either permits head admission before the next boundary or already covers the root.

This is the late support step of arXiv 2405.00549v4, Lemma 2.

Head admission follows from endpoint finality compatibility before the next slot boundary. -/
theorem Execution.mem_supportersOf_of_duty_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {first time : ℕ} (oneBlock : OneBlockPerRoot e time) (admitted : BlocksAdmitted e 0 Δ time)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    (started : e.startTime ≤ first)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon time)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (few : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon → getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} <
        2 * total.toNat)
    {epoch : Epoch} {begin next : Slot} {beginTime endTime : UInt64}
    (beginOk : computeStartSlotAtEpoch preset epoch = .ok begin)
    (nextOk : addChecked begin preset.SLOTS_PER_EPOCH = .ok next)
    (beginTimeOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endTimeOk : computeTimeAtSlotMs config genesisTimeMs next = .ok endTime)
    (fresh : first ≤ beginTime.toNat) (complete : endTime.toNat ≤ time)
    {root : Root} (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (rootFinal : ∀ k' ≤ k, first ≤ (e.world k').time →
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ rootBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {state : BeaconState preset fork}
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (within : state.RegistryWithinLimit)
    {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset)
    (duty : ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
      assignment.committee v slot = some committeeIndex) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
  have _ := positive
  have _ := window
  have _ := ring
  have _ := large
  have _ := few
  have _ := stateOk
  have _ := within
  have forward := fun u hu j => e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) j u hu
  have rootAbove := (forward w receiver k).reachable.anchorSlot_le_block
    known
  obtain ⟨slot, committee, beginLe, slotLt, assigned⟩ := duty
  obtain ⟨followingSlot, slotTime, followingTime, deadline, n, attestation, indexed,
      nextSlotOk, slotTimeOk, followingTimeOk, deadlineOk, firstLe, beforeBoundary,
      boundaryLe, vote⟩ := e.exists_voteAt_of_duty_interval votes fits beginTimeOk endTimeOk
    started fresh complete honest beginLe slotLt assigned
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextSlotOk slotTimeOk followingTimeOk dueOk
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, notFuture⟩ :=
    vote.data_head anchored (UInt64.le_of_eq anchorSlot) start honest deadlineOk dueOk dueLt
  have supports := safe deadline firstLe (by omega) v honest n head vote.atTime
    (vote.atTime.symm ▸ vote.upToDate) headOk
  have sourceKnown : ((e.world n).state v).blocks[root]? = some rootBlock := by
    have test := supports
    unfold Store.isAncestor at test
    simp only [bind_ok_iff] at test
    obtain ⟨block, held, _⟩ := test
    have held := Store.block_ok_iff.mp held
    have eq := oneBlock v honest w receiver n k (by rw [vote.atTime]; omega) (by omega) root block
      rootBlock held known
    exact eq ▸ held
  have genesis : ∀ j, ((e.world j).state w).genesisTimeMs = genesisTimeMs := by
    intro j
    have left := (e.clock_bounds v n).1
    have right := (e.clock_bounds w j).1
    rw [start v honest] at left
    rw [start w receiver] at right
    exact right.trans (left.symm.trans vote.genesis)
  have epochExists : ∀ j, ∃ current,
      ((e.world j).state w).getCurrentStoreEpoch config = .ok current := by
    intro j
    obtain ⟨current, currentOk, _, _⟩ :=
      (forward w receiver j).slots_le_current slots (UInt64.le_of_eq anchorSlot)
    exact ⟨computeEpochAtSlot preset current, by
      simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨endpointEpoch, endpointOk⟩ := epochExists k
  have endpointHorizon := inHorizon w receiver k endpointEpoch (by omega) endpointOk
  obtain ⟨⟨pre, preTime, preLate, preCurrent⟩, ⟨boundary, boundaryTime, boundaryCurrent⟩⟩ :=
    e.exists_duty_boundaries fits (prompt.of_le boundaryLe) receiver nextSlotOk slotTimeOk
      followingTimeOk
      deadlineOk (started.trans firstLe)
  have preLe : pre ≤ k := by
    by_contra h
    have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp at bad
    omega
  obtain ⟨preEpoch, preEpochOk⟩ := epochExists pre
  have preHorizon := inHorizon w receiver pre preEpoch (by omega) preEpochOk
  rcases e.blocks_or_justified_covers sync preGloas oneBlock admitted anchored sound start
      slots anchorSlot anchorBoundary chain honest receiver preLe (by omega)
      (by simpa [vote.atTime] using preLate) preCurrent preEpochOk endpointOk preHorizon
      endpointHorizon headKnown sourceKnown known supports
      (rootFinal pre preLe (by omega) preCurrent) with admittedHead | covered
  swap
  · exact Or.inr covered
  have arrivalExists : ∃ arrival, pre ≤ arrival ∧ arrival ≤ k ∧
      (e.world arrival).time = followingTime.toNat ∧
      UpToDate config checks sources (e.world arrival).time ((e.world arrival).view w)
        ((e.world arrival).state w) := by
    by_cases same : followingTime.toNat = time
    · exact ⟨k, preLe, le_refl _, by omega, upToDate⟩
    · have boundaryBefore : boundary ≤ k := by
        by_contra h
        have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
        dsimp at bad
        omega
      have preBefore : pre ≤ boundary := by
        by_contra h
        have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
        dsimp at bad
        omega
      exact ⟨boundary, preBefore, boundaryBefore, boundaryTime, boundaryCurrent⟩
  obtain ⟨arrival, preArrival, arrivalLe, arrivalTime, arrivalCurrent⟩ := arrivalExists
  have currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok followingSlot := by
    unfold Store.getCurrentSlot
    rw [genesis arrival]
    have clock : ((e.world arrival).state w).timeMs = followingTime :=
      UInt64.toNat_inj.mp (arrivalCurrent.1.trans arrivalTime)
    rw [clock]
    exact mapError_ok_iff.mpr (computeSlotAtTimeMs_computeTimeAtSlotMs slots followingTimeOk)
  have votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some headBlock := dataRoot ▸ e.blocks_of_le preArrival admittedHead
  have targetRead := vote.data_target anchored anchorSlot anchorBoundary start honest
    (nonzero v honest n (by rw [vote.atTime]; omega))
  obtain ⟨targetBoundary, targetBlock, targetBoundaryOk, targetKnown, targetLe, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
  have targetAbove := (forward v honest n).reachable.anchorSlot_le_block
    targetKnown
  have receiverRead := Store.getCheckpointBlock_of_same_blocks
    (forward w receiver arrival).reachable (oneBlock v honest w receiver n arrival
      (by rw [vote.atTime]; omega) (by omega))
    targetBoundaryOk (UInt64.le_trans targetAbove targetLe) ⟨headBlock, votedKnown⟩ targetRead
  have anchorEmpty : anchor.equivocatingIndices = [] := by
    unfold getForkchoiceStore at anchored
    simp only [bind_ok_iff] at anchored
    obtain ⟨_, _, anchored⟩ := anchored
    split at anchored
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at anchored
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at anchored
      obtain ⟨_, _, _, _, rfl⟩ := anchored
      rfl
  have counted := fun j => e.not_mem_equivocatingIndices slots
    (fun u hu => (start u hu) ▸ anchorEmpty)
    receiver honest j
  obtain ⟨latest, latestOk, rank⟩ := vote.recorded_at_next_slot sync preGloas anchored start
    oneBlock honest receiver dataSlot dataEpoch nextSlotOk currentOk (by omega) arrivalCurrent
    (counted arrival) arrivalLe (by omega) votedKnown notFuture receiverRead
  have dutyEpoch : computeEpochAtSlot preset slot = epoch := by
    have b := (computeStartSlotAtEpoch_ok_iff.mp beginOk).2
    have nx := (addChecked_ok_iff.mp nextOk).2
    have lo := UInt64.le_iff_toNat_le.mp beginLe
    have hi := UInt64.lt_iff_toNat_lt.mp slotLt
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
  left
  exact e.mem_supportersOf_of_latest_rank anchored start oneBlock preGloas honest receiver
    latestOk (counted k) upToDate (by omega) dueOk dueLt beginOk beginTimeOk fresh
    (by simpa [dataEpoch, dutyEpoch] using rank)
    (fun earlier hfirst htime => safe earlier hfirst (by omega)) known rootAbove active

/-- Checkpoint provenance can depend on the block whose state holds the checkpoint. -/
private theorem walk_indexed_checkpoints {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {p : Root → Checkpoint → Prop}
    (anchor : ∀ root, store.blocks[root]? = some anchorBlock →
      CheckpointsSatisfy (p root) anchorState)
    (inherit : ∀ root (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block ≠ anchorBlock →
      (∃ parent, store.blockStates[block.parentRoot]? = some parent) →
      ∀ checkpoint, p block.parentRoot checkpoint → p root checkpoint)
    (reads : ∀ root (block : BeaconBlock preset fork) (parent : BeaconState preset fork),
      store.blocks[root]? = some block → block ≠ anchorBlock →
      store.blockStates[block.parentRoot]? = some parent →
      ∀ checks count middle cached,
        advanceSlots config checks count parent = .ok middle → processSlot middle = .ok cached →
        middle.slot < block.slot →
        ∀ checkpoint,
        (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) →
        getBlockRoot cached checkpoint.epoch = .ok checkpoint.root → p root checkpoint)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) : CheckpointsSatisfy (p root) state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · rw [anchored same]
    exact anchor root (same ▸ found)
  · obtain ⟨parent, checks, engine, signed, message, parentFound, transitioned⟩ := produced same
    obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok transitioned
    have parentHolds := walk_indexed_checkpoints reachable anchor inherit reads parentFound
    -- Move inherited checkpoints across the parent edge before following the slot run.
    have lifted : CheckpointsSatisfy (p root) parent :=
      ⟨inherit root block found same ⟨parent, parentFound⟩ _ parentHolds.1,
        inherit root block found same ⟨parent, parentFound⟩ _ parentHolds.2.1,
        inherit root block found same ⟨parent, parentFound⟩ _ parentHolds.2.2⟩
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, run⟩ := slotsOk
    apply (lifted.advanceSlots ?_ run).of_frame (frame_processBlock blockOk)
    intro i bounded middle cached advanced cachedOk
    apply reads root block parent found same parentFound checks i middle cached advanced cachedOk
    have atSlot := advanceSlots_slot i advanced
    rw [message] at bounded
    have lower := UInt64.lt_iff_toNat_lt.mp (stateTransition_slot transitioned).1
    rw [message] at lower
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- Justified checkpoints newer than the anchor belong to their stored block's chain. -/
theorem walk_checkpoint_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block ∧ block ≠ anchorBlock)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    CheckpointsSatisfy (fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
      ∃ boundary block, store.blocks[root]? = some block ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) state := by
  apply walk_indexed_checkpoints reachable (p := fun root checkpoint =>
    checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
      ∃ boundary block, store.blocks[root]? = some block ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) ?_ ?_ ?_ stored
  · intro root found
    have bound := UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState)
    exact ⟨.inl (UInt64.le_trans sound.ordered.2 bound), .inl bound,
      .inl (UInt64.le_trans sound.ordered.1 (UInt64.le_trans sound.ordered.2 bound))⟩
  · intro root block found different held checkpoint holds
    rcases holds with old | ⟨descends, boundary, parent, parentFound, boundaryOk, below, read⟩
    · exact .inl old
    · have parentLt := reachable.parent_slot_lt_of_ne_anchor aligned found different parentFound
      refine .inr ⟨Store.isAncestor_of_parent before found parentFound parentLt descends,
        boundary, block, found, boundaryOk, UInt64.le_trans below (UInt64.le_of_lt parentLt), ?_⟩
      have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) before found
        (UInt64.not_le.mpr (UInt64.lt_of_le_of_lt below parentLt)) parentFound parentLt
      simpa [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind, step]
        using read
  · intro root block parent found different held checks count middle cached run cachedOk middleLt
      checkpoint recent read
    by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
    · exact .inl old
    have recent' : checkpoint.epoch = getPreviousEpoch middle ∨
        checkpoint.epoch = getCurrentEpoch middle := by
      simpa only [getPreviousEpoch, getCurrentEpoch, processSlot_slot cachedOk] using recent
    rw [getBlockRoot_processSlot_of_recent_epoch positive window cachedOk recent'] at read
    obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
    have later : anchorState.slot ≤ start := by
      have epochLt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp old)
      rw [getCurrentEpoch_toNat] at epochLt
      have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
      have eq := (Base.Uint64.mulChecked_ok_iff.mp startOk).2
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have path : (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ start =
        .ok checkpoint.root := by
      cases count with
      | zero =>
        cases Except.ok.inj run
        exact reachable.blockState_history_ancestor aligned nonzero held read later .pending
      | succ count =>
        have atSlot := advanceSlots_slot (count + 1) run
        have greater : parent.slot < middle.slot := UInt64.lt_iff_toNat_lt.mpr (by omega)
        have computed : processSlots config checks parent middle.slot = .ok middle := by
          simp only [processSlots, bind_ok_iff, ensure_ok_iff]
          refine ⟨(), greater, ?_⟩
          have countEq : middle.slot.toNat - parent.slot.toNat = count + 1 := by omega
          simpa only [countEq] using run
        obtain ⟨readBlock, known, _⟩ := reachable.processSlots_history_slot_le nonzero child held
          computed read later (UInt64.le_trans aligned later)
        have ahead : lookaheadState config checks parent middle.slot = .ok middle := by
          simp [lookaheadState, greater, computed, Except.mapError]
        exact reachable.lookahead_history_ancestor aligned nonzero held known ahead read later
          .pending
    have checkpointRead : store.getCheckpointBlock block.parentRoot checkpoint.epoch =
        .ok checkpoint.root := by
      simpa [Store.getCheckpointBlock, startOk, Except.mapError, bind, Except.bind,
        Functor.map, Except.map, pure, Except.pure] using path
    obtain ⟨_, _, _, _, _, descends⟩ := Store.isAncestor_of_getCheckpointBlock before checkpointRead
    obtain ⟨parentBlock, parentFound⟩ := reachable.known_of_blockState held
    have startLt : start < block.slot := UInt64.lt_trans
      (UInt64.lt_iff_toNat_lt.mpr (getBlockRootAtSlot_ok_iff.mp read).1) middleLt
    have parentLt := reachable.parent_slot_lt_of_ne_anchor aligned found different parentFound
    refine .inr ⟨Store.isAncestor_of_parent before found parentFound parentLt descends,
      start, block, found, startOk, UInt64.le_of_lt startLt, ?_⟩
    have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) before found
      (UInt64.not_le.mpr startLt) parentFound parentLt
    simpa [Store.getCheckpointBlock, startOk, Except.mapError, bind, Except.bind, step]
      using checkpointRead

/-- Pull-up justification preserves the stored block's checkpoint ancestry. -/
theorem walk_pulled_checkpoint_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block ∧ block ≠ anchorBlock)
    {root : Root} {state pulled : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state)
    (computed : processJustificationAndFinalization state = .ok pulled) :
    CheckpointsSatisfy (fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
      ∃ boundary block, store.blocks[root]? = some block ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) pulled := by
  apply (walk_checkpoint_ancestor reachable sound before positive window aligned nonzero
    child stored).processJustification ?_ computed
  intro checkpoint recent read
  by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl old
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
  have later : anchorState.slot ≤ start := by
    have epochLt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp old)
    rw [getCurrentEpoch_toNat] at epochLt
    have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
    have eq := (Base.Uint64.mulChecked_ok_iff.mp startOk).2
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have path := reachable.blockState_history_ancestor aligned nonzero stored read later .pending
  have checkpointRead : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root := by
    simpa [Store.getCheckpointBlock, startOk, Except.mapError, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure] using path
  obtain ⟨_, _, _, _, _, descends⟩ := Store.isAncestor_of_getCheckpointBlock before checkpointRead
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  have notAnchor : block ≠ anchorBlock := by
    intro same
    obtain ⟨post, postOk, anchored, _⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same] at read
    have lt := (getBlockRootAtSlot_ok_iff.mp read).1
    have le := UInt64.le_iff_toNat_le.mp later
    omega
  have below : start ≤ block.slot := by
    rw [← (reachable.blockState_header found stored notAnchor).1]
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (getBlockRootAtSlot_ok_iff.mp read).1)
  exact .inr ⟨descends, start, block, found, startOk, below, checkpointRead⟩

end Models.Network

end EthLib.Consensus
