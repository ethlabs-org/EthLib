module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSets
public import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedOrigins
public import EthLib.Consensus.Proofs.Transition.RunKept
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.HonestAggregation
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

/-- Each honest validator processes messages before and at each slot boundary.

The slots are those that start at the start of the execution or later.

Pre-boundary processing admits delivered blocks before the next tick can change finality.

Boundary processing admits votes after their slot has ended.

This is a processing hypothesis, not a consequence of receipt in a network view.

It makes explicit the processing needed in addition to the network bound of
arXiv 2405.00549v4, Section 2. -/
def Prompt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ w ∈ J, ∀ slot start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    e.startTime ≤ start.toNat →
    (∃ k, (e.world k).time = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w)) ∧
    (e.startTime < start.toNat → ∃ k, (e.world k).time + 1 = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w))

/-- The committees that an honest store reads for a range of slots are those of the assignment.

An honest validator is in the committees of the range when the assignment gives it a slot there.

The agreement is restricted to actual heads and past ranges.

For a target-state comparison, a common state supplies the hypotheses of `RunKept.committeesKept`.

The assignment link remains separate: a free assignment is not determined by a transition. -/
structure CommitteesFollow
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop where
  /-- Honest duties use the actual head's committees for the past slots read by the rule. -/
  assigned : ∀ w ∈ J, ∀ k head current first last participants,
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).getCurrentSlot config = .ok current → last < current →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok participants →
    ∀ v ∈ J, v ∈ participants ↔
      ∃ slot committeeIndex, first ≤ slot ∧ slot ≤ last ∧
        assignment.committee v slot = some committeeIndex
  /-- The common-state witnesses for the target and head committee comparison. -/
  common : ∀ w ∈ J, ∀ k head headState current v attestation targetState,
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

/-- The head of an honest store follows the honest support of a block, Lemma 2 in the store.

The store is up to date, and the parent of the block is on the chain of its head.

The block is in the filtered tree of the store.

The committees are those from the slot after the parent to the slot before the current one.

Count the honest supporters of the block twice, and add the honest voters for its parent.

The sum exceeds the weight of those committees plus the boost.

The balances are those of the justified state of the store.

Then the block is on the chain of the head.

The tree part of Lemma 2 in issue 1458 is to give this fact.

It needs a cap on the weight of a sibling.

The reads field prevents a failed committee computation from making descent vacuous. -/
structure HeadFollowsSupport
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) [DecidablePred (· ∈ J)] : Prop where
  /-- A head has the balance and committee reads needed for every past range. -/
  reads : ∀ w ∈ J, ∀ k head,
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    ∃ state current score nodes,
      ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state ∧
      ((e.world k).state w).getCurrentSlot config = .ok current ∧
      computeProposerScore config state = .ok score ∧
      ((e.world k).state w).getFilteredNodeTree config = .ok nodes ∧
      ∀ first last, last < current → ∃ participants weight,
        ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok participants ∧
        ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state first last =
          .ok weight
  /-- Honest support above the sibling cap makes the head follow a viable child. -/
  follows : ∀ w ∈ J, ∀ k head state root block parentBlock current first last beforeBlock maximum score
    nodes parentParticipants,
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).block root = .ok block →
    ((e.world k).state w).block block.parentRoot = .ok parentBlock →
    ((e.world k).state w).getCurrentSlot config = .ok current →
    addChecked parentBlock.slot 1 = .ok first → subChecked current 1 = .ok last →
    subChecked block.slot 1 = .ok beforeBlock →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state first last =
      .ok maximum →
    computeProposerScore config state = .ok score →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first beforeBlock =
      .ok parentParticipants →
    ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes →
    ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true →
    maximum.toNat + score.toNat <
      stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).parentVotersOf state parentParticipants block parentBlock |
            v ∈ J} +
        2 * stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} →
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true

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
  /-- Counterfactual reads under the call's balances must succeed before margins can be compared. -/
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
  /-- The call's balance source also satisfies the bound on every committee range it reads. -/
  sourceByzantine : ∀ w ∈ J, ∀ k head firstSlot lastSlot participants,
    (e.world k).time = first →
    ((e.world k).state w).getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants →
    ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (Store.activeMembers balanceSource participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100
  /-- The Byzantine validators hold at most β of the stake of each range of committees. -/
  byzantine : ∀ w ∈ J, ∀ k head state firstSlot lastSlot participants,
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants →
    ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      (Store.activeMembers state participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100
  /-- No honest validator is a known equivocator of an honest store. -/
  dishonest : ∀ w ∈ J, ∀ k, ∀ v ∈ ((e.world k).state w).equivocatingIndices, v ∉ J

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

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

omit [DecidablePred (· ∈ J)] in
/-- A recorded honest vote retains both its accepted slot and its signing provenance. -/
theorem Execution.exists_signed_origin_of_latestMessages
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    {v : ValidatorIndex} {message : LatestMessage fork}
    (latest : ((e.world n).state u).latestMessages[v]? = some message) :
    ∃ attestation : Attestation preset fork,
      message = LatestMessage.ofAttestation attestation ∧
      ((e.world n).state u).VoteOrigin config v attestation ∧
      ∃ m ∈ (e.world n).view u,
        (v, attestation.data) ∈ statements config checks anchorState anchorBlock m := by
  let Origin := fun (view : Set (Message preset fork)) (store : Store preset fork) =>
    ∀ v message, store.latestMessages[v]? = some message →
      ∃ a : Attestation preset fork, message = LatestMessage.ofAttestation a ∧
        store.VoteOrigin config v a ∧
        ∃ m ∈ view, (v, a.data) ∈ statements config checks anchorState anchorBlock m
  have transfer {s t : Store preset fork} {view nextView : Set (Message preset fork)}
      (old : Origin view s) (incl : view ⊆ nextView)
      (messages : t.latestMessages = s.latestMessages)
      (blocks : ∀ {r : Root} {b : BeaconBlock preset fork},
        s.blocks[r]? = some b → t.blocks[r]? = some b)
      (states : ∀ {c : Checkpoint} {b : BeaconState preset fork},
        s.checkpointStates[c]? = some b → t.checkpointStates[c]? = some b)
      (clock : ∀ {slot}, s.getCurrentSlot config = .ok slot →
        ∃ next, t.getCurrentSlot config = .ok next ∧ slot ≤ next) : Origin nextView t := by
    intro v message found
    obtain ⟨a, eq, origin, m, seen, signed⟩ := old v message (messages ▸ found)
    exact ⟨a, eq, origin.mono blocks states clock, m, incl seen, signed⟩
  have attestationStep {s t : Store preset fork} {view : Set (Message preset fork)}
      {a : Attestation preset fork} {fromBlock : Bool}
      (reached : Store.Reachable config anchorState anchorBlock s) (old : Origin view s)
      (carried : ∃ m ∈ view, attestationStatements (config := config) (checks := checks)
        anchorState anchorBlock a ⊆ statements config checks anchorState anchorBlock m)
      (step : s.onAttestation config checks a fromBlock = .ok t) : Origin view t := by
    intro v message found
    rcases Store.onAttestation_latestMessages_cases step found with previous | ⟨rfl, origin⟩
    · obtain ⟨a, eq, origin, rest⟩ := old v message previous
      refine ⟨a, eq, origin.mono (fun h => (Store.onAttestation_frame step).2.1 ▸ h)
        (Store.onAttestation_checkpointStates_of_found step) (fun h =>
          ⟨_, h ▸ (Store.onAttestation_sameClock step).getCurrentSlot, UInt64.le_refl _⟩), rest⟩
    · obtain ⟨m, seen, carries⟩ := carried
      refine ⟨a, rfl, origin, m, seen, carries ?_⟩
      -- Recover the exact accepted data, not just its lossy latest-message projection.
      have handled := step
      unfold Store.onAttestation at handled
      simp only [bind_ok_iff] at handled
      obtain ⟨_, _, stored, storing, target, targetOk, _, _, indexed, indexedOk,
        valid, validOk, handled⟩ := handled
      split at handled
      · rename_i validTrue
        have indexedOk := mapError_ok_iff.mp indexedOk
        have dataSame : indexed.data = a.data := by
          obtain ⟨indices, indicesOk, _⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
          obtain ⟨indexed', made, _, dataSame, _⟩ :=
            getIndexedAttestation_of_getAttestingIndices indicesOk
          exact Except.ok.inj (indexedOk.symm.trans made) ▸ dataSame
        obtain ⟨target', indexed', targetFound, _, indexedOk', voter⟩ := origin.committees
        have targetEq : target = target' := by
          have targetHeld : t.checkpointStates[a.data.target]? = some target := by
            have eq : stored.updateLatestMessages indexed.attestingIndices.data.toList a = t :=
              Except.ok.inj handled
            rw [← eq]
            exact Store.checkpointState_ok_iff.mp targetOk
          exact Option.some.inj (targetHeld.symm.trans targetFound)
        have indexedEq : indexed = indexed' := by
          rw [targetEq] at indexedOk
          exact Except.ok.inj (indexedOk.symm.trans indexedOk')
        refine ⟨s, indexed, reached, ⟨stored, target, storing, targetOk, indexedOk,
          by simpa [validTrue] using mapError_ok_iff.mp validOk⟩, ?_⟩
        exact ⟨by simpa [indexedEq] using voter, dataSame.symm⟩
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at handled
  have invariant : ∀ i, Origin ((e.world i).view u) ((e.world i).state u) := by
    intro i
    induction i with
    | zero =>
      intro v message found
      change (e.start u).latestMessages[v]? = some message at found
      obtain ⟨_, _, empty, _⟩ := getForkchoiceStore_fields anchorStore
      rw [anchored u caller, empty] at found
      simp at found
    | succ i ih =>
      have extend {s} (old : Origin ((e.world i).view u) s) :
          Origin ((e.world (i + 1)).view u) s :=
        transfer old (e.monotone_view u (Nat.le_succ i)) rfl (fun h => h) (fun h => h)
          (fun h => ⟨_, h, UInt64.le_refl _⟩)
      rcases e.state_succ i u with same | ⟨_, moved⟩
      · exact same ▸ extend ih
      apply extend
      have forward := e.forwardReachable
        (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) i u caller
      cases moved with
      | tick later bounded step =>
        exact transfer ih (fun _ h => h) (Store.onTick_checkpointStates_latestMessages step).2
          (fun h => (Store.onTick_frame step).2.2.1 ▸ h)
          (fun h => (Store.onTick_checkpointStates_latestMessages step).1 ▸ h)
          (Store.exists_getCurrentSlot_onTick_ge (UInt64.le_iff_toNat_le.mpr
            (by
              change _ ≤ (UInt64.ofNat (e.world i).time).toNat
              have eq : (UInt64.ofNat (e.world i).time).toNat = (e.world i).time :=
                UInt64.toNat_ofNat_of_lt bounded
              rw [eq]
              exact later)) step)
      | attestation seen step =>
        exact attestationStep forward.reachable ih ⟨_, seen, fun _ h => h⟩ step
      | attesterSlashing _ step =>
        exact transfer ih (fun _ h => h)
          (Store.onAttesterSlashing_checkpointStates_latestMessages step).2
          (fun h => (Store.onAttesterSlashing_frame step).2.1 ▸ h)
          (fun h => (Store.onAttesterSlashing_checkpointStates_latestMessages step).1 ▸ h)
          (fun h => ⟨_, h ▸ (Store.onAttesterSlashing_sameClock step).getCurrentSlot,
            UInt64.le_refl _⟩)
      | block seen step =>
        rename_i signed
        unfold Store.onBlockWithVotes at step
        simp only [bind_ok_iff, ← Array.foldlM_toList] at step
        obtain ⟨blocked, blockOk, voted, votedOk, slashedOk⟩ := step
        let P := fun s => Store.Reachable config anchorState anchorBlock s ∧
          Origin ((e.world i).view u) s
        have blockedP : P blocked := ⟨forward.reachable.block blockOk,
          transfer ih (fun _ h => h) (Store.onBlock_checkpointStates_latestMessages blockOk).2
            (Store.onBlock_blocks_of_found blockOk)
            (fun h => (Store.onBlock_checkpointStates_latestMessages blockOk).1 ▸ h)
            (fun h => ⟨_, h ▸ (Store.onBlock_sameClock blockOk).getCurrentSlot,
              UInt64.le_refl _⟩)⟩
        have foldStep : ∀ {α : Type} (xs : List α) (f : Store preset fork → α →
            Except ForkChoiceError (Store preset fork)),
            (∀ a ∈ xs, ∀ s t, P s → f s a = .ok t → P t) →
            ∀ s t, P s → xs.foldlM f s = .ok t → P t := by
          intro α xs f
          induction xs with
          | nil =>
            intro _ s t holds step
            simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at step
            exact step ▸ holds
          | cons a rest ih =>
            intro keeps s t holds step
            rw [List.foldlM_cons, bind_ok_iff] at step
            obtain ⟨mid, first, restOk⟩ := step
            exact ih (fun a mem => keeps a (List.mem_cons_of_mem _ mem)) mid t
              (keeps a List.mem_cons_self s mid holds first) restOk
        have votedP : P voted := foldStep _ _ (fun a mem s t holds step =>
          ⟨holds.1.attestation step, attestationStep holds.1 holds.2
            ⟨.block signed, seen, fun x hx => Or.inl ⟨a, by simpa using mem, hx⟩⟩ step⟩)
          blocked voted blockedP votedOk
        exact (foldlM_ok_invariant P (fun s _ t holds step =>
          ⟨holds.1.attesterSlashing step,
            transfer holds.2 (fun _ h => h)
              (Store.onAttesterSlashing_checkpointStates_latestMessages step).2
              (fun h => (Store.onAttesterSlashing_frame step).2.1 ▸ h)
              (fun h => (Store.onAttesterSlashing_checkpointStates_latestMessages step).1 ▸ h)
              (fun h => ⟨_, h ▸ (Store.onAttesterSlashing_sameClock step).getCurrentSlot,
                UInt64.le_refl _⟩)⟩) votedP slashedOk).2
      | payloadAttestation _ step =>
        obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes step
        rw [same]
        exact transfer ih (fun _ h => h) rfl (fun h => h) (fun h => h)
          (fun h => ⟨_, h, UInt64.le_refl _⟩)
      | envelope _ step =>
        obtain ⟨_, _, _, _, _, record, same⟩ := Store.onExecutionPayloadEnvelope_ok step
        rw [same]
        obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
        exact transfer ih (fun _ h => h) rfl (fun h => h) (fun h => h)
          (fun h => ⟨_, h, UInt64.le_refl _⟩)
      | inclusionList _ step =>
        obtain ⟨_, _, same⟩ := Store.onInclusionList_ok ‹_› step
        rw [same]
        exact transfer ih (fun _ h => h) rfl (fun h => h) (fun h => h)
          (fun h => ⟨_, h, UInt64.le_refl _⟩)
  exact invariant n v message latest

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
    (fits : DelayFits fork config genesisTimeMs Δ) (oneBlock : OneBlockPerRoot e)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
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
  obtain ⟨a, rfl, origin, msg, seen, signed⟩ :=
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
    (oneBlock u caller v honest n m) known walk
  exact ⟨m, earlier, b, sameRoot ▸ held, late⟩

/-- Step 5, the transport: the bound of step 4 holds in each honest store at a later time.

The caller is an honest validator whose store is up to date and holds the bound of step 4.

Its ranges of committees end at the slot before its own, and at the slot before the block.

From the time of the call to just before the later time, the block is safe.

So each honest vote of those slots supports the block.

The receiver is an honest validator whose store is up to date at the later time.

Its ranges of committees end at the slot before its own, and at the slot before the block.

The honest validators vote as their duty asks from the start of the execution.

Each honest store starts as the same store, which holds no vote.

The proof follows three lemmas of [verified-fast-confirmation][vfc].

Two are `honest_supporters_sum_le_Sval_window` and `weak_base_discharged_window`.

The third is `bval_endpoint_strip_window_uniform`.

The counting step `honest_ratio_of_new_votes` takes the place of its fixed committees.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honest_support_of_safe {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ)
    (oneBlock : OneBlockPerRoot e)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {balanceSource : BeaconState preset fork}
    {slot firstSlot lastSlot beforeBlock : Slot} {block parentBlock : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {proposerScore maximumSupport : Gwei}
    (callerHead : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximumSupport)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head firstSlot
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit) (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes balanceSource) ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head balanceSource
      root = .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head balanceSource root =
      .ok adversary)
    (confirmed : ((e.world n).state u).isOneConfirmed config head balanceSource
      (((e.world n).state u).tallyVotes balanceSource) root = .ok true)
    (base : maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    {time : ℕ} (later : (e.world n).time ≤ time)
    (weights : WeightBounds e balanceSource (e.world n).time time shift)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon)
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
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (receiverUpToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (rootFinal : ∀ k' ≤ k,
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ block.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current last : Slot} {maximum score : Gwei}
    {receiverParticipants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverLastOk : subChecked current 1 = .ok last)
    (receiverMaximumOk : ((e.world k).state w).computeCommitteeWeightBetweenSlots
      receiverHead.root state firstSlot last = .ok maximum)
    (scoreOk : computeProposerScore config state = .ok score)
    (receiverParticipantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root
      firstSlot beforeBlock = .ok receiverParticipants) :
    maximum.toNat + score.toNat <
      stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block
            parentBlock | v ∈ J} +
        2 * stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
  sorry

/-- Step 5, the induction: a block that holds the bound of step 4 is safe up to a last time.

The caller and its bound are those of `Execution.honest_support_of_safe`.

The parent of the block is safe from the time of the call to the last time.

Take a time of that range such that the block is safe at each earlier time of the range.

Then each honest store holds the block in its filtered tree or below its justified block.

Step 6 gives that fact from the other checks of the rule.

The proof is a strong induction on the time.

It follows `safeFrom_of_headStep_at` of [verified-fast-confirmation][vfc].

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_of_support {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ)
    (oneBlock : OneBlockPerRoot e)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) (follows : HeadFollowsSupport e)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (noVotes : anchor.latestMessages.isEmpty)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {balanceSource : BeaconState preset fork}
    {slot firstSlot lastSlot beforeBlock : Slot} {block parentBlock : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {proposerScore maximumSupport : Gwei}
    (callerHead : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximumSupport)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head firstSlot
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit) (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes balanceSource) ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head balanceSource
      root = .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head balanceSource root =
      .ok adversary)
    (confirmed : ((e.world n).state u).isOneConfirmed config head balanceSource
      (((e.world n).state u).tallyVotes balanceSource) root = .ok true)
    (base : maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    {limit : ℕ} (weights : WeightBounds e balanceSource (e.world n).time limit shift)
    (compatible : ∀ w ∈ J, ∀ k, (e.world n).time ≤ (e.world k).time →
      (e.world k).time ≤ limit →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world n).state u).getCheckpointBlock root
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root)
    (parentSafe : ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time block.parentRoot)
    (viable : ∀ time, (e.world n).time ≤ time → time ≤ limit →
      (∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root) →
      CoveredOrViableAt e time root) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root := by
  sorry

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
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e)
    {w : ValidatorIndex} (receiver : w ∈ J)
    {slot next : Slot} {start following : UInt64} {time : ℕ}
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
  obtain ⟨boundary, preboundary⟩ := prompt w receiver next following followingOk startedBefore.le
  obtain ⟨k, atTime, current⟩ := preboundary startedBefore
  exact ⟨⟨k, atTime, by omega, current⟩, boundary⟩

omit [DecidablePred (· ∈ J)] in
/-- A duty inside a complete slot interval has a vote before the endpoint's delivery cutoff. -/
theorem Execution.exists_voteAt_of_duty_interval {Δ : ℕ}
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    {begin last slot : Slot} {beginTime endTime : UInt64} {first time : ℕ}
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
    (start : ∀ u ∈ J, e.start u = anchor) (oneBlock : OneBlockPerRoot e)
    (preGloas : fork < .glamsterdam)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {n k : ℕ}
    {data : AttestationData}
    (signed : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world n).time ((e.world n).view v) ((e.world n).state v) data)
    {first time : ℕ} {root : Root} (afterFirst : first ≤ (e.world n).time)
    (before : (e.world n).time < time)
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
  have eq := oneBlock v honest w receiver n k root sourceBlock rootBlock sourceKnown known
  subst sourceBlock
  have reached := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) k w receiver
  have transferred := Store.isAncestor_of_same_blocks reached preGloas
    (oneBlock v honest w receiver n k) sourceKnown known aboveAnchor
    ⟨tip, dataRoot ▸ tipKnown⟩ supported
  have pending := Store.getHead_pending preGloas headOk
  have headEq : head = ⟨data.beaconBlockRoot, .pending⟩ := by
    cases head
    simp_all
  exact headEq ▸ transferred

omit [DecidablePred (· ∈ J)] in
/-- A latest honest vote signed in the safe interval contributes its endpoint tally balance. -/
theorem Execution.mem_supportersOf_of_signed_in_range {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) (oneBlock : OneBlockPerRoot e)
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
    (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root)
    {rootBlock tip : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (aboveAnchor : anchorBlock.slot ≤ rootBlock.slot)
    (tipKnown : ((e.world k).state w).blocks[attestation.data.beaconBlockRoot]? = some tip)
    {state : BeaconState preset fork}
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
  have descends := e.isAncestor_of_maySign_of_safe anchored start oneBlock preGloas
    honest receiver signed afterFirst before safe known aboveAnchor tipKnown
  have check : ((e.world k).state w).voteCountsFor ⟨root, .pending⟩ v = true := by
    apply Store.voteCountsFor_of_check _ latest (by simpa using counted)
    simpa only [Store.getSupportedNode_of_lt preGloas, bind, Except.bind,
      LatestMessage.ofAttestation] using descends
  simp only [List.mem_toFinset, List.mem_map] at active
  obtain ⟨entry, member, eq⟩ := active
  simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨entry, ⟨member, eq ▸ check⟩, eq⟩

omit [DecidablePred (· ∈ J)] in
/-- Honest stores with the same blocks compute the same cached target state under fixed checks. -/
theorem Execution.checkpointStates_eq_of_oneBlock {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) (oneBlock : OneBlockPerRoot e)
    {u w : ValidatorIndex} (first : u ∈ J) (second : w ∈ J) {n k : ℕ}
    {checkpoint : Checkpoint} {left right : BeaconState preset fork}
    (leftFound : ((e.world n).state u).checkpointStates[checkpoint]? = some left)
    (rightFound : ((e.world k).state w).checkpointStates[checkpoint]? = some right) :
    left = right := by
  obtain ⟨leftBase, leftSlot, leftBaseFound, leftSlotOk, leftRun⟩ :=
    e.checkpointStates_fixedChecks anchored (start u first) leftFound
  obtain ⟨rightBase, rightSlot, rightBaseFound, rightSlotOk, rightRun⟩ :=
    e.checkpointStates_fixedChecks anchored (start w second) rightFound
  have baseEq := e.blockStates_eq anchored first second (start u first) (start w second)
    (oneBlock u first w second n k) leftBaseFound rightBaseFound
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
    (start : ∀ u ∈ J, e.start u = anchor) (oneBlock : OneBlockPerRoot e)
    {u w : ValidatorIndex} (first : u ∈ J) (second : w ∈ J) {n k : ℕ}
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
    (oneBlock u first w second n k) leftFound rightFound
  have slotEq := Except.ok.inj (leftSlotOk.symm.trans rightSlotOk)
  subst rightBase
  subst rightSlot
  exact Except.ok.inj (leftRun.symm.trans rightRun)

omit [DecidablePred (· ∈ J)] in
/-- A duty attestation is accepted once its target block is held and its time checks pass. -/
theorem VoteAt.accepted_of_target_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) (oneBlock : OneBlockPerRoot e)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot : Slot} {committeeIndex : CommitteeIndex} {deadline n k : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
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
    (oneBlock v honest w receiver n k) baseFound receiverBaseFound
  subst receiverBase
  have computed : ((e.world k).state w).computeCheckpointState config checks
      attestation.data.target = .ok sourceState := by
    simpa [Store.computeCheckpointState, Store.blockState_ok_iff.mpr receiverBaseFound,
      boundaryOk, lookaheadState, bind, Except.bind, Except.mapError] using ran
  obtain ⟨withTarget, targetState, stored, read⟩ :=
    Store.exists_storeTargetCheckpointState computed
  have stateEq := e.targetStates_eq_of_oneBlock anchored start oneBlock honest receiver
    sourceStored sourceRead stored read
  subst targetState
  have committees := vote.committees sourceStore sourceState sourceStored sourceRead
  exact ⟨⟨_, Store.onAttestation_of_reads valid stored read committees indexedOk signed⟩,
    ⟨withTarget, sourceState, stored, read, indexedOk, signed⟩⟩

omit [DecidablePred (· ∈ J)] in
/-- An endpoint checkpoint read admits a supporting head at an earlier delivery event.

The boundary is no later than the supported block, so the descendant shares its checkpoint.

The earlier receiver need not already hold the supported block. -/
theorem Execution.blocks_of_endpoint_checkpoint {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {n arrival endpoint : ℕ}
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
    (oneBlock w receiver v honest endpoint n) boundaryOk aboveAnchor
    ⟨rootBlock, sourceKnown⟩ checkpoint
  have headCheckpoint := Store.getCheckpointBlock_of_isAncestor preGloas sourceKnown
    supports boundaryOk belowRoot sourceCheckpoint
  exact (e.blocks_of_partiallySynchronous sync oneBlock admitted anchored start honest receiver
    (by simpa using late) upToDate finalizedKnown
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) headKnown headCheckpoint).1

omit [DecidablePred (· ∈ J)] in
/-- Prefix agreement makes the finalized root known within the current-epoch horizon. -/
theorem Execution.finalized_known_of_prefix {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ u ∈ J, e.start u = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) :
    ∃ block, ((e.world k).state w).blocks[
      ((e.world k).state w).finalizedCheckpoint.root]? = some block := by
  have forward := e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) k w receiver
  have justifiedLe := (forward.justified_epoch_le_current sound slots
    (UInt64.le_of_eq anchorSlot) epochOk).1
  have checkpoint := chain w receiver w receiver k k
    ((e.world k).state w).justifiedCheckpoint (Or.inl rfl)
    (forward.reachable.finalized_le_justified sound) (UInt64.le_trans justifiedLe inHorizon)
  obtain ⟨_, block, _, held, _, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
  exact ⟨block, held⟩

omit [DecidablePred (· ∈ J)] in
/-- Every realized finalized boundary stays at or above an epoch-aligned anchor. -/
theorem Execution.anchorSlot_le_finalized_boundary {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {w : ValidatorIndex} (start : e.start w = anchor) {k : ℕ} {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset
      ((e.world k).state w).finalizedCheckpoint.epoch = .ok boundary) :
    anchorBlock.slot ≤ boundary := by
  obtain ⟨_, _, _, _, _, finalized, _, _⟩ := getForkchoiceStore_anchor anchored
  have epochs := (e.epochsLe_of_le w (Nat.zero_le k)).2
  simp only [Execution.world_zero, World.initial, start, finalized] at epochs
  have rounded : anchorState.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH =
      anchorState.slot := by
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at anchorBoundary
    rw [anchorSlot, computeStartSlotAtEpoch_computeEpochAtSlot] at anchorBoundary
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, decide_eq_true_eq] at anchorBoundary
    have h := (computeStartSlotAtEpoch_ok_iff.mp
      (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot)).2
    have le : (anchorState.slot / preset.SLOTS_PER_EPOCH *
        preset.SLOTS_PER_EPOCH).toNat ≤ anchorState.slot.toNat := by
      rw [h, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_mul_le_self _ _
    have zero := congrArg UInt64.toNat anchorBoundary
    simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
    have upper := anchorState.slot.toNat_lt
    have lower := (anchorState.slot / preset.SLOTS_PER_EPOCH *
      preset.SLOTS_PER_EPOCH).toNat_lt
    apply UInt64.toNat_inj.mp
    omega
  have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
    (UInt64.le_iff_toNat_le.mp epochs)
  have anchorValue := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot)).2
  rw [rounded] at anchorValue
  rw [anchorSlot, UInt64.le_iff_toNat_le,
    (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2, anchorValue]
  exact mono

omit [DecidablePred (· ∈ J)] in
/-- Coverage by an earlier finalized checkpoint gives coverage by endpoint justification. -/
theorem Execution.justified_covers_of_finalized_covers {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ u ∈ J, e.start u = anchor)
    (preGloas : fork < .glamsterdam)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {w : ValidatorIndex} (receiver : w ∈ J) {arrival endpoint : ℕ}
    (later : arrival ≤ endpoint)
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
    ((e.world endpoint).state w).justifiedCheckpoint (Or.inl rfl) le inHorizon
  obtain ⟨_, finalized, _, held, _, descends⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
  exact Store.isAncestor_trans_of_lt preGloas held known descends covered

omit [DecidablePred (· ∈ J)] in
/-- Endpoint finality compatibility admits a delayed head or covers its root by justification. -/
theorem Execution.blocks_or_justified_covers {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ u ∈ J, e.start u = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {n arrival endpoint : ℕ} (later : arrival ≤ endpoint)
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
    exact e.blocks_of_endpoint_checkpoint sync preGloas oneBlock admitted anchored start
      honest receiver late upToDate
      (e.finalized_known_of_prefix anchored sound start slots anchorSlot preGloas chain
        receiver arrivalOk arrivalHorizon) headKnown sourceKnown supports boundaryOk
      (e.anchorSlot_le_finalized_boundary anchored anchorSlot anchorBoundary
        (start w receiver) boundaryOk) belowRoot checkpoint
  · right
    have forward := e.forwardReachable
      (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) endpoint w receiver
    have justifiedLe := (forward.justified_epoch_le_current sound slots
      (UInt64.le_of_eq anchorSlot) endpointOk).1
    exact e.justified_covers_of_finalized_covers anchored sound start preGloas chain receiver
      later (UInt64.le_trans justifiedLe endpointHorizon) known covered

/-- A complete duty epoch gives honest support unless justification already covers the root.

The tally state may be old; no comparison with the caller's balances is used.

Finality either permits head admission before the next boundary or already covers the root.

This is the late support step of arXiv 2405.00549v4, Lemma 2.

The statement is under review; head admission must be derived, not assumed as vote delivery. -/
theorem Execution.mem_supportersOf_of_duty_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    {first time : ℕ} (started : e.startTime ≤ first)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon)
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
  sorry

end Models.Network

end EthLib.Consensus
