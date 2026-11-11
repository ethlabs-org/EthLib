module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSets
public import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
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
  /-- The balance states read in this short-horizon result are at most two epochs apart. -/
  nearby : ∀ w ∈ J, ∀ k state, first ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    (getCurrentEpoch state).toNat ≤ (getCurrentEpoch balanceSource).toNat + 2 ∧
      (getCurrentEpoch balanceSource).toNat ≤ (getCurrentEpoch state).toNat + 2
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
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ)
    (oneBlock : OneBlockPerRoot e)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
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
    (compatible : ∀ w ∈ J, ∀ k, (e.world n).time ≤ (e.world k).time →
      (e.world k).time ≤ time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world n).state u).getCheckpointBlock root
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (receiverUpToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
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
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} := by
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

/-- A complete later duty epoch makes each assigned honest tally voter support the safe prefix.

The tally state may be old; no comparison with the caller's balances is used.

The head block is admitted before the next boundary, and its vote is recorded at that boundary.

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
    (known : ∃ block, ((e.world k).state w).blocks[root]? = some block)
    {state : BeaconState preset fork}
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (within : state.RegistryWithinLimit)
    {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset)
    (duty : ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
      assignment.committee v slot = some committeeIndex) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
  sorry

end Models.Network

end EthLib.Consensus
