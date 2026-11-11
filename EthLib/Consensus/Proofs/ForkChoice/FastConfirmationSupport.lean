module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSets
public import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.Transition.RunKept

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
  sorry

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
