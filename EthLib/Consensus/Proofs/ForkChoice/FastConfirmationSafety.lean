module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationResets

/-!
# Statements: safety of the fast confirmation rule

This file states step 8 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The target is the paper's long-horizon Theorem 1.

The weight and delivery interfaces are under review and are not frozen.

The proofs are placeholders, and each statement may still change.

An honest validator calls the rule at the start of each slot of a run of slots.

The block that the last call stores is then on the chain of the head of each honest store.

That holds from the start of the next slot to a last time.

The first statement reads the checks of step 6 and the walk of the rule off one call.

The second keeps a block of that walk safe, by an induction on the time.

At each time it goes up the walk from the start of the rule to the block.

Step 5 gives the honest support of each block of the walk in each honest store.

Step 6 gives that the last block is not filtered out, so no block before it is.

The third statement is the theorem, by an induction on the calls.

The induction keeps three facts on the block that a call stores.

The block is safe from the start of the next slot.

A block of the current epoch or the one before is also safe from the call itself.

For a block of the current epoch, the rule has checked the target, as `TargetChecked` says.

Each start of a call holds the first two facts.

The block stored before holds them by the induction.

Step 7 gives them for the finalized block and for the observed justified block.

The theorem takes Assumption 2 of the paper at each call, as `RuleBounds` holds it.

It takes the facts of Casper FFG as hypotheses, with a horizon.

It derives the honest vote of a justified checkpoint and the honest third from Assumption 2.

`RuleBounds` bounds the adverse shift of subset weights and requires observable margin for it.

The theorem does not cover a confirmed block that the rule restores after a restart.

Two theorems of [verified-fast-confirmation][vfc] give the result there.

The first is `accepted_confirmed_root_safe_from_next_slot`.

The second is `Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold`.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- Step 8, one call: the stored block is a start, or passed the checks along a confirmed walk.

The start and its three cases are those of `onFastConfirmation_confirmedRoot`.

A later block has passed the checks of step 6 from that start.

It is a root of the walk from the start to the head.

That block and each root before it in the walk are one-confirmed.

Each known block must sit at a later slot than its known parent.

The checks read the head of the slot before in the store after the call.

The proof joins `getLatestConfirmed_checked` and `findLatestConfirmedDescendant_eq_or`.

Both read the same start of the same call. -/
theorem onFastConfirmation_checked {fcr after : FastConfirmationStore}
    (lower : store.ParentsBelow)
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head slot start, store.getHead config = .ok head ∧
      store.getCurrentSlot config = .ok slot ∧
      after.previousSlotHead = fcr.currentSlotHead ∧
      after.currentSlotHead = head.root ∧
      (∀ next, addChecked slot 1 = .ok next →
        isStartSlotAtEpoch preset next = .ok true →
        after.previousEpochGreatestUnrealizedCheckpoint = store.unrealizedJustifiedCheckpoint) ∧
      (∀ next, addChecked slot 1 = .ok next →
        isStartSlotAtEpoch preset next = .ok false →
        after.previousEpochGreatestUnrealizedCheckpoint =
          fcr.previousEpochGreatestUnrealizedCheckpoint) ∧
      (isStartSlotAtEpoch preset slot = .ok true →
        after.currentEpochObservedJustifiedCheckpoint =
          after.previousEpochGreatestUnrealizedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.currentEpochObservedJustifiedCheckpoint) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        after.currentEpochObservedJustifiedCheckpoint = fcr.currentEpochObservedJustifiedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.previousEpochObservedJustifiedCheckpoint) ∧
      (start = fcr.confirmedRoot ∧
          store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
          (isStartSlotAtEpoch preset slot = .ok true →
            store.isConfirmedChainSafe config after head.root fcr.confirmedRoot = .ok true) ∨
        start = store.finalizedCheckpoint.root ∨
        start = after.currentEpochObservedJustifiedCheckpoint.root ∧
          isStartSlotAtEpoch preset slot = .ok true ∧
          (∃ observedBlock epoch,
            store.block after.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
            store.getCurrentStoreEpoch config = .ok epoch ∧
            Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
          store.unrealizedJustification head.root =
            .ok after.currentEpochObservedJustifiedCheckpoint) ∧
      (after.confirmedRoot = start ∨
        store.Checked config after head.root start after.confirmedRoot ∧
        ∃ balanceSource chain later,
          store.checkpointState after.currentEpochObservedJustifiedCheckpoint =
            .ok balanceSource ∧
          store.getAncestorRoots head.root start = .ok (chain ++ after.confirmedRoot :: later) ∧
          ∀ member ∈ chain ++ [after.confirmedRoot], store.isOneConfirmed config head.root
            balanceSource (store.tallyVotes balanceSource) member = .ok true) := by
  sorry

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- Assumption 2 of the paper at the calls of the rule that one validator makes.

The calls are those of a run: one call at each event of a list, from a first store of the rule.

Each call weighs with the state of its observed justified checkpoint, the source of balances.

From the call to the last time, `WeightBounds` bounds the adverse shift of support margins.

In the pulled-up state of the head of a call, take the committees of the epoch so far.

The Byzantine validators hold at most β of their stake.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

No honest validator is a known equivocator of the store of a call.

The fields name stores of the run alone, so an execution can hold them. -/
structure RuleBounds
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) [DecidablePred (· ∈ J)] (u : ValidatorIndex) (events : List ℕ)
    (first : FastConfirmationStore) (margin limit : ℕ) : Prop where
  /-- From each call on, the honest stores weigh as the source of balances of the call does. -/
  weights : ∀ calls n fcr after checkpoint balanceSource, events[calls]? = some n →
    ((events.take calls).map fun k => (e.world k).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) first = .ok fcr →
    ((e.world n).state u).onFastConfirmation config fcr = .ok after →
    (checkpoint = after.currentEpochObservedJustifiedCheckpoint ∨
      checkpoint = after.previousEpochObservedJustifiedCheckpoint) →
    ((e.world n).state u).checkpointState checkpoint = .ok balanceSource →
    WeightBounds e balanceSource (e.world n).time limit margin ∧ balanceSource.RegistryWithinLimit ∧
      EffectiveBalancesAligned balanceSource
  /-- The measured tally exceeds the rule's conservative threshold by the weight shift.

  This is an observable margin, not an assumption about the unknown honest supporters. -/
  slack : ∀ n ∈ events, ∀ head state root block parent firstSlot lastSlot beforeBlock
    slot participants maximum score support discount adversary,
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    ((e.world n).state u).block root = .ok block →
    ((e.world n).state u).block block.parentRoot = .ok parent →
    addChecked parent.slot 1 = .ok firstSlot → subChecked slot 1 = .ok lastSlot →
    subChecked block.slot 1 = .ok beforeBlock →
    ((e.world n).state u).getCommitteesBetweenSlots head.root firstSlot beforeBlock =
      .ok participants →
    ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root state firstSlot lastSlot =
      .ok maximum → computeProposerScore config state = .ok score →
    ((e.world n).state u).isOneConfirmed config head.root state
      (((e.world n).state u).tallyVotes state) root = .ok true →
    ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes state)
      ⟨root, .pending⟩ = .ok support →
    ((e.world n).state u).computeEmptySlotSupportDiscount config head.root state root =
      .ok discount →
    ((e.world n).state u).getAdversarialWeight config head.root state root = .ok adversary →
    maximum.toNat + score.toNat + 2 * adversary.toNat + margin <
      discount.toNat + 2 * support.toNat
  /-- Alignment is needed in the pulled-up state, not just the observed checkpoint state. -/
  headAligned : ∀ n ∈ events, ∀ head state,
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
    EffectiveBalancesAligned state
  /-- The Byzantine validators hold at most β of the committees of the epoch so far. -/
  byzantine : ∀ n ∈ events, ∀ head state slot epochStart lastSlot participants,
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
    subChecked slot 1 = .ok lastSlot →
    ((e.world n).state u).getCommitteesBetweenSlots head.root epochStart lastSlot =
      .ok participants →
    ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      (Store.activeMembers state participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100
  /-- The honest validators of the slots still to come hold their share, with the margin. -/
  remaining : ∀ n ∈ events, ∀ head state slot epochStart lastSlot participants total soFar,
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
    subChecked slot 1 = .ok lastSlot →
    ((e.world n).state u).getCommitteesBetweenSlots head.root epochStart lastSlot =
      .ok participants →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root state epochStart
      lastSlot = .ok soFar →
    3 * ((total.toNat - soFar.toNat) / 100 *
        (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat)) + margin ≤
      3 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∉ participants ∧ v ∈ J}
  /-- No honest validator is a known equivocator of the store of a call. -/
  dishonest : ∀ n ∈ events, ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

/-- Step 8, the walk: a block that the rule confirms after a safe start is safe up to a last time.

The caller is an honest validator whose store is up to date.

The block is a root of the walk from the start of the rule to the head of the caller.

That block and each root before it in the walk are one-confirmed.

The start is safe from the call to the last time.

Take a time of that range such that the block is safe at each earlier time of the range.

Then each honest store holds the block in its filtered tree or below its justified block.

Step 6 gives that fact from the other checks of the rule.

A store that holds the block in its filtered tree holds each block before it there.

The honest stores weigh as the source of balances of the caller does, up to the last time.

The proof is a strong induction on the time, and at each time an induction along the walk.

It does not use `Execution.safeAt_of_support`, which asks for a parent that is safe before.

A block of the walk is not filtered out only because the last block is not.

So the blocks of the walk are safe together at each time, not one after the other.

A theorem of [verified-fast-confirmation][vfc] gives the same result.

It is `safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_of_walk {Δ : ℕ} (sync : e.Synchronous Δ)
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
    (lower : ((e.world n).state u).ParentsBelow)
    {head : ForkChoiceNode} {start root : Root} {balanceSource : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ root :: later))
    (allConfirmed : ∀ member ∈ chain ++ [root], ((e.world n).state u).isOneConfirmed config
      head.root balanceSource (((e.world n).state u).tallyVotes balanceSource) member = .ok true)
    (within : balanceSource.RegistryWithinLimit) (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {limit shift : ℕ} (weights : WeightBounds e balanceSource (e.world n).time limit shift)
    (compatible : ∀ member ∈ chain ++ [root], ∀ w ∈ J, ∀ k,
      (e.world n).time ≤ (e.world k).time → (e.world k).time ≤ limit →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world n).state u).getCheckpointBlock member
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root)
    (slack : ∀ member ∈ chain ++ [root], ∀ block parent firstSlot lastSlot beforeBlock
      slot participants maximum score support discount adversary,
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      ((e.world n).state u).block member = .ok block →
      ((e.world n).state u).block block.parentRoot = .ok parent →
      addChecked parent.slot 1 = .ok firstSlot → subChecked slot 1 = .ok lastSlot →
      subChecked block.slot 1 = .ok beforeBlock →
      ((e.world n).state u).getCommitteesBetweenSlots head.root firstSlot beforeBlock =
        .ok participants →
      ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root balanceSource
        firstSlot lastSlot = .ok maximum →
      computeProposerScore config balanceSource = .ok score →
      ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes balanceSource)
        ⟨member, .pending⟩ = .ok support →
      ((e.world n).state u).computeEmptySlotSupportDiscount config head.root balanceSource member =
        .ok discount →
      ((e.world n).state u).getAdversarialWeight config head.root balanceSource member =
        .ok adversary →
      maximum.toNat + score.toNat + 2 * adversary.toNat + shift <
        discount.toNat + 2 * support.toNat)
    (startSafe : ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time start)
    (viable : ∀ time, (e.world n).time ≤ time → time ≤ limit →
      (∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root) →
      CoveredOrViableAt e time root) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root := by
  sorry

/-- Statement target for long-horizon safety, with interfaces still under review.

The bound includes at least the next-slot boundary, so its conclusion is not an empty interval.

Positive weight shift additionally requires the measured residual in `RuleBounds.slack`.

An honest validator calls the rule at the events of a list, with its store up to date.

The calls are at the starts of consecutive slots, and the first store of the rule is the anchor's.

Each honest store starts as the store of the anchor, which holds no vote.

No checkpoint of the state of the anchor is of a later epoch than that state.

An epoch has more than one slot.

The network is synchronous, and the delay fits in a slot.

The honest validators vote as their duty asks, and are prompt.

The committees of the stores follow the assignment, and the head follows honest support.

Those two facts are parts of issue 1458.

Partial synchrony delivers blocks into views; `BlocksAdmitted` supplies handler admission.

A target with an honest quorum is included within an epoch, Assumption 3.

Up to the horizon, the facts of Casper FFG hold.

The finalized block of an honest store is on the chain of each later justified checkpoint.

Two justified checkpoints of one epoch are the same.

Each counting state bounds Byzantine current-or-previous-epoch voters against its active stake.

This bound gives an honest signer directly, without a reference-state drift.

The margin covers the drift of such a state from the pulled-up state of a head, over two epochs.

Assumption 2 holds at each call, with that margin, as `RuleBounds` says.

Each honest store up to the last time is in an epoch at most the horizon.

Then the block that the last call stores is safe from the start of the next slot.

It stays safe to the last time.

The proof is a direct induction on the calls, retaining the checks of each call.

Its property is the three facts of the head of this file.

`Execution.justifiedByHonestVote` and `Execution.honestThirdPins` give two inputs of step 6.

The head of the slot before, as the rule tracks it, was the head of the call before.

The call before the first slot of an epoch records the observed justified checkpoint.

It is one slot before the call that reads it, so `Execution.safeAt_observed` applies.

The reference is `confirmed_root_safe_from_next_slot` in [verified-fast-confirmation][vfc].

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_confirmedRoot {Δ : ℕ} (sync : e.Synchronous Δ)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) (follows : HeadFollowsSupport e)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ)
    (included : TargetIncluded e)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon) (unique : OneJustifiedPerEpoch e horizon)
    {threshold margin : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200)
    (headDrifts : ∀ w ∈ J, ∀ n head headState epoch,
      ((e.world n).state w).getPulledUpHeadState config head = .ok headState →
      ((e.world n).state w).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ v ∈ J, ∀ k (state : BeaconState preset fork),
        ((e.world k).state v).Counts config state →
        epoch.toNat ≤ (getCurrentEpoch state).toNat →
        (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 →
        DriftAtMost headState state margin)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
      ((e.world n).view u) ((e.world n).state u))
    (lower : ∀ n ∈ events, ((e.world n).state u).ParentsBelow)
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {last : FastConfirmationStore}
    (ran : (events.map fun n => (e.world n).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) =
        .ok last)
    {limit : ℕ}
    (bounds : RuleBounds e u events (getFastConfirmationStore anchor) margin limit)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastCall : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (nonempty : following.toNat ≤ limit) :
    ∀ time, following.toNat ≤ time → time ≤ limit → SafeAt e time last.confirmedRoot := by
  sorry

end Models.Network

end EthLib.Consensus
