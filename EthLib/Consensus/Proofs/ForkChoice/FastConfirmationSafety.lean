module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationTransport

/-!
# Statements: the block that the fast confirmation rule stores is safe from the next slot

This file states step 8 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr], and the result is its Theorem 1.

Some proofs are placeholders, and each statement is proposed for review.

An honest validator calls the rule at the start of each slot of a run of slots.

The block that the last call stores is then on the chain of the head of each honest store.

That holds from the start of the next slot to a last time.

The first statement reads the checks of step 6 and the walk of the rule off one call.

The walk statement keeps a confirmed block safe, by an induction on the time.

Before the end of the first complete epoch after the call, it uses the transport of step 5.

That transport compares the balances of the caller with those of each receiver.

From the end of that epoch on, it uses the honest duties of a complete epoch instead.

Those are weighed in the justified state of each receiver, with no comparison of balances.

The theorem is an induction on the calls, through `CallInvariant`.

The invariant keeps three facts on the block that a call stores.

The block is safe from the start of the next slot.

A recent block has a recent ancestor that is safe from the start of the current epoch.

That ancestor is the historical anchor that the transport of step 5 needs.

A block of the current epoch extends an origin whose target the rule has checked.

Each start of a call holds the facts that the walk needs.

The block stored before holds them by the induction.

Step 7 gives them for the finalized block and for the observed justified block.

The theorem takes Assumption 2 of the paper at each call, as `RuleBounds` holds it.

It takes the facts of Casper FFG as hypotheses, with a horizon.

It derives the honest vote of a justified checkpoint and the honest third from Assumption 2.

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

/-- The checkpoint update records the epoch boundary tests of the same slot. -/
private theorem updateFastConfirmationVariables_checkpoints
    {fcr after : FastConfirmationStore} {head : Root}
    (updated : store.updateFastConfirmationVariables config fcr head = .ok after) :
    ∃ slot, store.getCurrentSlot config = .ok slot ∧
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
        after.currentEpochObservedJustifiedCheckpoint =
          fcr.currentEpochObservedJustifiedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.previousEpochObservedJustifiedCheckpoint) := by
  unfold updateFastConfirmationVariables at updated
  simp only [bind_ok_iff] at updated
  obtain ⟨slot, slotOk, next, nextOk, nextStart, nextStartOk, updated⟩ := updated
  have nextOk := mapError_ok_iff.mp nextOk
  refine ⟨slot, slotOk, ?_⟩
  split at updated <;> simp only [bind_ok_iff] at updated <;>
    obtain ⟨atStart, atStartOk, updated⟩ := updated <;> split at updated <;>
    simp only [pure, Except.pure, Except.ok.injEq] at updated <;> subst updated <;>
    simp_all

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
  unfold onFastConfirmation at confirmed
  simp only [bind_ok_iff] at confirmed
  obtain ⟨head, headOk, updated, updateOk, root, latest, confirmed⟩ := confirmed
  simp only [pure, Except.pure, Except.ok.injEq] at confirmed
  subst confirmed
  obtain ⟨slot, start, slotOk, startCase, result⟩ :=
    getLatestConfirmed_checked_start lower latest
  obtain ⟨previousHead, currentHead⟩ :=
    Prod.mk.inj (updateFastConfirmationVariables_heads updateOk)
  obtain ⟨updateSlot, updateSlotOk, checkpoints⟩ :=
    updateFastConfirmationVariables_checkpoints updateOk
  have sameSlot : updateSlot = slot := Except.ok.inj (updateSlotOk.symm.trans slotOk)
  subst updateSlot
  rw [updateFastConfirmationVariables_confirmedRoot updateOk] at startCase
  refine ⟨head, slot, start, headOk, slotOk, previousHead, currentHead,
    checkpoints.1, checkpoints.2.1, checkpoints.2.2.1, checkpoints.2.2.2, startCase, ?_⟩
  rcases result with same | ⟨checked, descendant⟩
  · exact Or.inl same
  · rcases findLatestConfirmedDescendant_eq_or descendant with same | walk
    · exact Or.inl same
    · exact Or.inr ⟨checked, walk⟩

variable (lower : store.ParentsBelow) in
/-- Before Gloas, each node of a filtered tree has a viable leaf of the tree below it.

The leaf passes `isViableLeaf`, so its chain holds the finalized block of the store. -/
theorem exists_viableLeaf_of_mem_filterNodeTree (before : fork < .glamsterdam) :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes →
      ∀ n ∈ nodes, ∃ leaf ∈ nodes, store.isViableLeaf config leaf = .ok true ∧
        (blockTree lower).Ancestor (some n.root) (some leaf.root) := by
  intro node
  induction hrank : store.nodeRank node using Nat.strong_induction_on generalizing node with
  | _ rank ih =>
  intro nodes walk n mem
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind_ok_iff] at walk
    obtain ⟨isViable, viable, walk⟩ := walk
    simp only [pure, Except.pure, Except.ok.injEq] at walk
    subst walk
    cases isViable
    · cases mem
    · rw [List.mem_singleton.mp mem]
      exact ⟨node, List.mem_singleton_self _, viable, .refl _⟩
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at walk
  obtain ⟨viable, viableOk, walk⟩ := walk
  simp only [pure, Except.pure, Except.ok.injEq] at walk
  subst walk
  have nonempty : viable ≠ [] := fun nil => by simp [nil] at mem
  have nodesEq : (if viable.isEmpty then [] else viable ++ [node]) = viable ++ [node] := by
    simp [List.isEmpty_iff, nonempty]
  rw [nodesEq] at mem ⊢
  -- Each node below a child of the start is a viable node of the start.
  have below : ∀ x ∈ viable, ∃ child ∈ children, ∃ nodesBelow,
      store.nodeRank child < store.nodeRank node ∧
      store.filterNodeTree config child = .ok nodesBelow ∧ x ∈ nodesBelow ∧
      ∀ y ∈ nodesBelow, y ∈ viable := by
    intro x hx
    obtain ⟨child, childMem, nodesBelow, belowOk, xMem⟩ := (mem_of_flatMapM_ok viableOk x).mp hx
    split at belowOk
    · rename_i lowerRank
      refine ⟨child, childMem, nodesBelow, lowerRank, belowOk, xMem, fun y hy => ?_⟩
      exact (mem_of_flatMapM_ok viableOk y).mpr ⟨child, childMem, nodesBelow, by
        simp [lowerRank, belowOk], hy⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  rcases List.mem_append.mp mem with mem | same
  · obtain ⟨child, -, nodesBelow, lowerRank, belowOk, nMem, lift⟩ := below n mem
    obtain ⟨leaf, leafIn, viable', above⟩ := ih _ (hrank ▸ lowerRank) rfl belowOk n nMem
    exact ⟨leaf, List.mem_append_left _ (lift leaf leafIn), viable', above⟩
  · -- The start has a viable child, and a viable leaf lies below that child.
    rw [List.mem_singleton.mp same]
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨child, childMem, nodesBelow, lowerRank, belowOk, xMem, lift⟩ := below x hx
    have childIn := filterNodeTree_self belowOk (List.ne_nil_of_mem xMem)
    obtain ⟨leaf, leafIn, viable', above⟩ :=
      ih _ (hrank ▸ lowerRank) rfl belowOk child childIn
    obtain ⟨-, block, found, parentRoot⟩ := (mem_getNodeChildren before childrenOk).mp childMem
    have isChild : (blockTree lower).IsChild (some child.root) (some node.root) :=
      blockTree_isChild_iff.mpr ⟨block, found, parentRoot⟩
    exact ⟨leaf, List.mem_append_left _ (lift leaf leafIn), viable', isChild.ancestor.trans above⟩

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- A complete epoch lies in a range of times, and each of its reads succeeds.

It starts at the first time or later, and it ends at the last time or before.

Its end is the start of the epoch after it, so every duty of the epoch has its slot by then.

Near the end of `UInt64` time, such an epoch may not exist.

Then the whole range belongs to the initial phase. -/
def CompleteEpochWithin (preset : Preset) (config : Config) (genesisTimeMs : UInt64)
    (first last : ℕ) : Prop :=
  ∃ (epoch : Epoch) (begin next : Slot) (beginTime endTime : UInt64),
    computeStartSlotAtEpoch preset epoch = .ok begin ∧
    addChecked begin preset.SLOTS_PER_EPOCH = .ok next ∧
    computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime ∧
    computeTimeAtSlotMs config genesisTimeMs next = .ok endTime ∧
    first ≤ beginTime.toNat ∧ endTime.toNat ≤ last

open Classical in
/-- The late majority of a receiver: a complete epoch of honest duties outweighs what is missing.

This is a generalized missing-duty assumption, not Assumption 2 of the paper as stated there.

The paper fixes the validator set; here the receiver weighs with its own justified state.

That state may be old, so honest validators of its tally may have no duty in a recent epoch.

The epoch starts at a first time or later, and ends at a given time or before.

The tally is the set of validators that are active and not slashed in that state.

The Byzantine validators hold at most β of the whole tally.

The missing stake is that of honest validators of the tally without a duty in the epoch.

Twice the missing stake, plus the boost, fits in the margin that β leaves.

`ByzantineStakeAtMost.majority_of_missing_weight` turns this into a majority of the head.

It does not follow from `WeightBounds`, which compares the balances of two states. -/
def LateMargin (config : Config) (genesisTimeMs : UInt64) (assignment : Assignment preset)
    (J : Set ValidatorIndex) [DecidablePred (· ∈ J)] (first time : ℕ)
    (state : BeaconState preset fork) (boost : ℕ) : Prop :=
  ∃ (epoch : Epoch) (begin next : Slot) (beginTime endTime : UInt64),
    computeStartSlotAtEpoch preset epoch = .ok begin ∧
    addChecked begin preset.SLOTS_PER_EPOCH = .ok next ∧
    computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime ∧
    computeTimeAtSlotMs config genesisTimeMs next = .ok endTime ∧
    first ≤ beginTime.toNat ∧ endTime.toNat ≤ time ∧
    ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      ((unslashedActiveBalances state).map (·.1)).toFinset J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 ∧
    100 * (2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧
          ¬∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
            assignment.committee v slot = some committeeIndex} + boost) <
      (100 - 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) *
        stake (fun v => balanceAt state v.toNat)
          ((unslashedActiveBalances state).map (·.1)).toFinset

/-- The call of index `i` of a run is at the event `n`, from the store `fcr` to the store `after`.

The run makes one call at each event of a list, from a first store of the rule. -/
def CallAt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (u : ValidatorIndex) (events : List ℕ) (first : FastConfirmationStore)
    (i n : ℕ) (fcr after : FastConfirmationStore) : Prop :=
  events[i]? = some n ∧
    ((events.take i).map fun k => (e.world k).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) first = .ok fcr ∧
    ((e.world n).state u).onFastConfirmation config fcr = .ok after

/-- Assumption 2 of the paper at the calls of the rule that one validator makes.

Each call weighs with the state of its observed justified checkpoint, the source of balances.

While no complete epoch lies between the call and a time, `WeightBounds` bounds the shift.

That shift compares the balances of the source with those of each receiver.

The measured tally of each one-confirmed block exceeds the threshold of the rule by the shift.

In the pulled-up state of the head of a call, take the committees of the epoch so far.

The Byzantine validators hold at most β of their stake.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

No honest validator is a known equivocator of the store of a call.

Once a complete epoch lies between the call and a time, each receiver has `LateMargin`.

That second field is a separate assumption on the duties of an epoch, not a consequence of the
first.

The fields name stores of the execution alone, so an execution can hold them. -/
structure RuleBounds
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) [DecidablePred (· ∈ J)] (u : ValidatorIndex) (events : List ℕ)
    (first : FastConfirmationStore) (margin shift limit : ℕ) : Prop where
  /-- Before a complete epoch, the honest stores weigh near the source of balances. -/
  weights : ∀ i n fcr after balanceSource last,
    CallAt e u events first i n fcr after →
    ((e.world n).state u).checkpointState after.currentEpochObservedJustifiedCheckpoint =
      .ok balanceSource →
    ¬CompleteEpochWithin preset config genesisTimeMs (e.world n).time last →
    WeightBounds e balanceSource (e.world n).time last shift
  /-- The measured tally exceeds the rule's conservative threshold by the weight shift.

  This is an observable margin, not an assumption about the unknown honest supporters. -/
  slack : ∀ i n fcr after balanceSource head root block parent firstSlot lastSlot beforeBlock
    slot participants maximum score support discount adversary,
    CallAt e u events first i n fcr after →
    ((e.world n).state u).checkpointState after.currentEpochObservedJustifiedCheckpoint =
      .ok balanceSource →
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    ((e.world n).state u).block root = .ok block →
    ((e.world n).state u).block block.parentRoot = .ok parent →
    addChecked parent.slot 1 = .ok firstSlot → subChecked slot 1 = .ok lastSlot →
    subChecked block.slot 1 = .ok beforeBlock →
    ((e.world n).state u).getCommitteesBetweenSlots head.root firstSlot beforeBlock =
      .ok participants →
    ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root balanceSource firstSlot
      lastSlot = .ok maximum → computeProposerScore config balanceSource = .ok score →
    ((e.world n).state u).isOneConfirmed config head.root balanceSource
      (((e.world n).state u).tallyVotes balanceSource) root = .ok true →
    ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes balanceSource)
      ⟨root, .pending⟩ = .ok support →
    ((e.world n).state u).computeEmptySlotSupportDiscount config head.root balanceSource root =
      .ok discount →
    ((e.world n).state u).getAdversarialWeight config head.root balanceSource root =
      .ok adversary →
    maximum.toNat + score.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat
  /-- The Byzantine validators hold at most β of the committees of the epoch so far. -/
  byzantine : ∀ i n fcr after head state slot epochStart lastSlot participants,
    CallAt e u events first i n fcr after →
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
  remaining : ∀ i n fcr after head state slot epochStart lastSlot participants total soFar,
    CallAt e u events first i n fcr after →
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
  dishonest : ∀ i n fcr after, CallAt e u events first i n fcr after →
    ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J
  /-- After a complete epoch, each receiver has the late majority. -/
  late : ∀ i n fcr after, CallAt e u events first i n fcr after →
    ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      CompleteEpochWithin preset config genesisTimeMs (e.world n).time (e.world k).time →
      (e.world k).time ≤ limit →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
        .ok state →
      LateMargin config genesisTimeMs assignment J (e.world n).time (e.world k).time state
        (((e.world k).state w).boostScore config)

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- An ancestor test of an honest store still holds at a later event of the same validator. -/
theorem Execution.isAncestor_of_le {u : ValidatorIndex} {n k : ℕ} (later : n ≤ k)
    {node ancestor : ForkChoiceNode}
    (descends : ((e.world n).state u).isAncestor node ancestor = .ok true) :
    ((e.world k).state u).isAncestor node ancestor = .ok true := by
  have blocks {root : Root} {block : BeaconBlock preset fork}
      (found : ((e.world n).state u).blocks[root]? = some block) :
      ((e.world k).state u).blocks[root]? = some block :=
    e.blocks_of_le later found
  unfold Store.isAncestor at descends ⊢
  simp only [bind_ok_iff] at descends
  obtain ⟨block, found, reached, walk, rest⟩ := descends
  have held := blocks (Store.block_ok_iff.mp found)
  simp only [Store.block_ok_iff.mpr held, Store.getAncestor_of_blocks blocks walk, bind,
    Except.bind]
  exact rest

/-- The epoch of a block that an honest store holds is the same at a later event. -/
theorem Execution.getBlockEpoch_of_le {u : ValidatorIndex} {n k : ℕ} (later : n ≤ k)
    {root : Root} {epoch : Epoch}
    (read : ((e.world n).state u).getBlockEpoch root = .ok epoch) :
    ((e.world k).state u).getBlockEpoch root = .ok epoch := by
  unfold Store.getBlockEpoch at read ⊢
  simp only [bind_ok_iff] at read
  obtain ⟨block, found, rest⟩ := read
  rw [Store.block_ok_iff.mpr (e.blocks_of_le later (Store.block_ok_iff.mp found))]
  exact rest

/-- At the start of an epoch, no block of that epoch has the margin of a confirmed block.

Such a block is of the current slot, since no store holds a block of a later slot.

A vote counts only from a slot after its block and before the current slot.

So no recorded vote supports the block, and its support is zero.

The discount is at most the weight of the committees, so the margin fails.

The walk uses this for the premise `atStart` of `Execution.coveredOrViableAt_of_checked`. -/
theorem Execution.rootEpoch_ne_of_slack_at_epoch_start {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    {head root : Root} {balanceSource : BeaconState preset fork}
    {slot firstSlot lastSlot : Slot} {epoch rootEpoch : Epoch}
    {block parent : BeaconBlock preset fork} {maximum score support discount adversary : Gwei}
    {shift : ℕ}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (isStart : isStartSlotAtEpoch preset slot = .ok true)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (rootEpochOk : ((e.world n).state u).getBlockEpoch root = .ok rootEpoch)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok firstSlot)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximum)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes balanceSource) ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head
      balanceSource root = .ok discount)
    (slack : maximum.toNat + score.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat) :
    rootEpoch ≠ epoch := by
  sorry

/-- The finalized-chain premise of a receiver, from the coverage of a block.

At an event `k`, the receiver holds the block in its filtered tree or below its justified block.

In the second case the head of the receiver descends from the block anyway.

In the first case, take the finalized checkpoint of the receiver at any event `k'` up to `k`.

Its boundary is at or before the block, and it is the checkpoint block of the block there.

This is the premise `rootFinal` of the transport and of the late duty.

The finalized chain places the finalized checkpoints at `k'` and at `k` below the justified block.

Then two cases follow.

The boundary at `k'` is at or before the justified block: the block descends from that block.

The boundary is after the justified block: the finalized block is the justified block itself.

The finalized checkpoint at `k` then has the same block and a boundary still later.

A viable leaf below the block agrees with it, so no block of its chain lies between them.

So the block is after that later boundary, and its checkpoint block is the justified block.

A block below the boundary of a later finality is not in the filtered tree, unless it is the
justified block, which the second case covers. -/
theorem Execution.rootFinal_or_justified_covers {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon)
    (lower : ((e.world k).state w).ParentsBelow)
    {root : Root} {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    {nodes : List ForkChoiceNode}
    (treeOk : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (covered : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ∀ k' ≤ k, ∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ rootBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root := by
  rcases covered with covers | inTree
  · exact .inl covers
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w receiver
  have forward := e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) k w receiver
  -- Split a checkpoint read into its boundary and its walk.
  have split {r c : Root} {ep : Epoch}
      (read : ((e.world k).state w).getCheckpointBlock r ep = .ok c) :
      ∃ boundary anc, computeStartSlotAtEpoch preset ep = .ok boundary ∧
        ((e.world k).state w).getAncestor ⟨r, .pending⟩ boundary = .ok anc ∧ anc.root = c := by
    unfold Store.getCheckpointBlock at read
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
    obtain ⟨boundary, boundaryOk, anc, walk, eq⟩ := read
    exact ⟨boundary, anc, mapError_ok_iff.mp boundaryOk, walk, eq⟩
  -- A walk from a held block to the slot of a held block that it descends from.
  have walkTo {tip node : Root} {tipBlock nodeBlock : BeaconBlock preset fork}
      (tipFound : ((e.world k).state w).blocks[tip]? = some tipBlock)
      (nodeFound : ((e.world k).state w).blocks[node]? = some nodeBlock)
      (above : (Store.blockTree lower).Ancestor (some node) (some tip)) :
      ((e.world k).state w).getAncestor ⟨tip, .pending⟩ nodeBlock.slot = .ok ⟨node, .pending⟩ := by
    obtain ⟨anc, walk⟩ := Store.getAncestor_ok_of_orphans_le lower (slot := nodeBlock.slot)
      (node := ⟨tip, .pending⟩)
      (fun r b found orphan => reached.orphans_le (UInt64.le_of_eq anchorSlot) found orphan
        nodeFound) tipFound
    have ancRoot := Store.getAncestor_root_eq (lower := lower) (node := ⟨node, .pending⟩)
      nodeFound walk above
    have ancPending := Store.getAncestor_pending_of_lt preGloas rfl walk
    obtain ⟨r, s⟩ := anc
    simp only at ancRoot ancPending
    subst ancRoot ancPending
    exact walk
  -- The justified block is held, and the block descends from it.
  set justified := ((e.world k).state w).justifiedCheckpoint
  have treeWalk : ((e.world k).state w).filterNodeTree config ⟨justified.root, .pending⟩ =
      .ok nodes := treeOk
  obtain ⟨justifiedIn, -, -⟩ := Store.filterNodeTree_mem treeWalk _ inTree
  obtain ⟨-, ⟨justifiedBlock, justifiedFound⟩, -⟩ :=
    Store.filterNodeTree_mem treeWalk _ justifiedIn
  have below := (Store.filterNodeTree_ancestor (lower := lower) preGloas treeWalk _ inTree).1
  by_cases same : root = justified.root
  · left
    subst same
    exact Store.isAncestor_self (node := ⟨justified.root, .pending⟩) known
  right
  have rootWalk := walkTo known justifiedFound below
  have descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨justified.root, .pending⟩ = .ok true := by
    simp [Store.isAncestor, Store.block_ok_iff.mpr justifiedFound, rootWalk, later, bind,
      Except.bind, pure, Except.pure]
  obtain ⟨rootBlock', rootFound', justifiedLe⟩ :=
    Store.slot_le_of_isAncestor justifiedFound descends
  rw [known, Option.some.injEq] at rootFound'
  subst rootBlock'
  -- Every justified checkpoint of the receiver is within the horizon.
  have justifiedHorizon : justified.epoch ≤ horizon :=
    UInt64.le_trans (forward.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot)
      epochOk).1 inHorizon
  have endpointLe := reached.finalized_le_justified sound
  intro k' earlier
  have finalLe := (e.epochsLe_of_le w earlier).2
  -- The finalized chain places both finalized checkpoints below the justified block.
  have read := chain w receiver w receiver k' k justified (Or.inl rfl)
    (UInt64.le_trans finalLe endpointLe) justifiedHorizon
  obtain ⟨boundary, anc, boundaryOk, walk, ancRoot⟩ := split read
  refine ⟨boundary, boundaryOk, ?_⟩
  by_cases early : boundary ≤ justifiedBlock.slot
  · exact ⟨UInt64.le_trans early justifiedLe,
      Store.getCheckpointBlock_of_isAncestor preGloas justifiedFound descends boundaryOk early read⟩
  -- The boundary is after the justified block, so the finalized block is the justified block.
  have late : justifiedBlock.slot ≤ boundary := UInt64.le_of_lt (UInt64.not_le.mp early)
  rw [Store.getAncestor_of_le justifiedFound late, Except.ok.injEq] at walk
  subst walk
  have finalRoot : ((e.world k').state w).finalizedCheckpoint.root = justified.root := ancRoot.symm
  have readNow := chain w receiver w receiver k k justified (Or.inl rfl) endpointLe
    justifiedHorizon
  obtain ⟨boundaryNow, ancNow, boundaryNowOk, walkNow, ancNowRoot⟩ := split readNow
  have boundaryLe : boundary ≤ boundaryNow := by
    have h1 := computeStartSlotAtEpoch_ok_iff.mp boundaryOk
    have h2 := computeStartSlotAtEpoch_ok_iff.mp boundaryNowOk
    have h3 := UInt64.le_iff_toNat_le.mp finalLe
    apply UInt64.le_iff_toNat_le.mpr
    rw [h1.2, h2.2]
    exact Nat.mul_le_mul_right _ h3
  have lateNow : justifiedBlock.slot ≤ boundaryNow := UInt64.le_trans late boundaryLe
  rw [Store.getAncestor_of_le justifiedFound lateNow, Except.ok.injEq] at walkNow
  subst walkNow
  -- The current finality is not at genesis, since its boundary is after a held block.
  have notGenesis : ((e.world k).state w).finalizedCheckpoint.epoch ≠ GENESIS_EPOCH := by
    intro genesis
    have h := (computeStartSlotAtEpoch_ok_iff.mp boundaryNowOk).2
    rw [genesis] at h
    have zero : boundaryNow.toNat = 0 := by simpa [GENESIS_EPOCH] using h
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp early)
    have := UInt64.le_iff_toNat_le.mp boundaryLe
    omega
  -- A viable leaf below the block reads the justified block at the current boundary.
  obtain ⟨leaf, leafIn, viable, leafAbove⟩ :=
    Store.exists_viableLeaf_of_mem_filterNodeTree lower preGloas treeWalk _ inTree
  obtain ⟨-, ⟨leafBlock, leafFound⟩, -⟩ := Store.filterNodeTree_mem treeWalk _ leafIn
  have leafRead := (Store.isViableLeaf_finalized viable).resolve_left notGenesis
  obtain ⟨boundaryLeaf, ancLeaf, boundaryLeafOk, leafWalk, ancLeafRoot⟩ := split leafRead
  rw [boundaryNowOk, Except.ok.injEq] at boundaryLeafOk
  subst boundaryLeafOk
  have ancLeafPending := Store.getAncestor_pending_of_lt preGloas rfl leafWalk
  have ancLeafEq : ancLeaf = ⟨justified.root, .pending⟩ := by
    obtain ⟨r, s⟩ := ancLeaf
    have nowRoot : ((e.world k).state w).finalizedCheckpoint.root = justified.root :=
      ancNowRoot.symm
    simp only at ancLeafRoot ancLeafPending
    rw [ancLeafPending, ancLeafRoot, nowRoot]
  rw [ancLeafEq] at leafWalk
  have leafToRoot := walkTo leafFound known leafAbove
  -- The block is after the current boundary, or it would be the justified block.
  have rootLate : boundaryNow < rootBlock.slot := by
    by_contra notLate
    have le := UInt64.not_lt.mp notLate
    have through := Store.getAncestor_trans le leafWalk
    rw [leafToRoot, Store.getAncestor_of_le justifiedFound justifiedLe, Except.ok.injEq] at through
    exact same (congrArg ForkChoiceNode.root through)
  refine ⟨UInt64.le_trans boundaryLe (UInt64.le_of_lt rootLate), ?_⟩
  -- Both walks from the leaf reach the justified block at the earlier boundary.
  have viaRoot := Store.getAncestor_trans
    (UInt64.le_trans boundaryLe (UInt64.le_of_lt rootLate)) leafToRoot
  have viaJustified := Store.getAncestor_trans boundaryLe leafWalk
  rw [Store.getAncestor_of_le justifiedFound late] at viaJustified
  rw [viaJustified] at viaRoot
  simp [Store.getCheckpointBlock, boundaryOk, ← viaRoot, finalRoot, Except.mapError, bind,
    Except.bind, pure, Except.pure]

variable [DecidablePred (· ∈ J)]

/-- Step 8, the walk: a block that the rule confirms after a safe start is safe up to a last time.

The caller is an honest validator whose store is up to date at the start of a slot.

Its rule passed the checks of step 6 from a start to the block, along a confirmed walk.

The block is a root of the walk from the start to the head of the caller.

That block and each root before it in the walk are one-confirmed.

The start is safe from the call to the last time.

A historical anchor below the start is safe from the start of the current epoch to the call.

The facts that step 6 reads off earlier calls are given as in `coveredOrViableAt_of_checked`.

While no complete epoch lies between the call and a time, `WeightBounds` bounds the shift.

Once one does, each receiver has the late majority of `LateMargin`.

No honest store holds a block at the parent root of the anchor block.

So each honest store has its parents below its blocks, which the filtered tree and the head need.

The proof is a strong induction on the time, and at each time an induction along the walk.

At each time, step 6 gives the block in the filtered tree, or below the justified block.

The finalized-chain premise of each receiver follows by `Execution.rootFinal_or_justified_covers`.

Before the end of the first complete epoch, `Execution.honest_support_of_historical_anchor` and
`HeadFollowsSupport` keep the block on the chain of the head.

After it, `Execution.mem_supportersOf_of_duty_epoch` and
`Store.isAncestor_getHead_of_missing_weight` do.

A theorem of [verified-fast-confirmation][vfc] gives the same result.

It is `safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_of_walk {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ)
    (oneBlock : OneBlockPerRoot e)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) (follows : HeadFollowsSupport e)
    {horizon anchorEpoch : Epoch} {margin : ℕ}
    (chain : FinalizedPrefix e horizon)
    (unique : OneJustifiedPerEpoch e horizon) (pins : HonestThirdPins e anchorEpoch horizon margin)
    (voted : JustifiedByHonestVote e anchorEpoch horizon) (included : TargetIncluded e)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (noVotes : anchor.latestMessages.isEmpty)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (lower : ((e.world n).state u).ParentsBelow)
    {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {balanceSource : BeaconState preset fork} {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (sourceOk : ((e.world n).state u).checkpointState fcr.currentEpochObservedJustifiedCheckpoint =
      .ok balanceSource)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ root :: later))
    (allConfirmed : ∀ member ∈ chain ++ [root], ((e.world n).state u).isOneConfirmed config
      head.root balanceSource (((e.world n).state u).tallyVotes balanceSource) member = .ok true)
    (previousHead : fcr.previousSlotHead = anchor.finalizedCheckpoint.root ∨
      ∃ k < n, ∃ previous previousSlot,
        UpToDate config checks sources (e.world k).time ((e.world k).view u)
          ((e.world k).state u) ∧
        ((e.world k).state u).getHead config = .ok previous ∧
        previous.root = fcr.previousSlotHead ∧
        ((e.world k).state u).getCurrentSlot config = .ok previousSlot ∧
        addChecked previousSlot 1 = .ok slot)
    (targetVotes : HonestTargetVotes e margin u n head.root)
    (lineage : ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getBlockEpoch start = .ok epoch →
      TargetChecked e margin anchor.finalizedCheckpoint.root u n epoch start)
    (previousLineage : ∀ epoch previous,
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      isStartSlotAtEpoch preset slot = .ok true → addChecked previous 1 = .ok epoch →
      ((e.world n).state u).getBlockEpoch start = .ok previous →
      TargetChecked e margin anchor.finalizedCheckpoint.root u n previous start ∨
        (((e.world n).state u).unrealizedJustification head.root =
          .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
          start = fcr.currentEpochObservedJustifiedCheckpoint.root))
    {historical : Root} {epoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (startBelow : ((e.world n).state u).isAncestor ⟨start, .pending⟩ ⟨historical, .pending⟩ =
      .ok true)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (recent : epoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset epoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historicalSafe : ∀ earlier, epochStartTime.toNat ≤ earlier → earlier < (e.world n).time →
      SafeAt e earlier historical)
    {limit : ℕ}
    (startSafe : ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time start)
    {shift : ℕ}
    (weights : ∀ last, ¬CompleteEpochWithin preset config genesisTimeMs (e.world n).time last →
      WeightBounds e balanceSource (e.world n).time last shift)
    (slack : ∀ member ∈ chain ++ [root], ∀ block parent firstSlot lastSlot beforeBlock
      participants maximum score support discount adversary,
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
    (late : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      CompleteEpochWithin preset config genesisTimeMs (e.world n).time (e.world k).time →
      (e.world k).time ≤ limit →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
        .ok state →
      LateMargin config genesisTimeMs assignment J (e.world n).time (e.world k).time state
        (((e.world k).state w).boostScore config))
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (few : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon → getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} <
        2 * total.toNat) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root := by
  sorry

/-- What the induction of Theorem 1 keeps on the block that a call at the event `n` stores.

The block is safe from the start of the slot after the call to the last time.

A block of the current epoch or the one before has a historical anchor.

That anchor is on its chain, of the current epoch or the one before.

It is safe from the start of the current epoch to the last time.

A block of the current epoch extends an origin whose target the rule checked, as in
`TargetChecked`.

The origin is safe from that check to the last time, not only to the call.

In [verified-fast-confirmation][vfc] the first and third facts are
`ConfirmedSafeFromFollowingSlot` and `AcceptedHistoricalA32CurrentLineageAt`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def CallInvariant
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (margin limit : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (root : Root) : Prop :=
  (∀ slot next following, ((e.world n).state u).getCurrentSlot config = .ok slot →
    addChecked slot 1 = .ok next →
    computeTimeAtSlotMs config genesisTimeMs next = .ok following →
    ∀ time, following.toNat ≤ time → time ≤ limit → SafeAt e time root) ∧
  (∀ epoch rootEpoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
    epoch.toNat ≤ rootEpoch.toNat + 1 →
    ∃ (historical : Root) (historicalEpoch : Epoch) (epochStart : Slot) (epochStartTime : UInt64),
      ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨historical, .pending⟩ = .ok true ∧
      ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch ∧
      epoch.toNat ≤ historicalEpoch.toNat + 1 ∧
      computeStartSlotAtEpoch preset epoch = .ok epochStart ∧
      computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime ∧
      ∀ time, epochStartTime.toNat ≤ time → time ≤ limit → SafeAt e time historical) ∧
  (∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok epoch →
    ∃ k ≤ n, ∃ origin,
      ((e.world n).state u).getBlockEpoch origin = .ok epoch ∧
      ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
      (origin = anchorRoot ∨ ∃ head,
        UpToDate config checks sources (e.world k).time ((e.world k).view u)
          ((e.world k).state u) ∧
        ((e.world k).state u).getCurrentStoreEpoch config = .ok epoch ∧
        ((e.world k).state u).getHead config = .ok head ∧
        ((e.world k).state u).willCurrentTargetBeJustified config head.root = .ok true ∧
        ((e.world k).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
        HonestTargetVotes e margin u k head.root) ∧
      ∀ time, (e.world k).time ≤ time → time ≤ limit → SafeAt e time origin)

/-- Step 8, one call: the block that a call stores keeps `CallInvariant`.

Each earlier call of the run keeps it, which is the induction hypothesis.

The proof splits the call with `Store.onFastConfirmation_checked`.

A start that the call carries is the block stored before, at the slot before.

Its safety from this call on and its historical anchor come from the call before.

At the start of an epoch, the start itself is the historical anchor.

A finalized start with a confirmed walk is the block of the anchor, by
`Execution.finalizedCheckpoint_eq_of_checked`.

A finalized start without a walk is safe one delay after the call, by `Execution.safeAt_finalized`.

It is the block of the anchor or is two epochs old, by
`Execution.finalizedCheckpoint_eq_or_blockEpoch_add_two_le`, so it needs no historical anchor.

An observed start is safe from the call, by `Execution.safeAt_observed`.

The call before recorded it one slot before, and the first call reads the block of the anchor.

A walk gives a block safe from the call, by `Execution.safeAt_of_walk`.

Its inputs come from the induction hypothesis, from `RuleBounds` and from
`Execution.honestTargetVotes_of_byzantineStakeAtMost`, `Execution.honestThirdPins` and
`Execution.justifiedByHonestVote`.

A walked block of the current epoch from a start of the epoch before has its own target check.

In [verified-fast-confirmation][vfc] this is the successor case of
`confirmed_safety_and_lineage_of_acceptedActualFCRFold`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.callInvariant_step {Δ : ℕ} (sync : e.Synchronous Δ)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) (follows : HeadFollowsSupport e)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ)
    (included : TargetIncluded e)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
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
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (nonzero : ∀ w ∈ J, ∀ k (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
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
    {shift limit : ℕ}
    (bounds : RuleBounds e u events (getFastConfirmationStore anchor) margin shift limit)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt e u events (getFastConfirmationStore anchor) i n fcr after)
    (earlier : ∀ i' < i, ∀ n' fcr' after',
      CallAt e u events (getFastConfirmationStore anchor) i' n' fcr' after' →
      CallInvariant e margin limit anchor.finalizedCheckpoint.root u n' after'.confirmedRoot) :
    CallInvariant e margin limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
  sorry

/-- Theorem 1: the block that the rule stores is safe from the start of the next slot.

An honest validator calls the rule at the events of a list, with its store up to date.

The calls are at the starts of consecutive slots, and the first store of the rule is the anchor's.

Each honest store starts as the store of the anchor, which holds no vote.

The anchor keeps the invariant of the state transition, and its block is at the start of an epoch.

An epoch has more than one slot, and the historical buffer holds two epochs.

The network is synchronous, and the delay fits strictly in a slot.

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

Each block that an honest store holds has a nonzero state root.

No honest store holds a block at the parent root of the anchor block, up to the last time.

So the parents of the blocks of each honest store are at lower slots.

Assumption 2 holds at each call, with that margin and a weight shift, as `RuleBounds` says.

Each honest store up to the last time is in an epoch at most the horizon.

The start of the next slot is at most the last time.

Then the block that the last call stores is safe from the start of the next slot.

It stays safe to the last time.

The proof is a strong induction on the calls, with `Execution.callInvariant_step`.

In [verified-fast-confirmation][vfc], this is `confirmed_root_safe_from_next_slot`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_confirmedRoot {Δ : ℕ} (sync : e.Synchronous Δ)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e) (follows : HeadFollowsSupport e)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ)
    (included : TargetIncluded e)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
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
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (nonzero : ∀ w ∈ J, ∀ k (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
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
    {shift limit : ℕ}
    (bounds : RuleBounds e u events (getFastConfirmationStore anchor) margin shift limit)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastCall : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (nonempty : following.toNat ≤ limit) :
    ∀ time, following.toNat ≤ time → time ≤ limit → SafeAt e time last.confirmedRoot := by
  -- The promised interval is not empty, so the theorem says something about the run.
  have _ := nonempty
  -- Every call of the run keeps the invariant, by strong induction on its index.
  have invariant : ∀ i n fcr after,
      CallAt e u events (getFastConfirmationStore anchor) i n fcr after →
      CallInvariant e margin limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro n fcr after calls
      exact e.callInvariant_step sync half slots long window ring votes fits prompt committees
        follows preGloas oneBlock admitted included anchored sound anchorSlot anchorAtBoundary
        start noVotes maxAligned increment chain unique byzantine unslashed positive enough
        large nonzero headDrifts caller upToDate lower atSlots bounds inHorizon anchorParent calls
        fun i' lt n' fcr' after' calls' => ih i' lt n' fcr' after' calls'
  -- The last call of the run stores the block that the run returns.
  obtain ⟨prior, rfl⟩ := List.getLast?_eq_some_iff.mp lastCall
  rw [List.map_append, List.foldlM_append] at ran
  simp only [bind_ok_iff] at ran
  obtain ⟨fcr, before, ran⟩ := ran
  simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_ok_iff] at ran
  obtain ⟨stored, call, done⟩ := ran
  have done : stored = last := Except.ok.inj done
  subst done
  have index : (prior ++ [n])[prior.length]? = some n := by simp
  have taken : (prior ++ [n]).take prior.length = prior := List.take_left' rfl
  have calls : CallAt e u (prior ++ [n]) (getFastConfirmationStore anchor) prior.length n fcr
      stored := ⟨index, by rw [taken]; exact before, call⟩
  exact (invariant _ n fcr stored calls).1 slot next following slotOk nextOk followingOk

end Models.Network

end EthLib.Consensus
