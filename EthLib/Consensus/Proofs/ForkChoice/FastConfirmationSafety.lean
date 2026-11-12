module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationTransport

/-!
# Statements: the block that the fast confirmation rule stores is safe from the next slot

This file states step 8 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The result is the safety part of its Theorem 1, for the specification as EthLib states it.

It is a conditional result.

It rests on placeholders in this file and in the files it imports.

It also rests on the generalized assumptions of `RuleBounds`, which are not the paper's own.

It does not state the monotonicity part of Theorem 1.

An honest validator calls the rule at the start of each slot of a run of slots.

The block that the last call stores is then on the chain of the head of each honest store.

That holds from the start of the next slot to a last time.

The first statement reads the checks of step 6 and the walk of the rule off one call.

The walk statement keeps a confirmed block safe, by an induction on the time.

Before a complete epoch lies between the call and a time, it uses the transport of step 5.

That transport compares the balances of the caller with those of each receiver.

After one does, it uses the honest duties of a complete epoch instead.

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

The theorem takes the bounds of `RuleBounds` at each call that confirms by a walk.

They generalize Assumption 2 of the paper to balances that change; they are not that assumption.

It takes the facts of Casper FFG as hypotheses, with a horizon.

It derives the honest vote of a justified checkpoint and the honest third from Byzantine bounds.

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

The start is the one that the rule selects, as `getLatestConfirmed_checked_start` gives it.

A later block has passed the checks of step 6 from that start.

It is a root of the walk from the start to the head, so it is not the start.

That block and each root before it in the walk are one-confirmed.

Each known block must sit at a later slot than its known parent.

The checks read the head of the slot before in the store after the call.

The proof joins `getLatestConfirmed_checked_start` and `findLatestConfirmedDescendant_eq_or`.

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
      (∃ base,
        (base = fcr.confirmedRoot ∧
            ((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ =
                .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config after head.root
                  fcr.confirmedRoot = .ok true)) ∨
          base = store.finalizedCheckpoint.root ∧
            ¬((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                 store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                 epoch.toNat ≤ blockEpoch.toNat + 1) ∧
               store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ =
                 .ok true ∧
               (isStartSlotAtEpoch preset slot = .ok true →
                 store.isConfirmedChainSafe config after head.root
                   fcr.confirmedRoot = .ok true))) ∧
        (start = base ∧
            ¬(isStartSlotAtEpoch preset slot = .ok true ∧
               (∃ observedBlock epoch,
                 store.block after.currentEpochObservedJustifiedCheckpoint.root =
                   .ok observedBlock ∧
                 store.getCurrentStoreEpoch config = .ok epoch ∧
                 Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
               store.unrealizedJustification head.root =
                 .ok after.currentEpochObservedJustifiedCheckpoint ∧
               ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                 store.block after.currentEpochObservedJustifiedCheckpoint.root =
                   .ok observedBlock ∧
                 baseBlock.slot < observedBlock.slot) ∨
          start = after.currentEpochObservedJustifiedCheckpoint.root ∧
            (isStartSlotAtEpoch preset slot = .ok true ∧
              (∃ observedBlock epoch,
                store.block after.currentEpochObservedJustifiedCheckpoint.root =
                  .ok observedBlock ∧
                store.getCurrentStoreEpoch config = .ok epoch ∧
                Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
              store.unrealizedJustification head.root =
                .ok after.currentEpochObservedJustifiedCheckpoint ∧
              ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                store.block after.currentEpochObservedJustifiedCheckpoint.root =
                  .ok observedBlock ∧
                baseBlock.slot < observedBlock.slot))) ∧
      (after.confirmedRoot = start ∨
        after.confirmedRoot ≠ start ∧
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
    · -- The walk returns roots strictly above its start, so the result is not the start.
      obtain ⟨balanceSource, chain, later, sourceOk, walked, confirmedAll⟩ := walk
      refine Or.inr ⟨fun same => ?_, checked, balanceSource, chain, later, sourceOk, walked,
        confirmedAll⟩
      obtain ⟨b, t, bOk, tOk, lt⟩ := slot_lt_of_mem_getAncestorRoots walked (by simp)
        (List.mem_append_right _ (List.mem_cons_self ..))
      rw [← same] at tOk
      obtain rfl : b = t := Except.ok.inj (bOk.symm.trans tOk)
      exact UInt64.lt_irrefl _ lt

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

It does not follow from `WeightBounds`, which compares the balances of two states.

Take an assignment that gives each active validator a duty in each epoch, as with a static set.

Then each honest validator of the tally has a duty in the epoch, and the missing stake is zero.

The condition is then the Byzantine bound on the tally and `100 * boost < (100 - 2β) * W`.

Here `W` is the stake of the tally.

That case shows the condition can hold; it does not make the condition the paper's. -/
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

/-- Implementation-level safety assumptions at the calls of the rule that one validator makes.

They generalize Assumption 2 of the paper to balances that change between states.

They are assumptions of the theorem, not the paper's Assumption 2 itself.

The bounds apply only to a call that stores a new block of its own confirmed walk.

The walk starts from the start that the rule selects.

`Store.onFastConfirmation_checked` gives that start.

A call that returns its start unchanged needs none of the bounds.

Each call weighs with the state of its observed justified checkpoint, the source of balances.

While no complete epoch lies between the call and a time, `WeightBounds` bounds the shift.

That shift compares the balances of the source with those of each receiver.

The measured tally of each block of the walk exceeds the threshold of the rule by the shift.

Away from the start of an epoch, take the committees of the epoch so far.

They are read in the pulled-up state of the head of the call.

The Byzantine validators hold at most β of their stake.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

No field says that honest validators are not known equivocators.

`Execution.not_mem_equivocatingIndices` derives that, from the anchor store with no equivocator.

Once a complete epoch lies between the call and a time, a receiver has `LateMargin`.

That holds only where its justified block does not already cover the stored block.

That last field is its own assumption on the duties of an epoch.

It does not follow from the weight bound.

The fields name stores of the execution alone, so an execution can hold them. -/
structure RuleBounds
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) [DecidablePred (· ∈ J)] (u : ValidatorIndex) (events : List ℕ)
    (first : FastConfirmationStore) (margin shift limit : ℕ) : Prop where
  /-- At a call that stores a block of its own walk, five bounds hold, in this order.

  The start is the one that the rule selects, as `Store.onFastConfirmation_checked` gives it.

  The stored block is not that start, so the call confirmed a new block.

  First, before a complete epoch, the honest stores weigh near the source of balances.

  Second, the tally of each block of the walk exceeds the threshold by the weight shift.

  That is an observable margin, not an assumption about the unknown honest supporters.

  Third, away from an epoch start, the Byzantine validators hold at most β of its committees.

  Those are the committees of the epoch so far.

  Fourth, away from an epoch start, the honest validators of the slots to come hold their share.

  They hold it with the margin.

  Fifth, after a complete epoch, a receiver that does not cover the block has the majority. -/
  walked : ∀ i n fcr after head slot start balanceSource chain later,
    CallAt e u events first i n fcr after →
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    (∃ base,
      (base = fcr.confirmedRoot ∧
          ((∃ epoch blockEpoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch ∧
              ((e.world n).state u).getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
              epoch.toNat ≤ blockEpoch.toNat + 1) ∧
            ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ =
              .ok true ∧
            (isStartSlotAtEpoch preset slot = .ok true →
              ((e.world n).state u).isConfirmedChainSafe config after head.root
                fcr.confirmedRoot = .ok true)) ∨
        base = ((e.world n).state u).finalizedCheckpoint.root ∧
          ¬((∃ epoch blockEpoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch ∧
               ((e.world n).state u).getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
               epoch.toNat ≤ blockEpoch.toNat + 1) ∧
             ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ =
               .ok true ∧
             (isStartSlotAtEpoch preset slot = .ok true →
               ((e.world n).state u).isConfirmedChainSafe config after head.root
                 fcr.confirmedRoot = .ok true))) ∧
      (start = base ∧
          ¬(isStartSlotAtEpoch preset slot = .ok true ∧
             (∃ observedBlock epoch,
               ((e.world n).state u).block after.currentEpochObservedJustifiedCheckpoint.root =
                 .ok observedBlock ∧
               ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch ∧
               Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
             ((e.world n).state u).unrealizedJustification head.root =
               .ok after.currentEpochObservedJustifiedCheckpoint ∧
             ∃ baseBlock observedBlock, ((e.world n).state u).block base = .ok baseBlock ∧
               ((e.world n).state u).block after.currentEpochObservedJustifiedCheckpoint.root =
                 .ok observedBlock ∧
               baseBlock.slot < observedBlock.slot) ∨
        start = after.currentEpochObservedJustifiedCheckpoint.root ∧
          (isStartSlotAtEpoch preset slot = .ok true ∧
            (∃ observedBlock epoch,
              ((e.world n).state u).block after.currentEpochObservedJustifiedCheckpoint.root =
                .ok observedBlock ∧
              ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch ∧
              Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
            ((e.world n).state u).unrealizedJustification head.root =
              .ok after.currentEpochObservedJustifiedCheckpoint ∧
            ∃ baseBlock observedBlock, ((e.world n).state u).block base = .ok baseBlock ∧
              ((e.world n).state u).block after.currentEpochObservedJustifiedCheckpoint.root =
                .ok observedBlock ∧
              baseBlock.slot < observedBlock.slot))) →
    after.confirmedRoot ≠ start →
    ((e.world n).state u).Checked config after head.root start after.confirmedRoot →
    ((e.world n).state u).checkpointState after.currentEpochObservedJustifiedCheckpoint =
      .ok balanceSource →
    ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later) →
    (∀ member ∈ chain ++ [after.confirmedRoot], ((e.world n).state u).isOneConfirmed config
      head.root balanceSource (((e.world n).state u).tallyVotes balanceSource) member =
        .ok true) →
    (∀ last, last ≤ limit →
      ¬CompleteEpochWithin preset config genesisTimeMs (e.world n).time last →
      WeightBounds e balanceSource (e.world n).time last shift) ∧
    (∀ member ∈ chain ++ [after.confirmedRoot], ∀ block parent firstSlot lastSlot beforeBlock
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
      ((e.world n).state u).computeEmptySlotSupportDiscount config head.root balanceSource
        member = .ok discount →
      ((e.world n).state u).getAdversarialWeight config head.root balanceSource member =
        .ok adversary →
      maximum.toNat + score.toNat + 2 * adversary.toNat + shift <
        discount.toNat + 2 * support.toNat) ∧
    (∀ state epochStart lastSlot participants,
      isStartSlotAtEpoch preset slot = .ok false →
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
      subChecked slot 1 = .ok lastSlot →
      ((e.world n).state u).getCommitteesBetweenSlots head.root epochStart lastSlot =
        .ok participants →
      ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
        (Store.activeMembers state participants) J
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) ∧
    (∀ state epochStart lastSlot participants total soFar,
      isStartSlotAtEpoch preset slot = .ok false →
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
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
          {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∉ participants ∧ v ∈ J}) ∧
    (∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      CompleteEpochWithin preset config genesisTimeMs (e.world n).time (e.world k).time →
      (e.world k).time ≤ limit →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
        .ok state →
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨after.confirmedRoot, .pending⟩ ≠ .ok true →
      LateMargin config genesisTimeMs assignment J (e.world n).time (e.world k).time state
        (((e.world k).state w).boostScore config))

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
  intro sameEpoch
  have forward := e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored) n u caller
  -- A successful clock read rules out a zero slot duration.
  have positive : 0 < config.SLOT_DURATION_MS := by
    have clock := mapError_ok_iff.mp slotOk
    unfold computeSlotAtTimeMs at clock
    obtain ⟨elapsed, -, divided⟩ := bind_ok_iff.mp clock
    have nonzero := (divChecked_ok_iff.mp divided).1
    exact UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.toNat_inj.not.mpr nonzero
      simp only [UInt64.toNat_zero] at this ⊢
      omega)
  obtain ⟨current, currentOk, blocks, -⟩ :=
    forward.slots_le_current positive (UInt64.le_of_eq anchorSlot)
  rw [slotOk, Except.ok.injEq] at currentOk
  subst current
  have known := Store.block_ok_iff.mp blockOk
  have notFuture := blocks root block known
  have currentEpoch : computeEpochAtSlot preset slot = epoch := by
    simpa only [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] using epochOk
  have blockEpoch : computeEpochAtSlot preset block.slot = epoch := by
    simpa only [Store.getBlockEpoch, blockOk, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, sameEpoch] using rootEpochOk
  -- The boundary slot is its epoch rounded down, so a block of that epoch is not earlier.
  have rounded : slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH = slot := by
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at isStart
    rw [computeStartSlotAtEpoch_computeEpochAtSlot] at isStart
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, decide_eq_true_eq] at isStart
    have zero := congrArg UInt64.toNat isStart
    simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
    have upper := slot.toNat_lt
    have lower := (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
    apply UInt64.toNat_inj.mp
    omega
  have boundary := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot)).2
  rw [rounded] at boundary
  have epochEqual := congrArg UInt64.toNat (blockEpoch.trans currentEpoch.symm)
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochEqual
  have blockLower : slot.toNat ≤ block.slot.toNat := by
    rw [boundary, computeEpochAtSlot, UInt64.toNat_div, ← epochEqual]
    exact Nat.div_mul_le_self _ _
  -- Phase 0 fork-choice `validate_on_attestation` delays votes until their slot is past.
  have noVote (index : ValidatorIndex) :
      ((e.world n).state u).voteCountsFor ⟨root, .pending⟩ index = false := by
    apply Bool.eq_false_iff.mpr
    intro counts
    obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
      Store.exists_of_voteCountsFor _ counts
    rw [Store.getSupportedNode_of_lt preGloas, Except.ok.injEq] at supportedOk
    subst supported
    obtain ⟨attestation, rfl, origin⟩ := forward.votesHaveOrigins latest
    obtain ⟨voted, votedKnown, votedLe⟩ := origin.voted
    obtain ⟨past, pastOk, pastLt⟩ := origin.past
    rw [slotOk, Except.ok.injEq] at pastOk
    subst past
    obtain ⟨nodeBlock, nodeKnown, ancestorLe⟩ := Store.slot_le_of_isAncestor known descends
    change ((e.world n).state u).blocks[attestation.data.beaconBlockRoot]? =
      some nodeBlock at nodeKnown
    rw [votedKnown, Option.some.injEq] at nodeKnown
    subst nodeBlock
    have := UInt64.le_iff_toNat_le.mp ancestorLe
    have := UInt64.le_iff_toNat_le.mp votedLe
    have := UInt64.lt_iff_toNat_lt.mp pastLt
    omega
  have zero := Store.getAttestationScore_toNat_eq_sum _ supportOk
  simp only [noVote, Bool.false_eq_true, ↓reduceIte, List.map_const', List.sum_replicate_nat,
    Nat.mul_zero] at zero
  have bounded := Store.computeEmptySlotSupportDiscount_le blockOk parentOk firstOk lastOk
    maximumOk discountOk notFuture
  have := UInt64.le_iff_toNat_le.mp bounded
  omega

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

So a block below the boundary of a later finality is not in the filtered tree.

The one exception is the justified block itself, and there the justified block covers it. -/
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

/-- Clock updates do not change the per-block pull-up cache. -/
private theorem walk_tick_cache {store after : Store preset fork} {time : UInt64}
    (ticked : store.onTick config time = .ok after) :
    after.unrealizedJustifications = store.unrealizedJustifications := by
  have step : ∀ {store after : Store preset fork} {time : UInt64},
      store.onTickPerSlot config time = .ok after →
      after.unrealizedJustifications = store.unrealizedJustifications := by
    intro store after time ticked
    unfold Store.onTickPerSlot at ticked
    simp only [bind_ok_iff] at ticked
    obtain ⟨previous, _, current, _, ticked⟩ := ticked
    split at ticked <;>
      · obtain ⟨_, _, ticked⟩ := ticked
        split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
          subst after <;> try rfl
        all_goals unfold Store.updateCheckpoints
        all_goals
          split <;> dsimp only <;> split <;> rfl
  have catchup : ∀ {start after : Store preset fork} {slot : Slot},
      Store.catchUp config start slot = .ok after →
      after.unrealizedJustifications = start.unrealizedJustifications := by
    intro start after slot caught
    induction start using Store.catchUp.induct config slot with
    | _ start ih =>
      rw [Store.catchUp.eq_1] at caught
      simp only [bind_ok_iff] at caught
      obtain ⟨current, _, caught⟩ := caught
      split at caught
      · simp only [bind_ok_iff] at caught
        obtain ⟨next, _, nextTime, _, ticked, tick, caught⟩ := caught
        split at caught
        · exact (ih ticked ‹_› caught).trans (step tick)
        · cases caught
      · cases Except.ok.inj caught
        rfl
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, _, caught, caughtOk, ticked⟩ := ticked
  exact (step ticked).trans (catchup caughtOk)

/-- Attestation processing changes votes and target states, not the pull-up cache. -/
private theorem walk_attestation_cache {store after : Store preset fork}
    {checks : SignatureChecks} {attestation : Attestation preset fork} {fromBlock : Bool}
    (attested : store.onAttestation config checks attestation fromBlock = .ok after) :
    after.unrealizedJustifications = store.unrealizedJustifications := by
  unfold Store.onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, cached, caching, _, _, _, _, _, _, _, _, attested⟩ := attested
  have kept : cached.unrealizedJustifications = store.unrealizedJustifications := by
    unfold Store.storeTargetCheckpointState at caching
    split at caching
    · cases Except.ok.inj caching
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at caching
      obtain ⟨_, _, rfl⟩ := caching
      rfl
  split at attested
  · cases Except.ok.inj attested
    exact kept
  · cases attested

/-- A pull-up cache entry is either retained or is the result counted at its own key. -/
private theorem walk_pulled_cache {store after : Store preset fork} {root key : Root}
    {checkpoint : Checkpoint}
    (computed : store.computePulledUpTip config root = .ok after)
    (entry : after.unrealizedJustifications[key]? = some checkpoint) :
    store.unrealizedJustifications[key]? = some checkpoint ∨
      ∃ state pulled, after.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = checkpoint := by
  have states := (Store.computePulledUpTip_frame computed).2.2.1
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, _, epoch, _, computed⟩ := computed
  have update : ∀ (s : Store preset fork) j f,
      (s.updateCheckpoints j f).unrealizedJustifications = s.unrealizedJustifications := by
    intro s j f
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> rfl
  have pending : ∀ (s : Store preset fork) j f,
      (s.updateUnrealizedCheckpoints j f).unrealizedJustifications = s.unrealizedJustifications := by
    intro s j f
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> rfl
  have cache : after.unrealizedJustifications =
      store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint := by
    split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
      subst after
    all_goals simp only [update, pending]
  rw [cache, getElem?_insert_root] at entry
  by_cases same : root = key
  · simp only [same, ↓reduceIte, Option.some.injEq] at entry
    exact .inr ⟨state, pulled, states.symm ▸ same ▸ Store.blockState_ok_iff.mp found,
      mapError_ok_iff.mp processed, entry⟩
  · exact .inl (by simpa [same] using entry)

/-- Block import retains old cache entries or computes the entry at its new block. -/
private theorem walk_block_cache {store after : Store preset fork}
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {key : Root} {checkpoint : Checkpoint}
    (added : store.onBlock config checks sources signed = .ok after)
    (entry : after.unrealizedJustifications[key]? = some checkpoint) :
    store.unrealizedJustifications[key]? = some checkpoint ∨
      ∃ state pulled, after.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = checkpoint := by
  cases root : Serialization.Ssz.SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact .inl entry
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, _, head, _, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedCache : recorded.unrealizedJustifications = store.unrealizedJustifications := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        rfl
      · cases record
        rfl
    have boostedCache : boosted.unrealizedJustifications = store.unrealizedJustifications := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedCache
    rcases walk_pulled_cache added entry with old | fresh
    · left
      have kept : (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).unrealizedJustifications = boosted.unrealizedJustifications := by
        unfold Store.updateCheckpoints
        split <;> dsimp only <;> split <;> rfl
      rwa [kept, boostedCache] at old
    · exact .inr fresh

/-- Every pull-up cache entry comes from its own block state, except the anchor entry. -/
private theorem walk_cache_origin {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (before : fork < .glamsterdam) {key : Root} {checkpoint : Checkpoint}
    (entry : store.unrealizedJustifications[key]? = some checkpoint) :
    checkpoint.epoch = getCurrentEpoch anchorState ∨
      ∃ state pulled, store.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = checkpoint := by
  induction reachable with
  | anchor made =>
    unfold getForkchoiceStore at made
    simp only [bind_ok_iff] at made
    obtain ⟨stateRoot, _, made⟩ := made
    split at made
    · cases made
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
      obtain ⟨root, _, time, _, rfl⟩ := made
      rw [getElem?_insert_root] at entry
      split at entry
      · cases Option.some.inj entry
        exact .inl rfl
      · simp at entry
  | tick prior ticked ih =>
    rw [walk_tick_cache ticked] at entry
    rcases ih entry with old | ⟨state, pulled, held, processed, same⟩
    · exact .inl old
    · exact .inr ⟨state, pulled, (Store.onTick_frame ticked).2.2.2.symm ▸ held,
        processed, same⟩
  | @block prior after checks sources signed reachable added ih =>
    rcases walk_block_cache added entry with old | fresh
    · rcases ih old with old | ⟨state, pulled, held, processed, same⟩
      · exact .inl old
      · right
        refine ⟨state, pulled, ?_, processed, same⟩
        rcases Store.onBlock_same_or_insert added with eq |
          ⟨newRoot, _, fresh, _, _, _, _, _, states⟩
        · exact eq ▸ held
        have other : newRoot ≠ key := by
          rintro rfl
          rw [reachable.blockState_eq_none fresh] at held
          cases held
        rw [states, getElem?_insert_root]
        simpa only [other, ↓reduceIte] using held
    · exact .inr fresh
  | attestation prior attested ih =>
    rw [walk_attestation_cache attested] at entry
    rcases ih entry with old | ⟨state, pulled, held, processed, same⟩
    · exact .inl old
    · exact .inr ⟨state, pulled, (Store.onAttestation_frame attested).2.2.symm ▸ held,
        processed, same⟩
  | attesterSlashing prior slashed ih =>
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact ih entry
  | payloadAttestation => exact False.elim (Nat.not_le_of_lt before ‹.glamsterdam ≤ fork›)
  | envelope => exact False.elim (Nat.not_le_of_lt before ‹.glamsterdam ≤ fork›)
  | inclusionList =>
    exact False.elim (Nat.not_le_of_lt before
      (Nat.le_trans (by decide : Fork.glamsterdam ≤ Fork.hegota) ‹.hegota ≤ fork›))

/-- Checkpoint provenance can depend on the block whose state holds the checkpoint. -/
private theorem walk_indexed_checkpoints {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {p : Root → Checkpoint → Prop}
    (anchor : ∀ root, store.blocks[root]? = some anchorBlock →
      CheckpointsSatisfy (p root) anchorState)
    (inherit : ∀ root (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      (∃ parent, store.blockStates[block.parentRoot]? = some parent) →
      ∀ checkpoint, p block.parentRoot checkpoint → p root checkpoint)
    (reads : ∀ root (block : BeaconBlock preset fork) (parent : BeaconState preset fork),
      store.blocks[root]? = some block → store.blockStates[block.parentRoot]? = some parent →
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
      ⟨inherit root block found ⟨parent, parentFound⟩ _ parentHolds.1,
        inherit root block found ⟨parent, parentFound⟩ _ parentHolds.2.1,
        inherit root block found ⟨parent, parentFound⟩ _ parentHolds.2.2⟩
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, run⟩ := slotsOk
    apply (lifted.advanceSlots ?_ run).of_frame (frame_processBlock blockOk)
    intro i bounded middle cached advanced cachedOk
    apply reads root block parent found parentFound checks i middle cached advanced cachedOk
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
private theorem walk_checkpoint_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot) (lower : store.ParentsBelow)
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
  · intro root block found held checkpoint holds
    rcases holds with old | ⟨descends, boundary, parent, parentFound, boundaryOk, below, read⟩
    · exact .inl old
    · have parentLt := lower root block parent found parentFound
      refine .inr ⟨Store.isAncestor_of_parent before found parentFound parentLt descends,
        boundary, block, found, boundaryOk, UInt64.le_trans below (UInt64.le_of_lt parentLt), ?_⟩
      have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) before found
        (UInt64.not_le.mpr (UInt64.lt_of_le_of_lt below parentLt)) parentFound parentLt
      simpa [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind, step] using read
  · intro root block parent found held checks count middle cached run cachedOk middleLt checkpoint recent read
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
    have parentLt := lower root block parentBlock found parentFound
    refine .inr ⟨Store.isAncestor_of_parent before found parentFound parentLt descends,
      start, block, found, startOk, UInt64.le_of_lt startLt, ?_⟩
    have step := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) before found
      (UInt64.not_le.mpr startLt) parentFound parentLt
    simpa [Store.getCheckpointBlock, startOk, Except.mapError, bind, Except.bind, step]
      using checkpointRead

/-- Pull-up justification preserves the stored block's checkpoint ancestry. -/
private theorem walk_pulled_checkpoint_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot) (lower : store.ParentsBelow)
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
  apply (walk_checkpoint_ancestor reachable sound before positive window aligned lower nonzero
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

/-- Both voting-source selectors return an anchor-era checkpoint or an ancestor. -/
private theorem walk_source_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot) (lower : store.ParentsBelow)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block ∧ block ≠ anchorBlock)
    {root : Root} {checkpoint : Checkpoint}
    (read : store.getVotingSource config root = .ok checkpoint ∨
      store.unrealizedJustification root = .ok checkpoint) :
    checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
      ∃ boundary block, store.blocks[root]? = some block ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root := by
  have cache : store.unrealizedJustifications[root]? = some checkpoint →
      checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
        ∃ boundary block, store.blocks[root]? = some block ∧
          computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧ boundary ≤ block.slot ∧
          store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root := by
    intro entry
    rcases walk_cache_origin reachable before entry with old |
      ⟨state, pulled, stored, processed, same⟩
    · exact .inl (by rw [old]; exact UInt64.le_refl _)
    · exact same ▸ (walk_pulled_checkpoint_ancestor reachable sound before positive window
        aligned lower nonzero child stored processed).2.1
  rcases read with source | unrealized
  · unfold Store.getVotingSource at source
    simp only [bind_ok_iff] at source
    obtain ⟨block, _, epoch, _, source⟩ := source
    split at source
    · cases entry : store.unrealizedJustifications[root]? with
      | none => simp [entry] at source
      | some value =>
        simp only [entry, pure, Except.pure, Except.ok.injEq] at source
        exact cache (source ▸ entry)
    · cases stored : store.blockStates[root]? with
      | none => simp [stored] at source
      | some state =>
        simp only [stored, pure, Except.pure, Except.ok.injEq] at source
        exact source ▸ (walk_checkpoint_ancestor reachable sound before positive window
          aligned lower nonzero child stored).2.1
  · unfold Store.unrealizedJustification at unrealized
    cases entry : store.unrealizedJustifications[root]? with
    | none => simp [entry] at unrealized
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at unrealized
      exact cache (unrealized ▸ entry)

/-- Both source selectors name a checkpoint covered by finalized-prefix agreement. -/
private theorem walk_source_justified {store : Store preset fork} {root : Root}
    {checkpoint : Checkpoint}
    (read : store.getVotingSource config root = .ok checkpoint ∨
      store.unrealizedJustification root = .ok checkpoint) : store.Justified checkpoint := by
  have cache : store.unrealizedJustifications[root]? = some checkpoint → store.Justified checkpoint :=
    fun entry => .inr (.inr (.inr ⟨root, entry⟩))
  rcases read with source | unrealized
  · unfold Store.getVotingSource at source
    simp only [bind_ok_iff] at source
    obtain ⟨block, _, epoch, _, source⟩ := source
    split at source
    · cases entry : store.unrealizedJustifications[root]? with
      | none => simp [entry] at source
      | some value =>
        simp only [entry, pure, Except.pure, Except.ok.injEq] at source
        exact cache (source ▸ entry)
    · cases stored : store.blockStates[root]? with
      | none => simp [stored] at source
      | some state =>
        simp only [stored, pure, Except.pure, Except.ok.injEq] at source
        exact .inr (.inr (.inl ⟨root, state, stored, source.symm⟩))
  · unfold Store.unrealizedJustification at unrealized
    cases entry : store.unrealizedJustifications[root]? with
    | none => simp [entry] at unrealized
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at unrealized
      exact cache (unrealized ▸ entry)

/-- A selected source cannot be newer than the current epoch of its store. -/
private theorem walk_source_epoch_le {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (aligned : anchorBlock.slot ≤ anchorState.slot) (before : fork < .glamsterdam)
    {epoch : Epoch} (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    {root : Root} {checkpoint : Checkpoint}
    (read : store.getVotingSource config root = .ok checkpoint ∨
      store.unrealizedJustification root = .ok checkpoint) : checkpoint.epoch ≤ epoch := by
  have reached := forward.reachable
  obtain ⟨current, currentOk, _, states⟩ := forward.slots_le_current slots aligned
  have epochEq : computeEpochAtSlot preset current = epoch := by
    simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure] using epochOk
  have bound : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      getCurrentEpoch s ≤ epoch := by
    intro r s held
    rw [← epochEq, UInt64.le_iff_toNat_le]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (states r s held))
  have cache : store.unrealizedJustifications[root]? = some checkpoint → checkpoint.epoch ≤ epoch := by
    intro entry
    rcases walk_cache_origin reached before entry with old | ⟨state, pulled, held, run, same⟩
    · obtain ⟨r, _, found⟩ := reached.anchor_known
      obtain ⟨s, held, anchored, _⟩ := reached.blockStatesFromParents found
      simpa only [old, anchored rfl] using bound r s held
    · have inv := (reached.ordered sound).2 held
      rw [← same]
      exact UInt64.le_trans
        (processJustificationAndFinalization_invariant inv.ordered inv.settled run).2.2.1
        (bound root state held)
  rcases read with source | unrealized
  · unfold Store.getVotingSource at source
    simp only [bind_ok_iff] at source
    obtain ⟨block, _, currentEpoch, _, source⟩ := source
    split at source
    · cases entry : store.unrealizedJustifications[root]? with
      | none => simp [entry] at source
      | some value =>
        simp only [entry, pure, Except.pure, Except.ok.injEq] at source
        exact cache (source ▸ entry)
    · cases held : store.blockStates[root]? with
      | none => simp [held] at source
      | some state =>
        simp only [held, pure, Except.pure, Except.ok.injEq] at source
        rw [← source]
        exact UInt64.le_trans
          (UInt64.le_trans ((reached.ordered sound).2 held).settled (getPreviousEpoch_le _))
          (bound root state held)
  · unfold Store.unrealizedJustification at unrealized
    cases entry : store.unrealizedJustifications[root]? with
    | none => simp [entry] at unrealized
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at unrealized
      exact cache (unrealized ▸ entry)

/-- A checkpoint read composes with an earlier checkpoint read even across empty slots. -/
private theorem walk_checkpoint_trans {store : Store preset fork}
    {root middle checkpoint : Root} {epoch earlier : Epoch}
    {boundary prior : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (priorOk : computeStartSlotAtEpoch preset earlier = .ok prior)
    (ordered : earlier ≤ epoch)
    (read : store.getCheckpointBlock root epoch = .ok middle)
    (priorRead : store.getCheckpointBlock middle earlier = .ok checkpoint)
    (before : fork < .glamsterdam) :
    store.getCheckpointBlock root earlier = .ok checkpoint := by
  have below : prior ≤ boundary := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [(computeStartSlotAtEpoch_ok_iff.mp priorOk).2,
      (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp ordered)
  unfold Store.getCheckpointBlock at read priorRead ⊢
  simp only [boundaryOk, priorOk, Except.mapError, bind, Except.bind] at read priorRead ⊢
  cases walked : store.getAncestor ⟨root, .pending⟩ boundary with
  | error err => simp [walked] at read
  | ok node =>
    have pending := Store.getAncestor_pending_of_lt before rfl walked
    simp only [walked, pure, Except.pure, Except.ok.injEq] at read
    have nodeEq : node = ⟨middle, .pending⟩ := by
      cases node
      simp_all
    subst node
    have through := Store.getAncestor_trans below walked
    rw [through]
    exact priorRead

omit [DecidablePred (· ∈ J)] in
/-- An exact source boundary read carries finalized-prefix agreement back to its block. -/
private theorem walk_finalized_read_of_source {horizon : Epoch}
    (chain : FinalizedPrefix e horizon) (before : fork < .glamsterdam)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    {root : Root} {checkpoint : Checkpoint} {boundary : Slot}
    (source : ((e.world n).state u).getVotingSource config root = .ok checkpoint ∨
      ((e.world n).state u).unrealizedJustification root = .ok checkpoint)
    (boundaryOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary)
    (read : ((e.world n).state u).getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (ordered : ((e.world k).state w).finalizedCheckpoint.epoch ≤ checkpoint.epoch)
    (inHorizon : checkpoint.epoch ≤ horizon) :
    ((e.world n).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
  have priorRead := chain w receiver u caller k n checkpoint (walk_source_justified source)
    ordered inHorizon
  have splitRead := priorRead
  unfold Store.getCheckpointBlock at splitRead
  simp only [bind_ok_iff] at splitRead
  obtain ⟨prior, priorOk, _⟩ := splitRead
  exact walk_checkpoint_trans boundaryOk (mapError_ok_iff.mp priorOk) ordered read priorRead before

omit [DecidablePred (· ∈ J)] in
/-- Every held block reads an epoch-aligned anchor at the anchor's checkpoint boundary. -/
private theorem walk_anchor_read {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (before : fork < .glamsterdam) {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ}
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world n).state u).blocks[root]? = some block) :
    ((e.world n).state u).getCheckpointBlock root anchor.finalizedCheckpoint.epoch =
      .ok anchor.finalizedCheckpoint.root := by
  have reached := e.reachable
    (fun w hw => (anchored w hw) ▸ Store.Reachable.anchor anchorStore) n u honest
  obtain ⟨r, hashed, _, _, _, final, _, _⟩ := getForkchoiceStore_anchor anchorStore
  obtain ⟨r', hashed', found⟩ := reached.anchor_known
  rw [hashed, Except.ok.injEq] at hashed'
  subst r'
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
    have lower := (anchorState.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
    apply UInt64.toNat_inj.mp
    omega
  have boundaryOk : computeStartSlotAtEpoch preset anchor.finalizedCheckpoint.epoch =
      .ok anchorBlock.slot := by
    simpa [final, getCurrentEpoch, rounded, anchorSlot] using
      computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot
  have descends := e.isAncestor_anchor_of_known anchorStore anchored honest known
  rw [final] at descends
  have path := Store.getAncestor_of_isAncestor_of_lt before found descends
  unfold Store.getCheckpointBlock
  rw [boundaryOk]
  simp only [Except.mapError, bind, Except.bind, path, pure, Except.pure, final]

omit [DecidablePred (· ∈ J)] in
/-- Prefix agreement identifies a finalized checkpoint whose epoch is still the anchor's. -/
private theorem walk_finalized_eq_anchor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (before : fork < .glamsterdam) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    (upper : ((e.world k).state w).finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState)
    (inHorizon : getCurrentEpoch anchorState ≤ horizon) :
    ((e.world k).state w).finalizedCheckpoint = anchor.finalizedCheckpoint := by
  obtain ⟨r, _, found, _, justified, final, _, _⟩ := getForkchoiceStore_anchor anchorStore
  have lower := (e.epochsLe_of_le w (Nat.zero_le k)).2
  simp only [Execution.world_zero, World.initial, anchored w honest, final] at lower
  have epochEq := UInt64.le_antisymm upper lower
  have justifiedAt : ((e.world 0).state w).Justified anchor.justifiedCheckpoint := by
    change (e.start w).Justified anchor.justifiedCheckpoint
    rw [anchored w honest]
    exact .inl rfl
  have read := chain w honest w honest k 0 anchor.justifiedCheckpoint justifiedAt
    (by simpa only [justified] using upper) (by simpa only [justified] using inHorizon)
  have known : ((e.world 0).state w).blocks[r]? = some anchorBlock := by
    simpa only [Execution.world_zero, World.initial, anchored w honest] using found
  have own := walk_anchor_read anchorStore anchored anchorSlot anchorBoundary before honest known
  rw [justified, epochEq] at read
  rw [final] at own
  have rootEq := Except.ok.inj (own.symm.trans read)
  rw [final]
  cases cp : ((e.world k).state w).finalizedCheckpoint
  simp_all

omit [DecidablePred (· ∈ J)] in
/-- At a common epoch, a source at most two epochs old covers receiver finality. -/
private theorem walk_finalized_read_of_recent_source {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (before : fork < .glamsterdam) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch : Epoch}
    (callerEpoch : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (receiverEpoch : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
    (lower : ((e.world n).state u).ParentsBelow)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock)
    {root : Root} {block : BeaconBlock preset fork} {checkpoint : Checkpoint}
    (known : ((e.world n).state u).blocks[root]? = some block)
    (source : ((e.world n).state u).getVotingSource config root = .ok checkpoint ∨
      ((e.world n).state u).unrealizedJustification root = .ok checkpoint)
    (recent : epoch.toNat ≤ checkpoint.epoch.toNat + 2) :
    ((e.world n).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore) n u caller
  have anchorRead := walk_anchor_read anchorStore anchored anchorSlot anchorBoundary before caller known
  rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound receiver
      (anchored w receiver) receiverEpoch with same | age
  · simpa only [same] using anchorRead
  have ordered : ((e.world k).state w).finalizedCheckpoint.epoch ≤ checkpoint.epoch :=
    UInt64.le_iff_toNat_le.mpr (by omega)
  rcases walk_source_ancestor forward.reachable sound before positive window
      (UInt64.le_of_eq anchorSlot) lower nonzero child source with old |
      ⟨_, boundary, _, _, boundaryOk, _, read⟩
  · have same := walk_finalized_eq_anchor anchorStore anchored anchorSlot anchorBoundary before
      chain receiver (UInt64.le_trans ordered old) anchorHorizon
    simpa only [same] using anchorRead
  · exact walk_finalized_read_of_source chain before caller receiver source boundaryOk read ordered
      (UInt64.le_trans (walk_source_epoch_le forward sound slots (UInt64.le_of_eq anchorSlot)
        before callerEpoch source) inHorizon)

/-- A two-epoch advance contains a complete epoch, with representable boundaries. -/
private theorem walk_complete_of_epoch_gap {slot current : Slot} {begin endpoint : UInt64}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (endpointOk : computeTimeAtSlotMs config genesisTimeMs current = .ok endpoint)
    (gap : (computeEpochAtSlot preset slot).toNat + 2 ≤
      (computeEpochAtSlot preset current).toNat) :
    CompleteEpochWithin preset config genesisTimeMs begin.toNat endpoint.toNat := by
  let E := (computeEpochAtSlot preset slot).toNat
  let size := preset.SLOTS_PER_EPOCH.toNat
  have endLe : (E + 2) * size ≤ current.toNat :=
    (Nat.mul_le_mul_right size gap).trans (Nat.div_mul_le_self _ _)
  have startLe : (E + 1) * size ≤ current.toNat := by
    have := Nat.mul_le_mul_right size (show E + 1 ≤ E + 2 by omega)
    omega
  have epochBound : E + 1 < 2 ^ 64 := by
    have := (computeEpochAtSlot preset current).toNat_lt
    change E + 2 ≤ _ at gap
    omega
  have startBound : (E + 1) * size < 2 ^ 64 := startLe.trans_lt current.toNat_lt
  have endBound : (E + 2) * size < 2 ^ 64 := endLe.trans_lt current.toNat_lt
  let epoch : Epoch := (E + 1).toUInt64
  let first : Slot := ((E + 1) * size).toUInt64
  let next : Slot := ((E + 2) * size).toUInt64
  have epochNat : epoch.toNat = E + 1 := UInt64.toNat_ofNat_of_lt' epochBound
  have firstNat : first.toNat = (E + 1) * size := UInt64.toNat_ofNat_of_lt' startBound
  have nextNat : next.toNat = (E + 2) * size := UInt64.toNat_ofNat_of_lt' endBound
  have firstOk : computeStartSlotAtEpoch preset epoch = .ok first := by
    apply computeStartSlotAtEpoch_ok_iff.mpr
    exact ⟨by simpa [epochNat] using startBound, by simp [epochNat, firstNat, size]⟩
  have nextOk : addChecked first preset.SLOTS_PER_EPOCH = .ok next := by
    apply addChecked_ok_iff.mpr
    constructor
    · rw [firstNat]
      simp only [Nat.add_mul, Nat.one_mul] at endBound ⊢
      dsimp [size] at *
      omega
    · rw [firstNat, nextNat]
      simp [Nat.add_mul, size]
      omega
  have firstLe : first ≤ current := UInt64.le_iff_toNat_le.mpr (firstNat ▸ startLe)
  have nextLe : next ≤ current := UInt64.le_iff_toNat_le.mpr (nextNat ▸ endLe)
  obtain ⟨firstTime, firstTimeOk, firstTimeNat, _⟩ := exists_timeAtSlotMs_of_le firstLe endpointOk
  obtain ⟨nextTime, nextTimeOk, _, nextTimeLe⟩ := exists_timeAtSlotMs_of_le nextLe endpointOk
  have slotLe : slot ≤ first := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [firstNat]
    have bound := Nat.lt_mul_div_succ slot.toNat positive
    exact Nat.le_of_lt (by simpa [E, size, computeEpochAtSlot, Nat.mul_comm] using bound)
  obtain ⟨sameTime, sameTimeOk, _, timeLe⟩ := exists_timeAtSlotMs_of_le slotLe firstTimeOk
  rw [beginOk, Except.ok.injEq] at sameTimeOk
  subst sameTime
  exact ⟨epoch, first, next, firstTime, nextTime, firstOk, nextOk, firstTimeOk, nextTimeOk,
    UInt64.le_iff_toNat_le.mp timeLe, UInt64.le_iff_toNat_le.mp nextTimeLe⟩

/-- Before a complete epoch, a recent parent remains within the receiver's two-epoch cap. -/
private theorem walk_receiver_age {slot current : Slot} {begin endpoint : UInt64}
    {parentEpoch : Epoch}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (endpointOk : computeTimeAtSlotMs config genesisTimeMs current = .ok endpoint)
    (recent : (computeEpochAtSlot preset slot).toNat ≤ parentEpoch.toNat + 1)
    (initial : ¬CompleteEpochWithin preset config genesisTimeMs begin.toNat endpoint.toNat) :
    (computeEpochAtSlot preset current).toNat ≤ parentEpoch.toNat + 2 := by
  have gap := mt (walk_complete_of_epoch_gap positive beginOk endpointOk) initial
  omega

/-- A checkpoint read of a descendant is also a read of an ancestor above its boundary. -/
private theorem walk_checkpoint_of_descendant {store : Store preset fork}
    (before : fork < .glamsterdam) {tip root checkpoint : Root} {epoch : Epoch}
    {block : BeaconBlock preset fork} {boundary : Slot}
    (known : store.blocks[root]? = some block)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (below : boundary ≤ block.slot)
    (read : store.getCheckpointBlock tip epoch = .ok checkpoint) :
    store.getCheckpointBlock root epoch = .ok checkpoint := by
  have path := Store.getAncestor_of_isAncestor_of_lt before known descends
  have through := Store.getAncestor_trans below path
  simpa only [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind,
    through] using read

/-- Two-epoch-old finality is below every block of the current or previous epoch. -/
private theorem walk_finalized_boundary_below {block : BeaconBlock preset fork}
    {epoch finalized : Epoch} {boundary : Slot}
    (recent : epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (age : finalized.toNat + 2 ≤ epoch.toNat)
    (boundaryOk : computeStartSlotAtEpoch preset finalized = .ok boundary) :
    boundary ≤ block.slot := by
  have epochLe : finalized.toNat ≤ block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div] at recent
    omega
  apply UInt64.le_iff_toNat_le.mpr
  rw [(computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2]
  exact (Nat.mul_le_mul_right _ epochLe).trans (Nat.div_mul_le_self _ _)

omit [DecidablePred (· ∈ J)] in
/-- A recent descendant's source certifies finality for the recent block below it. -/
private theorem walk_finalized_read_below_source {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (before : fork < .glamsterdam) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch : Epoch}
    (callerEpoch : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (receiverEpoch : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
    (lower : ((e.world n).state u).ParentsBelow)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock)
    {root tip : Root} {block : BeaconBlock preset fork} {checkpoint : Checkpoint}
    (known : ((e.world n).state u).blocks[root]? = some block)
    (descends : ((e.world n).state u).isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (source : ((e.world n).state u).getVotingSource config tip = .ok checkpoint ∨
      ((e.world n).state u).unrealizedJustification tip = .ok checkpoint)
    (recent : epoch.toNat ≤ checkpoint.epoch.toNat + 2)
    (blockRecent : epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1) :
    ((e.world n).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
  rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound receiver
      (anchored w receiver) receiverEpoch with same | age
  · simpa only [same] using
      walk_anchor_read anchorStore anchored anchorSlot anchorBoundary before caller known
  obtain ⟨tipBlock, tipKnown, _⟩ := Store.slot_le_of_isAncestor known descends
  have read := walk_finalized_read_of_recent_source anchorStore anchored sound slots positive window
    anchorSlot anchorBoundary before chain caller receiver callerEpoch receiverEpoch inHorizon
    anchorHorizon lower nonzero child tipKnown source recent
  have splitRead := read
  unfold Store.getCheckpointBlock at splitRead
  simp only [bind_ok_iff] at splitRead
  obtain ⟨boundary, boundaryOk, _⟩ := splitRead
  have boundaryOk := mapError_ok_iff.mp boundaryOk
  exact walk_checkpoint_of_descendant before known descends boundaryOk
    (walk_finalized_boundary_below blockRecent age boundaryOk) read

/-- A checked root outside the current epoch has a recent source on its chain. -/
private theorem walk_checked_source {store : Store preset fork} {fcr : FastConfirmationStore}
    {head start root : Root} {epoch rootEpoch : Epoch}
    (checked : store.Checked config fcr head start root)
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (rootEpochOk : store.getBlockEpoch root = .ok rootEpoch)
    (older : rootEpoch ≠ epoch) :
    ∃ tip source, store.getVotingSource config tip = .ok source ∧
      epoch.toNat ≤ source.epoch.toNat + 2 ∧
      (tip = root ∨ store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true) := by
  obtain ⟨readEpoch, slot, readRootEpoch, startEpoch, readEpochOk, _, readRootEpochOk,
    _, _, branches⟩ := checked
  rw [epochOk, Except.ok.injEq] at readEpochOk
  rw [rootEpochOk, Except.ok.injEq] at readRootEpochOk
  subst readEpoch
  subst readRootEpoch
  rcases branches with previous | current
  · obtain ⟨source, sourceOk, recent, descends⟩ := previous.2.2.1
    exact ⟨fcr.previousSlotHead, source, sourceOk, recent, Or.inr descends⟩
  · obtain ⟨source, sourceOk, recent⟩ := (current.2.2 older).1
    exact ⟨root, source, sourceOk, recent, Or.inl rfl⟩

/-- Every walked member is at least as recent as the checked start. -/
private theorem walk_member_recent {store : Store preset fork} {fcr : FastConfirmationStore}
    {head start root member : Root} {roots : List Root} {epoch : Epoch}
    {block : BeaconBlock preset fork}
    (checked : store.Checked config fcr head start root)
    (walked : store.getAncestorRoots head start = .ok roots) (mem : member ∈ roots)
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (known : store.blocks[member]? = some block) :
    epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1 := by
  obtain ⟨readEpoch, slot, rootEpoch, startEpoch, readEpochOk, _, _, startEpochOk, recent, _⟩ :=
    checked
  rw [epochOk, Except.ok.injEq] at readEpochOk
  subst readEpoch
  obtain ⟨same, startBlock, sameOk, startOk, below⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) mem
  rw [Store.block_ok_iff.mpr known, Except.ok.injEq] at sameOk
  subst same
  have startEq : startEpoch = computeEpochAtSlot preset startBlock.slot := by
    simpa [Store.getBlockEpoch, startOk, bind, Except.bind, pure, Except.pure] using
      startEpochOk.symm
  have le : (computeEpochAtSlot preset startBlock.slot).toNat ≤
      (computeEpochAtSlot preset block.slot).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp below))
  rw [startEq] at recent
  omega

omit [DecidablePred (· ∈ J)] in
/-- A recent recorded vote belongs to the caller-head committees of any range containing its slot.

The common-state comparison applies to every recorded voter, not only honest voters. -/
private theorem walk_vote_mem_window (committees : CommitteesFollow e)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {head : ForkChoiceNode}
    {headState : BeaconState preset fork} {current : Epoch}
    {v : ValidatorIndex} {attestation : Attestation preset fork}
    {first last : Slot} {participants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (stateOk : ((e.world n).state u).blockState head.root = .ok headState)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok current)
    (past : attestation.data.target.epoch.toNat ≤ current.toNat)
    (recent : current.toNat ≤ attestation.data.target.epoch.toNat + 1)
    (origin : ((e.world n).state u).VoteOrigin config v attestation)
    (windowOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants)
    (low : first ≤ attestation.data.slot) (high : attestation.data.slot ≤ last) :
    v ∈ participants := by
  obtain ⟨targetState, index, committee, targetOk, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  obtain ⟨common, headRun, targetRun, final, fixed, headRing, targetRing⟩ :=
    committees.common u caller n head headState current v attestation targetState
      headOk stateOk epochOk past recent origin targetOk
  have headKept := headRun.committeesKept final fixed headRing
  have targetKept := targetRun.committeesKept final fixed targetRing
  have same := (headKept attestation.data.slot index origin.targetEpoch.symm).trans
    (targetKept attestation.data.slot index origin.targetEpoch.symm).symm
  have active := (headRun.active.getActiveValidatorIndices_eq fixed).trans
    (targetRun.active.getActiveValidatorIndices_eq fixed).symm
  have count : getCommitteeCountPerSlot headState (computeEpochAtSlot preset attestation.data.slot) =
      getCommitteeCountPerSlot targetState (computeEpochAtSlot preset attestation.data.slot) := by
    simp only [← origin.targetEpoch, getCommitteeCountPerSlot, active]
  exact Store.mem_getCommitteesBetweenSlots windowOk low high stateOk
    (count ▸ below) (same.trans committeeOk) member

omit [DecidablePred (· ∈ J)] in
/-- Every supporter of a recent block belongs to its caller-head adversary window. -/
private theorem walk_supporters_in_window (committees : CommitteesFollow e)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {head : ForkChoiceNode}
    {headState source : BeaconState preset fork} {current : Epoch}
    {root : Root} {block : BeaconBlock preset fork} {slot first last : Slot}
    {participants : Std.TreeSet ValidatorIndex}
    (origins : ((e.world n).state u).VotesHaveOrigins config)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (stateOk : ((e.world n).state u).blockState head.root = .ok headState)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok current)
    (known : ((e.world n).state u).blocks[root]? = some block)
    (recent : current.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (firstLe : first ≤ block.slot) (lastOk : subChecked slot 1 = .ok last)
    (windowOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants) :
    ∀ v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩, v ∈ participants := by
  intro v supporter
  obtain ⟨message, supported, latest, _, supportedOk, descends⟩ :=
    ((e.world n).state u).exists_of_voteCountsFor
      (Store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨attestation, rfl, origin⟩ := origins latest
  obtain ⟨votedBlock, votedKnown, votedLe⟩ := origin.voted
  obtain ⟨same, sameKnown, below⟩ := Store.slot_le_of_isAncestor known descends
  have rootEq := Store.getSupportedNode_root supportedOk
  change supported.root = attestation.data.beaconBlockRoot at rootEq
  rw [rootEq, votedKnown, Option.some.injEq] at sameKnown
  subst same
  have blockLe := UInt64.le_trans below votedLe
  obtain ⟨readSlot, readOk, past⟩ := origin.past
  rw [slotOk, Except.ok.injEq] at readOk
  subst readSlot
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have high : attestation.data.slot ≤ last := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one] at lastNat
    omega)
  have epochEq : current = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using
      epochOk.symm
  have monotone {a b : Slot} (le : a ≤ b) :
      (computeEpochAtSlot preset a).toNat ≤ (computeEpochAtSlot preset b).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp le)
  apply walk_vote_mem_window committees caller headOk stateOk epochOk
    (by rw [origin.targetEpoch, epochEq]; exact monotone (UInt64.le_of_lt past))
    (by rw [origin.targetEpoch]; have := monotone blockLe; omega) origin windowOk
    (UInt64.le_trans firstLe blockLe) high

/-- A recent one-confirmed block has an honest supporter in the caller's tally. -/
private theorem walk_exists_honest_supporter (committees : CommitteesFollow e)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {head : ForkChoiceNode}
    {headState source : BeaconState preset fork} {current : Epoch}
    {root : Root} {block : BeaconBlock preset fork} {slot : Slot}
    (origins : ((e.world n).state u).VotesHaveOrigins config)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (stateOk : ((e.world n).state u).blockState head.root = .ok headState)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok current)
    (known : ((e.world n).state u).blocks[root]? = some block)
    (recent : current.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (notFuture : block.slot ≤ slot)
    (within : source.RegistryWithinLimit) (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J)
    (byzantine : ∀ first last participants,
      ((e.world n).state u).getCommitteesBetweenSlots head.root first last = .ok participants →
      ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
        (Store.activeMembers source participants) J
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (confirmed : ((e.world n).state u).isOneConfirmed config head.root source
      (((e.world n).state u).tallyVotes source) root = .ok true) :
    ∃ v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩, v ∈ J := by
  obtain ⟨support, threshold, _, thresholdOk, _⟩ :=
    Store.isOneConfirmed_eq_ok_true_iff.mp confirmed
  obtain ⟨readSlot, readBlock, parent, score, first, last, maximum, discount, adversary,
    readSlotOk, readBlockOk, parentOk, scoreOk, firstOk, lastOk, maximumOk, discountOk,
    adversaryOk⟩ := Store.computeSafetyThreshold_eq_ok thresholdOk
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  rw [Store.block_ok_iff.mpr known, Except.ok.injEq] at readBlockOk
  subst readBlock
  obtain ⟨readSlot, readBlock, startSlot, readLast, readSlotOk, readBlockOk, readLastOk,
    startOk, rangeOk⟩ := Store.getAdversarialWeight_eq_ok adversaryOk
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  rw [Store.block_ok_iff.mpr known, Except.ok.injEq] at readBlockOk
  subst readBlock
  rw [lastOk, Except.ok.injEq] at readLastOk
  subst readLast
  obtain ⟨weight, equivocation, _, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨participants, participantsOk, _⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have firstLe : startSlot ≤ block.slot := by
    rcases startOk with rfl | boundary
    · exact UInt64.le_refl _
    · apply UInt64.le_iff_toNat_le.mpr
      rw [(computeStartSlotAtEpoch_ok_iff.mp boundary).2]
      exact Nat.div_mul_le_self _ _
  have inside := walk_supporters_in_window committees caller origins headOk stateOk slotOk
    epochOk known recent firstLe lastOk participantsOk (source := source)
  have positive := Store.lt_two_mul_honest_supportersOf_of_isOneConfirmed within slotOk
    (Store.block_ok_iff.mpr known) parentOk scoreOk firstOk lastOk maximumOk discountOk
    adversaryOk rangeOk participantsOk confirmed inside aligned increment dishonest
    (byzantine _ _ _ participantsOk)
  have discountLe := UInt64.le_iff_toNat_le.mp
    (Store.computeEmptySlotSupportDiscount_le (Store.block_ok_iff.mpr known) parentOk firstOk
      lastOk maximumOk discountOk notFuture)
  by_contra absent
  have empty : {v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩ | v ∈ J} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v member
    exact absent ⟨v, (Finset.mem_filter.mp member).1, (Finset.mem_filter.mp member).2⟩
  rw [empty, stake_empty] at positive
  omega

/-- A past honest supporter delivers the block once the caller establishes receiver finality. -/
private theorem walk_known_of_honest_supporter {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (fits : DelayFits fork config genesisTimeMs Δ)
    (preGloas : fork < .glamsterdam) (oneBlock : OneBlockPerRoot e)
    (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {u v w : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) (receiver : w ∈ J)
    {n k : ℕ} (later : (e.world n).time ≤ (e.world k).time)
    (callerCurrent : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (receiverCurrent : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {source : BeaconState preset fork} (within : source.RegistryWithinLimit)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world n).state u).blocks[root]? = some block)
    (supporter : v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩)
    (finalizedKnown : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).finalizedCheckpoint.root]? = some b)
    (checkpoint : ((e.world n).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root) :
    ((e.world k).state w).blocks[root]? = some block := by
  obtain ⟨m, _, pastBlock, pastKnown, delivered⟩ := e.past_block_of_honest_supporter
    slots fits oneBlock anchorStore anchored caller honest callerCurrent within supporter
  have same := oneBlock v honest u caller m n root pastBlock block pastKnown known
  subst pastBlock
  have reached := e.reachable
    (fun x hx => (anchored x hx) ▸ Store.Reachable.anchor anchorStore) m v honest
  have checkpointCopy := checkpoint
  unfold Store.getCheckpointBlock at checkpointCopy
  simp only [bind_ok_iff, mapError_ok_iff] at checkpointCopy
  obtain ⟨boundary, boundaryOk, _⟩ := checkpointCopy
  have above := e.anchorSlot_le_finalized_boundary anchorStore anchorSlot anchorBoundary
    (anchored w receiver) boundaryOk
  have pastCheckpoint := Store.getCheckpointBlock_of_same_blocks reached
    (oneBlock u caller v honest n m) boundaryOk above ⟨block, pastKnown⟩ checkpoint
  exact (e.blocks_of_partiallySynchronous sync oneBlock admitted anchorStore anchored honest
    receiver (by simpa using delivered.trans later) receiverCurrent finalizedKnown
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) pastKnown pastCheckpoint).1

/-- Each new member of the increasing root walk lies on the tip's ancestor chain. -/
private theorem walk_member_ancestor {store : Store preset fork}
    (before : fork < .glamsterdam) {tip terminal : Root} {acc roots : List Root}
    (walked : store.getAncestorRoots tip terminal acc = .ok roots) :
    ∀ member ∈ roots, member ∈ acc ∨
      ∃ block, store.blocks[member]? = some block ∧
        store.getAncestor ⟨tip, .pending⟩ block.slot = .ok ⟨member, .pending⟩ := by
  fun_induction Store.getAncestorRoots store tip terminal acc generalizing roots with
  | case1 => cases walked
  | case2 tip acc block found ih =>
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, _, walked⟩ := walked
    split at walked
    · cases Except.ok.inj walked
      simp
    · dsimp only at walked
      split at walked
      · cases Except.ok.inj walked
        intro member mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact Or.inr ⟨block, found,
            Store.getAncestor_of_le found (UInt64.le_refl _)⟩
        · exact Or.inl mem
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            intro member mem
            rcases ih parent parentFound lower walked member mem with old | ⟨b, held, path⟩
            · rcases List.mem_cons.mp old with rfl | old
              · exact Or.inr ⟨block, found,
                  Store.getAncestor_of_le found (UInt64.le_refl _)⟩
              · exact Or.inl old
            · have parentWalk := Store.getAncestor_parent_of_slot_lt
                (node := (⟨tip, .pending⟩ : ForkChoiceNode)) found parentFound lower
              rw [Store.parentPayloadStatus_of_lt before] at parentWalk
              have descends : store.isAncestor ⟨block.parentRoot, .pending⟩
                  ⟨member, .pending⟩ = .ok true := by
                simp [Store.isAncestor, Store.block_ok_iff.mpr held, path,
                  bind, Except.bind, pure, Except.pure]
              obtain ⟨same, sameFound, le⟩ := Store.slot_le_of_isAncestor held descends
              have eq := Option.some.inj (parentFound.symm.trans sameFound)
              subst same
              exact Or.inr ⟨b, held, (Store.getAncestor_trans le parentWalk).trans path⟩
          · cases walked

/-- Induction follows parent edges while keeping the complete returned walk fixed. -/
private theorem walk_members_induction {store : Store preset fork}
    {tip terminal : Root} {acc roots : List Root} (P : Root → Prop)
    (walked : store.getAncestorRoots tip terminal acc = .ok roots)
    (base : P terminal)
    (step : ∀ member ∈ roots, ∀ block, store.blocks[member]? = some block →
      P block.parentRoot → P member)
    (accStep : P tip → ∀ member ∈ acc, P member) :
    ∀ member ∈ roots, P member := by
  fun_induction Store.getAncestorRoots store tip terminal acc generalizing roots with
  | case1 => cases walked
  | case2 tip acc block found ih =>
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, _, walked⟩ := walked
    split at walked
    · cases Except.ok.inj walked
      simp
    · dsimp only at walked
      split at walked
      · rename_i parentEq
        cases Except.ok.inj walked
        have tipSafe := step tip (by simp) block found (parentEq ▸ base)
        intro member mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact tipSafe
        · exact accStep tipSafe member mem
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            rcases Store.getAncestorRoots_eq_nil_or walked with empty | ⟨front, shape⟩
            · subst roots
              simp
            · have tipMem : tip ∈ roots := by simp [shape]
              apply ih parent parentFound lower walked step
              intro parentSafe member mem
              have tipSafe := step tip tipMem block found parentSafe
              rcases List.mem_cons.mp mem with rfl | mem
              · exact tipSafe
              · exact accStep tipSafe member mem
          · cases walked

/-- The time induction supplies all earlier members before advancing along the same walk. -/
private theorem walk_time_members_induction {store : Store preset fork}
    {tip terminal : Root} {roots : List Root} {first limit : ℕ}
    (P : ℕ → Root → Prop)
    (walked : store.getAncestorRoots tip terminal = .ok roots)
    (base : ∀ time, first ≤ time → time ≤ limit → P time terminal)
    (step : ∀ time, first ≤ time → time ≤ limit →
      (∀ earlier, first ≤ earlier → earlier < time → ∀ member ∈ roots, P earlier member) →
      ∀ member ∈ roots, ∀ block, store.blocks[member]? = some block →
        P time block.parentRoot → P time member) :
    ∀ time, first ≤ time → time ≤ limit → ∀ member ∈ roots, P time member := by
  intro time
  induction time using Nat.strong_induction_on with
  | h time ih =>
    intro firstLe limitLe
    apply walk_members_induction (P time) walked (base time firstLe limitLe)
    · exact step time firstLe limitLe (fun earlier lower upper =>
        ih earlier upper lower (Nat.le_trans (Nat.le_of_lt upper) limitLe))
    · simp

/-- The tally indices are the registry positions used by the missing-weight head theorem. -/
private theorem walk_tally_indices {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) :
    ((unslashedActiveBalances state).map (·.1)).toFinset.image UInt64.toNat =
      Store.voters state := by
  ext i
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map,
    unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq, Prod.exists, Store.voters, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨v, ⟨index, balance, ⟨validator, j, inZip, active, rfl, rfl⟩, rfl⟩, rfl⟩
    have found := List.mem_zipIdx_iff_getElem?.mp inZip
    have lt : j < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    rw [toNat_toUInt64_of_lt within lt]
    exact ⟨lt, by simpa [Store.counts, ← Array.getElem?_toList, found] using active⟩
  · rintro ⟨lt, active⟩
    cases found : state.validators.data[i]? with
    | none => simp [Store.counts, found] at active
    | some validator =>
      refine ⟨i.toUInt64, ⟨i.toUInt64, validator.effectiveBalance, ?_, rfl⟩,
        toNat_toUInt64_of_lt within lt⟩
      refine ⟨validator, i, ?_, ?_, rfl, rfl⟩
      · exact List.mem_zipIdx_iff_getElem?.mpr (by simpa using found)
      · simpa [Store.counts, found] using active

/-- Reindexing the tally preserves every selected stake, including honest and missing duties. -/
private theorem walk_tally_stake {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (P : ValidatorIndex → Prop) [DecidablePred P] :
    stake (balanceAt state) {i ∈ Store.voters state | P i.toUInt64} =
      stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | P v} := by
  rw [← walk_tally_indices within]
  have selected :
      {i ∈ ((unslashedActiveBalances state).map (·.1)).toFinset.image UInt64.toNat |
        P i.toUInt64} =
      ({v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | P v}).image
        UInt64.toNat := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, member, rfl⟩, passes⟩
      exact ⟨v, ⟨member, by simpa using passes⟩, rfl⟩
    · rintro ⟨v, ⟨member, passes⟩, rfl⟩
      exact ⟨⟨v, member, rfl⟩, by simpa using passes⟩
  rw [selected, stake, Finset.sum_image]
  · rfl
  · intro a _ b _ eq
    exact UInt64.toNat_inj.mp eq

/-- The late-duty inequality is the missing-weight inequality in the receiver's own state. -/
private theorem walk_head_of_missing_duties {store : Store preset fork}
    {state : BeaconState preset fork} {config : Config} {nodes : List ForkChoiceNode}
    {node head : ForkChoiceNode} {score : Gwei} {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] (duty : ValidatorIndex → Prop) [DecidablePred duty]
    (within : state.RegistryWithinLimit) (lower : store.ParentsBelow)
    (before : fork < .glamsterdam)
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : node ∈ nodes)
    (scoreOk : store.getAttestationScore node state = .ok score)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      ((unslashedActiveBalances state).map (·.1)).toFinset J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (supported : ∀ v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset,
      v ∈ J → duty v → v ∈ store.supportersOf state node)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (margin : 100 * (2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧ ¬duty v} +
        store.boostScore config) <
      (100 - 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) *
        stake (fun v => balanceAt state v.toNat)
          ((unslashedActiveBalances state).map (·.1)).toFinset)
    (headOk : store.getHead config = .ok head) :
    store.isAncestor head node = .ok true := by
  classical
  let V := ((unslashedActiveBalances state).map (·.1)).toFinset
  let missing := stake (fun v => balanceAt state v.toNat) {v ∈ V | v ∈ J ∧ ¬duty v}
  have total := walk_tally_stake within (fun _ => True)
  simp only [Finset.filter_true] at total
  have honest := walk_tally_stake within (fun v => v ∈ J)
  have dishonest := walk_tally_stake within (fun v => v ∉ J)
  have bound : ByzantineStakeAtMost (balanceAt state) (Store.voters state)
      {i | i.toUInt64 ∈ J} config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 := by
    simpa only [ByzantineStakeAtMost, Set.mem_ofPred_eq, total, dishonest] using byzantine
  have support : stake (balanceAt state)
      {i ∈ Store.voters state | i ∈ ({i | i.toUInt64 ∈ J} : Set ℕ)} ≤
      score.toNat + missing := by
    rw [show {i ∈ Store.voters state | i ∈ ({i | i.toUInt64 ∈ J} : Set ℕ)} =
      {i ∈ Store.voters state | i.toUInt64 ∈ J} from rfl, honest]
    rw [← Store.stake_supportersOf within scoreOk]
    -- Every honest index either contributed a supporting duty or is counted as missing.
    change (∑ v ∈ V.filter (· ∈ J), balanceAt state v.toNat) ≤ _
    have split := Finset.sum_filter_add_sum_filter_not (V.filter (· ∈ J)) duty
      (fun v => balanceAt state v.toNat)
    rw [← split]
    apply Nat.add_le_add
    · apply Finset.sum_le_sum_of_subset
      intro v member
      obtain ⟨inside, dutied⟩ := Finset.mem_filter.mp member
      obtain ⟨inside, honest⟩ := Finset.mem_filter.mp inside
      exact supported v inside honest dutied
    · exact Nat.le_of_eq (by simp [missing, stake, Finset.filter_filter])
  exact Store.isAncestor_getHead_of_missing_weight lower before stateOk tree viable scoreOk
    bound support half (by simpa only [total] using margin) headOk

/-- Step 8, the walk: a block that the rule confirms after a safe start is safe up to a last time.

The caller is an honest validator whose store is up to date at the start of a slot.

Its rule passed the checks of step 6 from a start to the block, along a confirmed walk.

The block is a root of the walk from the start to the head of the caller.

That block and each root before it in the walk are one-confirmed.

The start is safe from the call to the last time.

A historical anchor below the start is safe from the start of the current epoch to the call.

The facts that step 6 reads off earlier calls are given as in `coveredOrViableAt_of_checked`.

While no complete epoch lies between the call and a time, `WeightBounds` bounds the shift.

Once one does, a receiver whose justified block does not cover the block has `LateMargin`.

A receiver whose justified block covers the block needs no majority.

No honest store holds a block at the parent root of the anchor block, up to the last time.

This is an explicit exclusion of stores that hold that root, not an assumption on hashes.

With it, each honest store has its parents below its blocks, by `Reachable.parentsBelow`.

The filtered tree and the head need that order.

The proof is a strong induction on the time, and at each time an induction along the walk.

At each time, step 6 gives the block in the filtered tree, or below the justified block.

The finalized-chain premise of each receiver follows by `Execution.rootFinal_or_justified_covers`.

Before a complete epoch lies in the range, the initial phase keeps the block on the head chain.

It uses `Execution.honest_support_of_historical_anchor` and `HeadFollowsSupport`.

In that phase the epoch of a receiver is at most two epochs after that of the parent of a member.

The parent is of the epoch of the start or later, and the start is of the epoch before or later.

`HeadFollowsSupport` asks that each counted voter of a sibling be a member of the window.

`Execution.mem_activeMembers_of_sibling_vote` gives that containment.

The transport also needs `unslashed`, so that an honest member of the window can support the block.

After one does, the late phase keeps it there.

It uses `Execution.mem_supportersOf_of_duty_epoch` and `Store.isAncestor_getHead_of_missing_weight`.

A theorem of [verified-fast-confirmation][vfc] gives the same result.

It is `safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_of_walk {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
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
    (targetVotes : ∀ slot, ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false → HonestTargetVotes e margin u n head.root)
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
    (weights : ∀ last, last ≤ limit →
      ¬CompleteEpochWithin preset config genesisTimeMs (e.world n).time last →
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
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ ≠ .ok true →
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
        2 * total.toNat)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root := by
  sorry

/-- What the induction of Theorem 1 keeps on the block that a call at the event `n` stores.

The block is safe from the start of the slot after the call to the last time.

A block of the current epoch or the one before has a historical anchor.

That anchor is on its chain, of the current epoch or the one before.

It is safe from the start of the current epoch to the last time.

A block of the current epoch extends an origin whose target the rule checked.

That is the record of `TargetChecked`.

The origin is safe from that check to the last time, not only to the call.

The first fact is `ConfirmedSafeFromFollowingSlot` in [verified-fast-confirmation][vfc].

The third is `AcceptedHistoricalA32CurrentLineageAt` there.

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

/-- The call's committee bounds count honest targets without assuming honest equivocation. -/
private theorem Execution.call_targetVotes {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (sound : Invariant anchorState)
    (slots : 0 < config.SLOT_DURATION_MS) (committees : CommitteesFollow e)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {head : ForkChoiceNode} {slot : Slot}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {margin : ℕ}
    (byzantine : ∀ state epochStart lastSlot participants,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
      subChecked slot 1 = .ok lastSlot →
      ((e.world n).state u).getCommitteesBetweenSlots head.root epochStart lastSlot =
        .ok participants →
      ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
        (Store.activeMembers state participants) J
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (remaining : ∀ state epochStart lastSlot participants total soFar,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
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
          {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∉ participants ∧ v ∈ J}) :
    HonestTargetVotes e margin u n head.root := by
  have reached := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) n u caller
  -- The anchor has no equivocators, and honest signatures never add one.
  have empty : anchor.equivocatingIndices = [] := by
    unfold getForkchoiceStore at anchored
    simp only [bind_ok_iff] at anchored
    obtain ⟨_, _, anchored⟩ := anchored
    split at anchored
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at anchored
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at anchored
      obtain ⟨_, _, _, _, rfl⟩ := anchored
      rfl
  have dishonest : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J := by
    intro v member honest
    exact e.not_mem_equivocatingIndices slots (fun w hw => (start w hw) ▸ empty)
      caller honest n member
  intro state support target readSlot epochStart lastSlot participants stateOk supportOk
    targetOk readSlotOk startOk lastOk participantsOk
  have sameSlot : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
  subst readSlot
  -- A successful support read supplies the total and elapsed committee weight.
  have reads := supportOk
  unfold Store.computeHonestFfgSupportForCurrentTarget at reads
  simp only [bind_ok_iff, mapError_ok_iff, slotOk, stateOk, startOk, lastOk, Except.ok.injEq,
    exists_eq_left'] at reads
  obtain ⟨total, totalOk, score, scoreOk, soFar, soFarOk, rest⟩ := reads
  have counted := e.honestTargetVotes_of_byzantineStakeAtMost anchored start committees retained
    caller
    ⟨head, headOk, rfl⟩ slotOk stateOk totalOk
    (reached.getPulledUpHeadState_aligned sound maxAligned stateOk) increment startOk lastOk
    soFarOk participantsOk (byzantine _ _ _ _ stateOk startOk lastOk participantsOk) dishonest
    (remaining _ _ _ _ _ _ stateOk startOk lastOk participantsOk totalOk soFarOk)
  exact counted state support target slot epochStart lastSlot participants stateOk supportOk
    targetOk slotOk startOk lastOk participantsOk

omit [DecidablePred (· ∈ J)] in
/-- A noninitial call consumes exactly the output of the call before it. -/
private theorem callAt_previous {u : ValidatorIndex} {events : List ℕ}
    {first fcr after : FastConfirmationStore} {i n : ℕ}
    (calls : CallAt e u events first (i + 1) n fcr after) :
    ∃ previous before, CallAt e u events first i previous before fcr := by
  have index : i < events.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp calls.1
    omega
  have previousOk : events[i]? = some events[i] := List.getElem?_eq_getElem index
  have ran := calls.2.1
  rw [List.take_add_one, previousOk] at ran
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
    List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_right] at ran
  obtain ⟨before, ranBefore, step⟩ := ran
  exact ⟨events[i], before, previousOk, ranBefore, step⟩

omit [DecidablePred (· ∈ J)] in
/-- Consecutive slot-start calls occur in increasing event order. -/
private theorem call_slots_order {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {m n : ℕ} {previous slot : Slot} {before begin : UInt64}
    (successor : slot.toNat = previous.toNat + 1)
    (beforeOk : computeTimeAtSlotMs config genesisTimeMs previous = .ok before)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atBefore : (e.world m).time = before.toNat)
    (atSlot : (e.world n).time = begin.toNat) :
    addChecked previous 1 = .ok slot ∧ m < n ∧ (e.world m).time + Δ < (e.world n).time := by
  have nextOk : addChecked previous 1 = .ok slot := addChecked_ok_iff.mpr ⟨by
    have := slot.toNat_lt
    simpa only [UInt64.toNat_one, ← successor] using this, by simpa using successor⟩
  have late := fits.call_before_next_slot nextOk beforeOk beginOk atBefore
    (by omega : begin.toNat ≤ (e.world n).time)
  refine ⟨nextOk, ?_, late⟩
  by_contra notBefore
  have backwards : (e.world n).time ≤ (e.world m).time :=
    e.monotone_time (Nat.le_of_not_gt notBefore)
  omega

omit [DecidablePred (· ∈ J)] in
/-- A representable slot start supplies the start time of its epoch. -/
private theorem call_epoch_start {slot : Slot} {begin : UInt64}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin) :
    ∃ epochStart epochStartTime,
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart ∧
      computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime := by
  have boundary := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
  have le := (computeStartSlotAtEpoch_le_lt positive boundary).1
  obtain ⟨time, timeOk, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_iff_toNat_le.mpr le) beginOk
  exact ⟨_, time, boundary, timeOk⟩

omit [DecidablePred (· ∈ J)] in
/-- The anchor root satisfies all three call-history clauses. -/
private theorem Execution.callInvariant_anchor {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    (positive : 0 < preset.SLOTS_PER_EPOCH) {u : ValidatorIndex} (caller : u ∈ J)
    {n : ℕ} {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    {margin limit : ℕ} :
    CallInvariant e margin limit anchor.finalizedCheckpoint.root u n
      anchor.finalizedCheckpoint.root := by
  have safe := e.safeAt_anchor anchored start
  have self {epoch : Epoch}
      (rootOk : ((e.world n).state u).getBlockEpoch anchor.finalizedCheckpoint.root = .ok epoch) :
      ((e.world n).state u).isAncestor ⟨anchor.finalizedCheckpoint.root, .pending⟩
        ⟨anchor.finalizedCheckpoint.root, .pending⟩ = .ok true := by
    unfold Store.getBlockEpoch at rootOk
    obtain ⟨block, found, _⟩ := bind_ok_iff.mp rootOk
    exact e.isAncestor_anchor_of_known anchored start caller (Store.block_ok_iff.mp found)
  refine ⟨fun _ _ _ _ _ _ time _ _ => safe time, ?_, ?_⟩
  · intro epoch rootEpoch epochOk rootOk recent
    have epochEq : epoch = computeEpochAtSlot preset slot := by
      simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
        using epochOk.symm
    obtain ⟨epochStart, time, boundary, timeOk⟩ := call_epoch_start positive beginOk
    refine ⟨anchor.finalizedCheckpoint.root, rootEpoch, epochStart, time,
      self rootOk, rootOk, recent, ?_, timeOk, fun t _ _ => safe t⟩
    simpa only [epochEq] using boundary
  · intro epoch _ rootOk
    exact ⟨n, le_rfl, anchor.finalizedCheckpoint.root, rootOk, self rootOk,
      Or.inl rfl, fun t _ _ => safe t⟩

omit [DecidablePred (· ∈ J)] in
/-- A reset to a nonanchor finalized block has no recent-history obligations. -/
private theorem callInvariant_old_finalized {u : ValidatorIndex} {n : ℕ}
    {anchorRoot root : Root} {margin limit Δ : ℕ} {slot : Slot} {begin : UInt64}
    (fits : DelayFits fork config genesisTimeMs Δ)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    (safe : ∀ time, (e.world n).time + Δ ≤ time → time ≤ limit → SafeAt e time root)
    (old : ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ∃ rootEpoch, ((e.world n).state u).getBlockEpoch root = .ok rootEpoch ∧
        rootEpoch.toNat + 2 ≤ epoch.toNat) :
    CallInvariant e margin limit anchorRoot u n root := by
  refine ⟨?_, ?_, ?_⟩
  · intro readSlot next following readSlotOk nextOk followingOk time afterNext bounded
    have same : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
    subst readSlot
    exact safe time (Nat.le_of_lt
      (fits.call_before_next_slot nextOk beginOk followingOk atSlot afterNext)) bounded
  · intro epoch rootEpoch epochOk rootOk recent
    obtain ⟨other, otherOk, age⟩ := old epoch epochOk
    have same : other = rootEpoch := Except.ok.inj (otherOk.symm.trans rootOk)
    subst other
    omega
  · intro epoch epochOk rootOk
    obtain ⟨other, otherOk, age⟩ := old epoch epochOk
    have same : other = epoch := Except.ok.inj (otherOk.symm.trans rootOk)
    subst other
    omega

omit [DecidablePred (· ∈ J)] in
/-- Within one epoch, a carried root keeps its historical anchor and target origin. -/
private theorem Execution.callInvariant_carried_inside
    {u : ValidatorIndex} {m n : ℕ} {root anchorRoot : Root} {margin limit : ℕ}
    (later : m ≤ n) (previous : CallInvariant e margin limit anchorRoot u m root)
    (sameEpoch : ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world m).state u).getCurrentStoreEpoch config = .ok epoch)
    (knownBefore : ∃ epoch, ((e.world m).state u).getBlockEpoch root = .ok epoch)
    (safe : ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root)
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat) :
    CallInvariant e margin limit anchorRoot u n root := by
  have readBefore {epoch : Epoch}
      (read : ((e.world n).state u).getBlockEpoch root = .ok epoch) :
      ((e.world m).state u).getBlockEpoch root = .ok epoch := by
    obtain ⟨old, oldOk⟩ := knownBefore
    have same : old = epoch := Except.ok.inj ((e.getBlockEpoch_of_le later oldOk).symm.trans read)
    exact same ▸ oldOk
  refine ⟨?_, ?_, ?_⟩
  · intro readSlot next following readSlotOk nextOk followingOk time afterNext bounded
    have same : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
    subst readSlot
    have late := fits.call_before_next_slot nextOk beginOk followingOk atSlot afterNext
    exact safe time (by omega) bounded
  · intro epoch rootEpoch epochOk rootOk recent
    obtain ⟨historical, historicalEpoch, epochStart, time, below, historicalOk,
      age, boundary, timeOk, historicalSafe⟩ :=
      previous.2.1 epoch rootEpoch (sameEpoch epoch epochOk) (readBefore rootOk) recent
    exact ⟨historical, historicalEpoch, epochStart, time,
      e.isAncestor_of_le later below, e.getBlockEpoch_of_le later historicalOk,
      age, boundary, timeOk, historicalSafe⟩
  · intro epoch epochOk rootOk
    obtain ⟨k, before, origin, originOk, below, checked, originSafe⟩ :=
      previous.2.2 epoch (sameEpoch epoch epochOk) (readBefore rootOk)
    exact ⟨k, before.trans later, origin, e.getBlockEpoch_of_le later originOk,
      e.isAncestor_of_le later below, checked, originSafe⟩

omit [DecidablePred (· ∈ J)] in
/-- At an epoch boundary an older safe root is its own historical anchor. -/
private theorem callInvariant_boundary {u : ValidatorIndex} {n : ℕ}
    {root anchorRoot : Root} {margin limit : ℕ} {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (boundary : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok slot)
    (atSlot : (e.world n).time = begin.toNat)
    (safe : ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root)
    (old : ((e.world n).state u).getBlockEpoch root ≠ .ok (computeEpochAtSlot preset slot))
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ) :
    CallInvariant e margin limit anchorRoot u n root := by
  have epochSame {epoch : Epoch}
      (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
      epoch = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
      using epochOk.symm
  refine ⟨?_, ?_, ?_⟩
  · intro readSlot next following readSlotOk nextOk followingOk time afterNext bounded
    have same : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
    subst readSlot
    have late := fits.call_before_next_slot nextOk beginOk followingOk atSlot afterNext
    exact safe time (by omega) bounded
  · intro epoch rootEpoch epochOk rootOk recent
    have known := rootOk
    unfold Store.getBlockEpoch at known
    obtain ⟨block, found, _⟩ := bind_ok_iff.mp known
    refine ⟨root, rootEpoch, slot, begin,
      Store.isAncestor_self (Store.block_ok_iff.mp found), rootOk, recent,
      (epochSame epochOk) ▸ boundary, beginOk, ?_⟩
    intro time afterBegin bounded
    exact safe time (atSlot ▸ afterBegin) bounded
  · intro epoch epochOk rootOk
    exact False.elim (old ((epochSame epochOk) ▸ rootOk))

omit [DecidablePred (· ∈ J)] in
/-- A successful epoch-start test identifies the rounded boundary with the slot. -/
private theorem call_boundary_eq {slot : Slot}
    (atStart : isStartSlotAtEpoch preset slot = .ok true) :
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok slot := by
  have boundary := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
  unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at atStart
  rw [boundary] at atStart
  simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, decide_eq_true_eq] at atStart
  have h := (computeStartSlotAtEpoch_ok_iff.mp boundary).2
  have le : (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat ≤ slot.toNat := by
    rw [h, computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  have zero := congrArg UInt64.toNat atStart
  simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
  have upper := slot.toNat_lt
  have lower := (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
  have same : slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH = slot := by
    apply UInt64.toNat_inj.mp
    omega
  exact boundary.trans (congrArg Except.ok same)

omit [DecidablePred (· ∈ J)] in
/-- A successful call returns a known block, including when it resets without walking. -/
private theorem Execution.call_root_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state u).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (lower : ((e.world n).state u).ParentsBelow)
    {fcr after : FastConfirmationStore}
    (called : ((e.world n).state u).onFastConfirmation config fcr = .ok after) :
    ∃ epoch, ((e.world n).state u).getBlockEpoch after.confirmedRoot = .ok epoch := by
  have ofBlock {root : Root} {block : BeaconBlock preset fork}
      (found : ((e.world n).state u).block root = .ok block) :
      ∃ epoch, ((e.world n).state u).getBlockEpoch root = .ok epoch := by
    exact ⟨computeEpochAtSlot preset block.slot, by
      simp [Store.getBlockEpoch, found, bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨head, slot, root, headOk, slotOk, _, _, _, _, _, _, selected, result⟩ :=
    Store.onFastConfirmation_checked lower called
  rcases result with same | ⟨_, checked, _⟩
  · rw [same]
    obtain ⟨base, baseCase, selected⟩ := selected
    rcases selected with ⟨rfl, _⟩ | ⟨rfl, _, ⟨block, _, found, _⟩, _⟩
    · rcases baseCase with ⟨rfl, ⟨epoch, blockEpoch, _, known, _⟩, _⟩ | ⟨rfl, _⟩
      · exact ⟨blockEpoch, known⟩
      · have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
            .ok (computeEpochAtSlot preset slot) := by
          simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
        rcases e.finalizedCheckpoint_eq_or_blockEpoch_add_two_le positive window anchored sound
          caller (start u caller) nonzero epochOk with same | ⟨epoch, known, _⟩
        · obtain ⟨anchorRoot, _, known, _, _, final, _⟩ := getForkchoiceStore_anchor anchored
          have known : ((e.world n).state u).blocks[anchorRoot]? = some anchorBlock :=
            e.blocks_of_le (Nat.zero_le n) (by
              change (e.start u).blocks[anchorRoot]? = some anchorBlock
              simpa only [start u caller] using known)
          rw [same, final]
          exact ofBlock (Store.block_ok_iff.mpr known)
        · exact ⟨epoch, known⟩
    · exact ofBlock found
  · obtain ⟨_, _, epoch, _, _, _, known, _⟩ := checked
    exact ⟨epoch, known⟩

omit [DecidablePred (· ∈ J)] in
/-- The epoch-start test is total, and is false exactly away from the rounded boundary. -/
private theorem call_not_boundary {slot : Slot}
    (notStart : ¬ isStartSlotAtEpoch preset slot = .ok true) :
    isStartSlotAtEpoch preset slot = .ok false := by
  simp only [isStartSlotAtEpoch, computeSlotsSinceEpochStart,
    computeStartSlotAtEpoch_computeEpochAtSlot, Except.mapError, bind, Except.bind,
    pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] at notStart ⊢
  simp [notStart]

omit [DecidablePred (· ∈ J)] in
/-- A slot immediately before an epoch boundary is not itself a boundary. -/
private theorem call_previous_not_boundary {slot previous : Slot}
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (nextOk : addChecked previous 1 = .ok slot)
    (boundary : isStartSlotAtEpoch preset slot = .ok true) :
    isStartSlotAtEpoch preset previous = .ok false := by
  apply call_not_boundary
  intro oldBoundary
  have now := (computeStartSlotAtEpoch_ok_iff.mp (call_boundary_eq boundary)).2
  have old := (computeStartSlotAtEpoch_ok_iff.mp (call_boundary_eq oldBoundary)).2
  have sum := (addChecked_ok_iff.mp nextOk).2
  have longNat := UInt64.lt_iff_toNat_lt.mp long
  have dividesNow : preset.SLOTS_PER_EPOCH.toNat ∣ slot.toNat := by rw [now]; exact dvd_mul_left _ _
  have dividesOld : preset.SLOTS_PER_EPOCH.toNat ∣ previous.toNat := by rw [old]; exact dvd_mul_left _ _
  have dividesOne := Nat.dvd_sub dividesNow dividesOld
  have diff : slot.toNat - previous.toNat = 1 := by
    simpa using congrArg (fun x => x - previous.toNat) sum
  rw [diff] at dividesOne
  have := Nat.le_of_dvd (by decide : 0 < 1) dividesOne
  norm_num at longNat
  omega

/-- Step 8, one call: the block that a call stores keeps `CallInvariant`.

Each earlier call of the run keeps it, which is the induction hypothesis.

The proof splits the call with `Store.onFastConfirmation_checked`.

A start that the call carries is the block stored before, at the slot before.

Its safety from this call on and its historical anchor come from the call before.

At the start of an epoch, the start itself is the historical anchor.

A finalized start with a confirmed walk is the block of the anchor.

`Execution.finalizedCheckpoint_eq_of_checked` gives that.

A finalized start without a walk is safe one delay after the call, by `Execution.safeAt_finalized`.

It is the block of the anchor or is two epochs old, so it needs no historical anchor.

`Execution.finalizedCheckpoint_eq_or_blockEpoch_add_two_le` gives that.

An observed start is safe from the call, by `Execution.safeAt_observed`.

The call before recorded it one slot before, and the first call reads the block of the anchor.

A walk gives a block safe from the call, by `Execution.safeAt_of_walk`.

Its inputs come from the induction hypothesis and from the one field of `RuleBounds`.

That field reads the walk with its selected start from `Store.onFastConfirmation_checked`.

A call that returns its start unchanged reads no bound.

`Execution.honestTargetVotes_of_byzantineStakeAtMost` gives the honest target votes.

`Execution.honestThirdPins` and `Execution.justifiedByHonestVote` give the FFG inputs.

A walked block of the current epoch from a start of the epoch before has its own target check.

This is the successor case of a theorem of [verified-fast-confirmation][vfc].

It is `confirmed_safety_and_lineage_of_acceptedActualFCRFold`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.callInvariant_step {Δ : ℕ} (sync : e.Synchronous Δ)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
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
  -- The preset bundle implies the ring bound that the H and N wrappers read.
  have ring :
      preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
    omega
  have positiveSlots : 0 < preset.SLOTS_PER_EPOCH := UInt64.lt_trans (by decide) long
  have positiveSlotsNat := UInt64.lt_iff_toNat_lt.mp positiveSlots
  have member : n ∈ events := List.mem_of_getElem? calls.1
  obtain ⟨slot, begin, slotOk, slotIndex, beginOk, atSlot⟩ := atSlots i n calls.1
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have forward := fun k => e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored) k u caller
  have anchorInvariant := e.callInvariant_anchor anchored start positiveSlots caller slotOk beginOk
    (margin := margin) (limit := limit)
  -- The finalized case is either the anchor or too old to carry historical obligations.
  have finalInvariant : CallInvariant e margin limit anchor.finalizedCheckpoint.root u n
      ((e.world n).state u).finalizedCheckpoint.root := by
    by_cases same : ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint
    · simpa only [same] using anchorInvariant
    apply callInvariant_old_finalized fits slotOk beginOk atSlot
      (e.safeAt_finalized sync positiveSlotsNat window preGloas oneBlock admitted anchored sound
        start chain caller epochOk (fun w hw k _ => nonzero w hw k) inHorizon)
    intro epoch currentOk
    exact (e.finalizedCheckpoint_eq_or_blockEpoch_add_two_le positiveSlotsNat window anchored
      sound caller (start u caller) (nonzero u caller n) currentOk).resolve_left same
  -- Consecutive calls supply the old root's safety from the current slot onward.
  have carriedSafe : ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time fcr.confirmedRoot := by
    cases i with
    | zero =>
      have initial : fcr = getFastConfirmationStore anchor := by
        simpa [pure, Except.pure] using calls.2.1.symm
      subst fcr
      exact fun time _ _ => e.safeAt_anchor anchored start time
    | succ j =>
      obtain ⟨m, before, previous⟩ := callAt_previous calls
      obtain ⟨oldSlot, oldTime, oldSlotOk, oldIndex, oldTimeOk, atOldSlot⟩ :=
        atSlots j m previous.1
      have nextOk := (call_slots_order fits (by omega : slot.toNat = oldSlot.toNat + 1)
        oldTimeOk beginOk atOldSlot atSlot).1
      have inv := earlier j (Nat.lt_succ_self j) m before fcr previous
      intro time afterCall bounded
      exact inv.1 oldSlot slot begin oldSlotOk nextOk beginOk time (by omega) bounded
  have carriedInvariant : CallInvariant e margin limit anchor.finalizedCheckpoint.root u n
      fcr.confirmedRoot := by
    cases i with
    | zero =>
      have initial : fcr = getFastConfirmationStore anchor := by
        simpa [pure, Except.pure] using calls.2.1.symm
      simpa only [initial, getFastConfirmationStore] using anchorInvariant
    | succ j =>
      obtain ⟨m, before, previous⟩ := callAt_previous calls
      obtain ⟨oldSlot, oldTime, oldSlotOk, oldIndex, oldTimeOk, atOldSlot⟩ :=
        atSlots j m previous.1
      have sum : slot.toNat = oldSlot.toNat + 1 := by omega
      obtain ⟨nextOk, eventLt, _⟩ := call_slots_order fits sum oldTimeOk beginOk atOldSlot atSlot
      have inv := earlier j (Nat.lt_succ_self j) m before fcr previous
      have known := e.call_root_known anchored sound start positiveSlotsNat window caller
        (nonzero u caller m) (lower m (List.mem_of_getElem? previous.1)) previous.2.2
      by_cases boundary : isStartSlotAtEpoch preset slot = .ok true
      · have boundaryOk := call_boundary_eq boundary
        apply callInvariant_boundary slotOk beginOk boundaryOk atSlot carriedSafe ?_ fits
        intro rootOk
        obtain ⟨rootEpoch, oldRootOk⟩ := known
        have nowRootOk := e.getBlockEpoch_of_le eventLt.le oldRootOk
        have same : rootEpoch = computeEpochAtSlot preset slot :=
          Except.ok.inj (nowRootOk.symm.trans rootOk)
        unfold Store.getBlockEpoch at oldRootOk
        obtain ⟨block, found, blockEpoch⟩ := bind_ok_iff.mp oldRootOk
        have blockEpoch : computeEpochAtSlot preset block.slot = computeEpochAtSlot preset slot :=
          (Except.ok.inj blockEpoch).trans same
        obtain ⟨current, currentOk, blocks, _⟩ :=
          (forward m).slots_le_current slots (UInt64.le_of_eq anchorSlot)
        have currentEq : current = oldSlot := Except.ok.inj (currentOk.symm.trans oldSlotOk)
        subst current
        have blockLe := UInt64.le_iff_toNat_le.mp
          (blocks _ _ (Store.block_ok_iff.mp found))
        have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
        have blockEpochNat := congrArg UInt64.toNat blockEpoch
        simp only [computeEpochAtSlot, UInt64.toNat_div] at blockEpochNat boundaryNat
        have blockLower := Nat.div_mul_le_self block.slot.toNat preset.SLOTS_PER_EPOCH.toNat
        rw [blockEpochNat] at blockLower
        omega
      · apply e.callInvariant_carried_inside eventLt.le inv ?_ known carriedSafe fits
          slotOk beginOk atSlot
        intro epoch currentOk
        have notMod : ¬ slot % preset.SLOTS_PER_EPOCH = 0 := by
          intro modZero
          apply boundary
          have rounded : slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH = slot := by
            apply UInt64.toNat_inj.mp
            have h := (computeStartSlotAtEpoch_ok_iff.mp
              (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot)).2
            have modNat := congrArg UInt64.toNat modZero
            simp only [UInt64.toNat_mod, UInt64.toNat_zero] at modNat
            rw [h, computeEpochAtSlot, UInt64.toNat_div]
            exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero modNat)
          simp [isStartSlotAtEpoch, computeSlotsSinceEpochStart,
            computeStartSlotAtEpoch_computeEpochAtSlot, rounded, Except.mapError,
            bind, Except.bind, pure, Except.pure]
        have sameEpoch : computeEpochAtSlot preset slot = computeEpochAtSlot preset oldSlot := by
          apply UInt64.toNat_inj.mp
          exact nextSlot_epoch_of_inside sum notMod
        have epochSame : epoch = computeEpochAtSlot preset slot :=
          Except.ok.inj (currentOk.symm.trans epochOk)
        simp [Store.getCurrentStoreEpoch, oldSlotOk, epochSame, sameEpoch,
          bind, Except.bind, pure, Except.pure]
  have voted := e.justifiedByHonestVote anchored sound positiveSlotsNat window ring preGloas
    nonzero start (fun w hw k state counts _ upper => large w hw k state counts upper)
    byzantine positive enough
  obtain ⟨head, readSlot, selectedStart, headOk, readSlotOk, previousHeadEq, currentHeadEq,
    recordedNext, keptNext, atBoundary, insideEpoch, selection, result⟩ :=
    Store.onFastConfirmation_checked (lower n member) calls.2.2
  have sameSlot : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
  subst readSlot
  have observedSafe (boundary : isStartSlotAtEpoch preset slot = .ok true)
      {observedBlock : BeaconBlock preset fork}
      (found : ((e.world n).state u).block after.currentEpochObservedJustifiedCheckpoint.root =
        .ok observedBlock)
      (age : addChecked (computeEpochAtSlot preset observedBlock.slot) 1 =
        .ok (computeEpochAtSlot preset slot)) :
      ∀ time, (e.world n).time ≤ time → time ≤ limit →
        SafeAt e time after.currentEpochObservedJustifiedCheckpoint.root := by
    have boundaryOk := call_boundary_eq boundary
    have nextInside {next : Slot} (nextOk : addChecked slot 1 = .ok next) :
        isStartSlotAtEpoch preset next = .ok false := by
      apply call_not_boundary
      intro nextBoundary
      have previousFalse := call_previous_not_boundary long nextOk nextBoundary
      rw [boundary] at previousFalse
      cases Except.ok.inj previousFalse
    have hasNext : ∃ next, addChecked slot 1 = .ok next := by
      have run := calls.2.2
      unfold Store.onFastConfirmation at run
      simp only [bind_ok_iff] at run
      obtain ⟨_, _, updated, updatedOk, _⟩ := run
      unfold Store.updateFastConfirmationVariables at updatedOk
      simp only [bind_ok_iff] at updatedOk
      obtain ⟨s, sOk, next, nextOk, _⟩ := updatedOk
      have same : s = slot := Except.ok.inj (sOk.symm.trans slotOk)
      exact ⟨next, same ▸ mapError_ok_iff.mp nextOk⟩
    obtain ⟨next, nextOk⟩ := hasNext
    have observedEq : after.currentEpochObservedJustifiedCheckpoint =
        fcr.previousEpochGreatestUnrealizedCheckpoint :=
      (atBoundary boundary).1.trans (keptNext next nextOk (nextInside nextOk))
    cases i with
    | zero =>
      have initial : fcr = getFastConfirmationStore anchor := by
        simpa [pure, Except.pure] using calls.2.1.symm
      rw [observedEq, initial]
      exact fun time _ _ => e.safeAt_anchor anchored start time
    | succ j =>
      obtain ⟨m, before, previous⟩ := callAt_previous calls
      obtain ⟨oldSlot, oldTime, oldSlotOk, oldIndex, oldTimeOk, atOldSlot⟩ :=
        atSlots j m previous.1
      have sum : slot.toNat = oldSlot.toNat + 1 := by omega
      obtain ⟨nextOk', eventLt, delayed⟩ := call_slots_order fits sum oldTimeOk beginOk atOldSlot atSlot
      obtain ⟨_, s, _, _, sOk, _, _, recorded, _⟩ :=
        Store.onFastConfirmation_checked (lower m (List.mem_of_getElem? previous.1)) previous.2.2
      have same : s = oldSlot := Except.ok.inj (sOk.symm.trans oldSlotOk)
      subst s
      have recordedEq := recorded slot nextOk' boundary
      rw [recordedEq] at observedEq
      have oldEpochOk : ((e.world m).state u).getCurrentStoreEpoch config =
          .ok (computeEpochAtSlot preset oldSlot) := by
        simp [Store.getCurrentStoreEpoch, oldSlotOk, bind, Except.bind, pure, Except.pure]
      have epochNext : addChecked (computeEpochAtSlot preset oldSlot) 1 =
          .ok (computeEpochAtSlot preset slot) := by
        have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
        have modZero : slot % preset.SLOTS_PER_EPOCH = 0 := by
          apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_mod, UInt64.toNat_zero]
          rw [boundaryNat]
          exact Nat.mul_mod_left _ _
        have nextEpoch := nextSlot_epoch_of_boundary sum modZero
        apply addChecked_ok_iff.mpr
        constructor
        · have := (computeEpochAtSlot preset slot).toNat_lt
          simpa only [computeEpochAtSlot, UInt64.toNat_div, UInt64.toNat_one, nextEpoch] using this
        · simpa only [computeEpochAtSlot, UInt64.toNat_div, UInt64.toNat_one] using nextEpoch
      rw [observedEq] at found ⊢
      exact e.safeAt_observed sync positiveSlotsNat window slots votes fits prompt preGloas
        oneBlock admitted anchored sound start chain unique voted caller delayed.le oldEpochOk
        epochOk epochNext slotOk boundary beginOk atSlot found age
        (fun w hw k _ => nonzero w hw k) inHorizon
  have observedInvariant (boundary : isStartSlotAtEpoch preset slot = .ok true)
      {observedBlock : BeaconBlock preset fork}
      (found : ((e.world n).state u).block after.currentEpochObservedJustifiedCheckpoint.root =
        .ok observedBlock)
      (age : addChecked (computeEpochAtSlot preset observedBlock.slot) 1 =
        .ok (computeEpochAtSlot preset slot)) :
      CallInvariant e margin limit anchor.finalizedCheckpoint.root u n
        after.currentEpochObservedJustifiedCheckpoint.root := by
    apply callInvariant_boundary slotOk beginOk (call_boundary_eq boundary) atSlot
      (observedSafe boundary found age) ?_ fits
    intro rootEpoch
    have same : computeEpochAtSlot preset observedBlock.slot = computeEpochAtSlot preset slot := by
      simpa [Store.getBlockEpoch, found, bind, Except.bind, pure, Except.pure] using rootEpoch
    have sum := (addChecked_ok_iff.mp age).2
    rw [same] at sum
    norm_num at sum
  rcases result with same | ⟨strict, checked, balanceSource, walk, later, sourceOk,
    walked, confirmedAll⟩
  · rw [same]
    obtain ⟨base, baseCase, selected⟩ := selection
    rcases selected with ⟨rfl, _⟩ | ⟨rfl, boundary, ⟨block, epoch, found, currentOk, age⟩, _⟩
    · rcases baseCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact carriedInvariant
      · exact finalInvariant
    · have sameEpoch : epoch = computeEpochAtSlot preset slot :=
        Except.ok.inj (currentOk.symm.trans epochOk)
      exact observedInvariant boundary found (sameEpoch ▸ age)
  -- Only a strict walk from the selected start consumes the rule bounds.
  obtain ⟨weights, slack, committeeByzantine, remaining, late⟩ := bounds.walked i n fcr after
    head slot selectedStart balanceSource walk later calls headOk slotOk selection strict
    checked sourceOk walked confirmedAll
  have targetVotes : ∀ s, ((e.world n).state u).getCurrentSlot config = .ok s →
      isStartSlotAtEpoch preset s = .ok false → HonestTargetVotes e margin u n head.root := by
    intro s sOk inside
    have same : s = slot := Except.ok.inj (sOk.symm.trans slotOk)
    subst s
    exact e.call_targetVotes anchored start sound slots committees (by omega) maxAligned increment
      caller
      headOk slotOk (fun state first last participants => committeeByzantine state first last
        participants inside) (fun state first last participants total soFar =>
        remaining state first last participants total soFar inside)
  have startFacts : CallInvariant e margin limit anchor.finalizedCheckpoint.root u n selectedStart ∧
      (∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time selectedStart) := by
    obtain ⟨base, baseCase, selected⟩ := selection
    rcases selected with ⟨rfl, _⟩ | ⟨rfl, boundary, ⟨block, epoch, found, currentOk, age⟩, _⟩
    · rcases baseCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact ⟨carriedInvariant, carriedSafe⟩
      · have same := e.finalizedCheckpoint_eq_of_checked positiveSlotsNat window anchored sound
          caller (start u caller) (nonzero u caller n) checked
        rw [same]
        exact ⟨anchorInvariant, fun time _ _ => e.safeAt_anchor anchored start time⟩
    · have sameEpoch : epoch = computeEpochAtSlot preset slot :=
        Except.ok.inj (currentOk.symm.trans epochOk)
      exact ⟨observedInvariant boundary found (sameEpoch ▸ age),
        observedSafe boundary found (sameEpoch ▸ age)⟩
  obtain ⟨checkedEpoch, checkedSlot, rootEpoch, startEpoch, checkedEpochOk, checkedSlotOk,
    rootEpochOk, startEpochOk, recent, checkedCases⟩ := checked
  have epochSame : checkedEpoch = computeEpochAtSlot preset slot :=
    Except.ok.inj (checkedEpochOk.symm.trans epochOk)
  subst checkedEpoch
  have slotSame : checkedSlot = slot := Except.ok.inj (checkedSlotOk.symm.trans slotOk)
  subst checkedSlot
  obtain ⟨historical, historicalEpoch, epochStart, epochStartTime, startBelow, historicalOk,
    historicalRecent, epochStartOk, epochStartTimeOk, historicalSafe⟩ :=
    startFacts.1.2.1 _ _ epochOk startEpochOk recent
  have previousHead : after.previousSlotHead = anchor.finalizedCheckpoint.root ∨
      ∃ k < n, ∃ previous previousSlot,
        UpToDate config checks sources (e.world k).time ((e.world k).view u) ((e.world k).state u) ∧
        ((e.world k).state u).getHead config = .ok previous ∧
        previous.root = after.previousSlotHead ∧
        ((e.world k).state u).getCurrentSlot config = .ok previousSlot ∧
        addChecked previousSlot 1 = .ok slot := by
    rw [previousHeadEq]
    cases i with
    | zero =>
      have initial : fcr = getFastConfirmationStore anchor := by
        simpa [pure, Except.pure] using calls.2.1.symm
      exact Or.inl (by simp [initial, getFastConfirmationStore])
    | succ j =>
      obtain ⟨m, before, previous⟩ := callAt_previous calls
      have prevMem := List.mem_of_getElem? previous.1
      obtain ⟨oldSlot, oldTime, oldSlotOk, oldIndex, oldTimeOk, atOldSlot⟩ := atSlots j m previous.1
      obtain ⟨nextOk, eventLt, _⟩ := call_slots_order fits (by omega) oldTimeOk beginOk atOldSlot atSlot
      obtain ⟨oldHead, _, _, oldHeadOk, _, _, oldHeadEq, _⟩ :=
        Store.onFastConfirmation_checked (lower m prevMem) previous.2.2
      exact Or.inr ⟨m, eventLt, oldHead, oldSlot, upToDate m prevMem, oldHeadOk,
        oldHeadEq.symm, oldSlotOk, nextOk⟩
  have boundedLineage (bounded : (e.world n).time ≤ limit) :
      ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
        ((e.world n).state u).getBlockEpoch selectedStart = .ok epoch →
        TargetChecked e margin anchor.finalizedCheckpoint.root u n epoch selectedStart := by
    intro epoch currentOk rootOk
    obtain ⟨k, before, origin, originOk, below, checked, safe⟩ :=
      startFacts.1.2.2 epoch currentOk rootOk
    exact ⟨k, before, origin, rootOk, originOk, below, checked,
      fun time lower upper => safe time lower (upper.trans bounded)⟩
  have previousLineage (bounded : (e.world n).time ≤ limit) :
      ∀ epoch previous, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
        isStartSlotAtEpoch preset slot = .ok true → addChecked previous 1 = .ok epoch →
        ((e.world n).state u).getBlockEpoch selectedStart = .ok previous →
        TargetChecked e margin anchor.finalizedCheckpoint.root u n previous selectedStart ∨
          (((e.world n).state u).unrealizedJustification head.root =
            .ok after.currentEpochObservedJustifiedCheckpoint ∧
            selectedStart = after.currentEpochObservedJustifiedCheckpoint.root) := by
    intro epoch previous currentOk boundary previousNext rootOk
    obtain ⟨base, baseCase, selected⟩ := selection
    rcases selected with ⟨rfl, _⟩ | ⟨rfl, _, _, justification, _⟩
    · rcases baseCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · left
        cases i with
        | zero =>
          have initial : fcr = getFastConfirmationStore anchor := by
            simpa [pure, Except.pure] using calls.2.1.symm
          have rootEq : fcr.confirmedRoot = anchor.finalizedCheckpoint.root := by
            simp [initial, getFastConfirmationStore]
          have known := rootOk
          unfold Store.getBlockEpoch at known
          obtain ⟨block, found, _⟩ := bind_ok_iff.mp known
          exact ⟨n, le_rfl, fcr.confirmedRoot, rootOk, rootOk,
            Store.isAncestor_self (Store.block_ok_iff.mp found), Or.inl rootEq,
            fun time _ _ => rootEq ▸ e.safeAt_anchor anchored start time⟩
        | succ j =>
          obtain ⟨m, before, previousCall⟩ := callAt_previous calls
          obtain ⟨oldSlot, oldTime, oldSlotOk, oldIndex, oldTimeOk, atOldSlot⟩ :=
            atSlots j m previousCall.1
          have sum : slot.toNat = oldSlot.toNat + 1 := by omega
          obtain ⟨_, eventLt, _⟩ := call_slots_order fits sum oldTimeOk beginOk atOldSlot atSlot
          have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp (call_boundary_eq boundary)).2
          have modZero : slot % preset.SLOTS_PER_EPOCH = 0 := by
            apply UInt64.toNat_inj.mp
            simp only [UInt64.toNat_mod, UInt64.toNat_zero]
            rw [boundaryNat]
            exact Nat.mul_mod_left _ _
          have epochStep := nextSlot_epoch_of_boundary sum modZero
          have epochSame : epoch = computeEpochAtSlot preset slot :=
            Except.ok.inj (currentOk.symm.trans epochOk)
          have previousSame : previous = computeEpochAtSlot preset oldSlot := by
            have previousNat := (addChecked_ok_iff.mp previousNext).2
            rw [epochSame] at previousNat
            simp only [computeEpochAtSlot, UInt64.toNat_div, UInt64.toNat_one] at previousNat
            apply UInt64.toNat_inj.mp
            simp only [computeEpochAtSlot, UInt64.toNat_div]
            omega
          have oldEpochOk : ((e.world m).state u).getCurrentStoreEpoch config = .ok previous := by
            simp [Store.getCurrentStoreEpoch, oldSlotOk, previousSame,
              bind, Except.bind, pure, Except.pure]
          obtain ⟨oldRootEpoch, oldRootOk⟩ := e.call_root_known anchored sound start positiveSlotsNat
            window caller (nonzero u caller m) (lower m (List.mem_of_getElem? previousCall.1))
            previousCall.2.2
          have rootSame : oldRootEpoch = previous :=
            Except.ok.inj ((e.getBlockEpoch_of_le eventLt.le oldRootOk).symm.trans rootOk)
          obtain ⟨k, beforeK, origin, originOk, below, target, originSafe⟩ :=
            (earlier j (Nat.lt_succ_self j) m before fcr previousCall).2.2 previous oldEpochOk
              (rootSame ▸ oldRootOk)
          exact ⟨k, beforeK.trans eventLt.le, origin, rootOk,
            e.getBlockEpoch_of_le eventLt.le originOk, e.isAncestor_of_le eventLt.le below,
            target, fun time lower upper => originSafe time lower (upper.trans bounded)⟩
      · left
        have same := e.finalizedCheckpoint_eq_of_checked positiveSlotsNat window anchored sound
          caller (start u caller) (nonzero u caller n)
          ⟨_, slot, rootEpoch, startEpoch, epochOk, slotOk, rootEpochOk, startEpochOk,
            recent, checkedCases⟩
        have known := rootOk
        unfold Store.getBlockEpoch at known
        obtain ⟨block, found, _⟩ := bind_ok_iff.mp known
        exact ⟨n, le_rfl, _, rootOk, rootOk,
          Store.isAncestor_self (Store.block_ok_iff.mp found), Or.inl (congrArg Checkpoint.root same),
          fun time _ _ => (congrArg Checkpoint.root same) ▸ e.safeAt_anchor anchored start time⟩
    · exact Or.inr ⟨justification, rfl⟩
  have pins := e.honestThirdPins anchored sound positiveSlotsNat window ring preGloas nonzero start
    (fun w hw k state counts _ upper => large w hw k state counts upper) headDrifts unslashed
  have few : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon → getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} <
        2 * total.toNat := by
    intro w hw k state total _ counts epochLe totalOk
    have epochLeNat := UInt64.le_iff_toNat_le.mp epochLe
    have bound := byzantine w hw k state total counts (by omega) totalOk
    have totalLower := UInt64.le_iff_toNat_le.mp
      (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
    have incrementPositive := UInt64.lt_iff_toNat_lt.mp positive
    have strictBound := Nat.mul_lt_mul_of_pos_right enough (show 0 < total.toNat by omega)
    nlinarith
  have walkSafe : ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time after.confirmedRoot := by
    intro time afterCall bounded
    have callBound := afterCall.trans bounded
    exact e.safeAt_of_walk sync slots positiveSlotsNat window lookahead preGloas admitted oneBlock half
      votes fits prompt committees follows chain unique pins voted included anchored sound anchorSlot
      anchorAtBoundary start rfl noVotes maxAligned increment caller (upToDate n member) (lower n member)
      slotOk beginOk atSlot headOk
      ⟨_, slot, rootEpoch, startEpoch, epochOk, slotOk, rootEpochOk, startEpochOk, recent, checkedCases⟩
      sourceOk walked confirmedAll previousHead targetVotes (boundedLineage callBound)
      (previousLineage callBound) epochOk startBelow historicalOk historicalRecent epochStartOk
      epochStartTimeOk (fun earlier lower beforeCall => historicalSafe earlier lower (Nat.le_trans (Nat.le_of_lt beforeCall) callBound))
      startFacts.2 weights slack late anchorParent (fun w hw k _ => nonzero w hw k) inHorizon
      (fun w hw k state _ counts epochLe => large w hw k state counts
        (by have := UInt64.le_iff_toNat_le.mp epochLe; omega)) few unslashed time afterCall bounded
  have rootMem : after.confirmedRoot ∈ walk ++ after.confirmedRoot :: later := by simp
  obtain ⟨rootBlock, startBlock, rootBlockOk, startBlockOk, rootLater⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) rootMem
  have headAbove : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨after.confirmedRoot, .pending⟩ = .ok true := by
    rcases walk_member_ancestor preGloas walked _ rootMem with impossible | ⟨block, known, path⟩
    · cases impossible
    · simp [Store.isAncestor, Store.block_ok_iff.mpr known, path, bind, Except.bind, pure, Except.pure]
  have rootAbove : ((e.world n).state u).isAncestor ⟨after.confirmedRoot, .pending⟩
      ⟨selectedStart, .pending⟩ = .ok true := by
    apply walk_members_induction
      (fun r => ((e.world n).state u).isAncestor ⟨r, .pending⟩ ⟨selectedStart, .pending⟩ = .ok true)
      walked (Store.isAncestor_self (Store.block_ok_iff.mp startBlockOk)) ?_ (by simp)
      _ rootMem
    intro r _ block known parentAbove
    obtain ⟨parent, parentKnown, _⟩ :=
      Store.slot_le_of_isAncestor (Store.block_ok_iff.mp startBlockOk) parentAbove
    exact Store.isAncestor_of_parent preGloas known parentKnown
      (lower n member r block parent known parentKnown) parentAbove
  have currentRootInside (same : rootEpoch = computeEpochAtSlot preset slot) :
      isStartSlotAtEpoch preset slot = .ok false := by
    apply call_not_boundary
    intro boundary
    obtain ⟨support, threshold, supportOk, thresholdOk, _⟩ :=
      Store.isOneConfirmed_eq_ok_true_iff.mp (confirmedAll after.confirmedRoot (by simp))
    obtain ⟨s, block, parent, score, first, last, maximum, discount, adversary,
      sOk, blockOk, parentOk, scoreOk, firstOk, lastOk, maximumOk, discountOk, adversaryOk⟩ :=
      Store.computeSafetyThreshold_eq_ok thresholdOk
    have sameSlot : s = slot := Except.ok.inj (sOk.symm.trans slotOk)
    subst s
    obtain ⟨beforeBlock, participants, _, beforeOk, participantsOk, _, _⟩ :=
      Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk firstOk discountOk
    have marginOk := slack _ (by simp) block parent first last beforeBlock participants maximum score
      support discount adversary blockOk parentOk firstOk lastOk beforeOk participantsOk maximumOk
      scoreOk supportOk discountOk adversaryOk
    exact e.rootEpoch_ne_of_slack_at_epoch_start anchored start anchorSlot preGloas caller
      slotOk boundary epochOk rootEpochOk blockOk parentOk firstOk lastOk maximumOk supportOk
      discountOk marginOk same
  refine ⟨?_, ?_, ?_⟩
  · intro readSlot next following readSlotOk nextOk followingOk time afterNext bounded
    have same : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
    subst readSlot
    have late := fits.call_before_next_slot nextOk beginOk followingOk atSlot afterNext
    exact walkSafe time (by omega) bounded
  · intro epoch _ readEpoch _ _
    have same : epoch = computeEpochAtSlot preset slot := Except.ok.inj (readEpoch.symm.trans epochOk)
    subst epoch
    have known := historicalOk
    unfold Store.getBlockEpoch at known
    obtain ⟨block, found, _⟩ := bind_ok_iff.mp known
    exact ⟨historical, historicalEpoch, epochStart, epochStartTime,
      Store.isAncestor_trans_of_lt preGloas (Store.block_ok_iff.mp startBlockOk)
        (Store.block_ok_iff.mp found) rootAbove startBelow,
      historicalOk, historicalRecent, epochStartOk, epochStartTimeOk, historicalSafe⟩
  · intro epoch readEpoch readRootEpoch
    have same : epoch = computeEpochAtSlot preset slot := Except.ok.inj (readEpoch.symm.trans epochOk)
    subst epoch
    have rootSame : rootEpoch = computeEpochAtSlot preset slot :=
      Except.ok.inj (rootEpochOk.symm.trans readRootEpoch)
    by_cases startSame : startEpoch = computeEpochAtSlot preset slot
    · obtain ⟨k, before, origin, originEpoch, above, checkedOrigin, safeOrigin⟩ :=
        startFacts.1.2.2 _ epochOk (startSame ▸ startEpochOk)
      have known := originEpoch
      unfold Store.getBlockEpoch at known
      obtain ⟨block, found, _⟩ := bind_ok_iff.mp known
      exact ⟨k, before, origin, originEpoch,
        Store.isAncestor_trans_of_lt preGloas (Store.block_ok_iff.mp startBlockOk)
          (Store.block_ok_iff.mp found) rootAbove above, checkedOrigin, safeOrigin⟩
    · have target : ((e.world n).state u).willCurrentTargetBeJustified config head.root = .ok true := by
        rcases checkedCases with old | current
        · exact False.elim (old.2.1 rootSame)
        · exact current.2.1 rootSame startSame
      -- The strict slack excludes the boundary before the gated counts are used.
      exact ⟨n, le_rfl, after.confirmedRoot, readRootEpoch,
        Store.isAncestor_self (Store.block_ok_iff.mp rootBlockOk),
        Or.inr ⟨head, upToDate n member, epochOk, headOk, target, headAbove,
          targetVotes slot slotOk (currentRootInside rootSame)⟩, walkSafe⟩

/-- Theorem 1, safety: the block that the rule stores is safe from the start of the next slot.

This is a conditional result, under the hypotheses below and the placeholders it depends on.

It does not state the monotonicity part of the paper's Theorem 1.

An honest validator calls the rule at the events of a list, with its store up to date.

The calls are at the starts of consecutive slots, and the first store of the rule is the anchor's.

Each honest store starts as the store of the anchor, which holds no vote.

The anchor keeps the invariant of the state transition, and its block is at the start of an epoch.

An epoch has more than one slot, and the historical buffer holds two epochs.

The seed lookaheads are at least one, and the RANDAO buffer exceeds the lower one by more than 3.

These preset bounds are sufficient for this proof; they are not claimed to be necessary.

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

This excludes stores that hold that root; it is not an assumption on hashes.

With it, the parents of the blocks of each honest store are at lower slots.

The implementation-level bounds of `RuleBounds` hold, with that margin and a weight shift.

They generalize Assumption 2 of the paper and apply only to calls that confirm by a walk.

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
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
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
      exact e.callInvariant_step sync half slots long window lookahead votes fits prompt committees
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
