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
/-- The late majority of a receiver: its honest duties of a complete epoch outweigh the rest.

This is a generalized late-duty assumption, not Assumption 2 of the paper as stated there.

The paper fixes the validator set; here the receiver weighs with its own justified state.

That state may be old, so honest validators of its tally may have no duty in a recent epoch.

The epoch starts at a first time or later, and ends at a given time or before.

The tally is the set of validators that are active and not slashed in that state.

The honest validators of the tally with a duty in the epoch are the counted ones.

Twice their stake exceeds the stake of the whole tally plus the boost.

Every honest duty of the epoch supports the block, so the block then holds a majority.

It does not follow from `WeightBounds`, which compares the balances of two states.

It follows from a Byzantine bound on the tally with a margin for the missing duties.

`late_majority_of_missing_duties` gives that implication.

Take an assignment that gives each active validator a duty in each epoch, as with a static set.

Then the condition is `W + boost < 2 * H`, where `W` is the stake of the tally.

Here `H` is the stake of its honest validators.

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
    stake (fun v => balanceAt state v.toNat)
        ((unslashedActiveBalances state).map (·.1)).toFinset + boost <
      2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧
          ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
            assignment.committee v slot = some committeeIndex}

/-- A Byzantine bound with a margin for missing duties gives the late majority.

The validators of a set `V` with stakes `w` are honest when in `J`, and some have a duty.

The Byzantine validators hold at most `num / den` of the stake of `V`, with `2 * num ≤ den`.

Twice the stake of honest validators without a duty, plus the boost, fits in the margin.

Then twice the stake of honest validators with a duty exceeds the stake of `V` plus the boost. -/
theorem late_majority_of_missing_duties {ν : Type*} {w : ν → ℕ} {V : Finset ν}
    {J : Set ν} [DecidablePred (· ∈ J)] (duty : ν → Prop) [DecidablePred duty]
    {num den boost : ℕ} (byzantine : ByzantineStakeAtMost w V J num den)
    (half : 2 * num ≤ den)
    (margin : den * (2 * stake w {v ∈ V | v ∈ J ∧ ¬duty v} + boost) <
      (den - 2 * num) * stake w V) :
    stake w V + boost < 2 * stake w {v ∈ V | v ∈ J ∧ duty v} := by
  -- The honest stake splits into the stake with a duty and the stake without one.
  have split : stake w {v ∈ V | v ∈ J ∧ duty v} + stake w {v ∈ V | v ∈ J ∧ ¬duty v} =
      stake w {v ∈ V | v ∈ J} := by
    have := Finset.sum_filter_add_sum_filter_not {v ∈ V | v ∈ J} duty w
    simpa only [stake, Finset.filter_filter] using this
  exact byzantine.majority_of_missing_weight (score := stake w {v ∈ V | v ∈ J ∧ duty v})
    (by omega) half margin

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
    {horizon : Epoch} {last : ℕ} (chain : FinalizedPrefix e horizon last)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ last)
    {epoch : Epoch}
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
  have read := chain w receiver w receiver k' k ((e.monotone_time earlier).trans bounded) bounded
    justified (Or.inl rfl)
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
  have readNow := chain w receiver w receiver k k bounded bounded justified (Or.inl rfl) endpointLe
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
    (before : fork < .glamsterdam) {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last) {epoch : Epoch}
    (callerEpoch : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (receiverEpoch : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
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
  -- A source no later than the anchor's epoch leaves the receiver at the anchor's finality.
  by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
  · have same := walk_finalized_eq_anchor anchorStore anchored anchorSlot anchorBoundary before
      chain receiver kBound (UInt64.le_trans ordered old) anchorHorizon
    simpa only [same] using anchorRead
  -- A later source is after the genesis epoch, so the receiver counts it as justified.
  have later : GENESIS_EPOCH < checkpoint.epoch := by
    have notLe : ¬ checkpoint.epoch.toNat ≤ (getCurrentEpoch anchorState).toNat :=
      fun le => old (UInt64.le_iff_toNat_le.mpr le)
    apply UInt64.lt_iff_toNat_lt.mpr
    simp only [GENESIS_EPOCH, UInt64.toNat_zero]
    omega
  rcases walk_source_ancestor forward.reachable sound before positive window
      (UInt64.le_of_eq anchorSlot) nonzero child source with early |
      ⟨_, boundary, _, _, boundaryOk, _, read⟩
  · exact absurd early old
  · exact walk_finalized_read_of_source chain before caller receiver nBound kBound source boundaryOk
      read ordered
      (UInt64.le_trans (walk_source_epoch_le forward sound slots (UInt64.le_of_eq anchorSlot)
        before callerEpoch source) inHorizon) later

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
    (before : fork < .glamsterdam) {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last) {epoch : Epoch}
    (callerEpoch : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (receiverEpoch : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
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
    anchorSlot anchorBoundary before chain caller receiver nBound kBound callerEpoch receiverEpoch
    inHorizon
    anchorHorizon nonzero child tipKnown source recent
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
private theorem walk_vote_mem_window {limit : ℕ}
    (committees : CommitteesFollow e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode}
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
    committees.common u caller n bounded head headState current v attestation targetState
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
private theorem walk_supporters_in_window {limit : ℕ}
    (committees : CommitteesFollow e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode}
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
  apply walk_vote_mem_window committees caller bounded headOk stateOk epochOk
    (by rw [origin.targetEpoch, epochEq]; exact monotone (UInt64.le_of_lt past))
    (by rw [origin.targetEpoch]; have := monotone blockLe; omega) origin windowOk
    (UInt64.le_trans firstLe blockLe) high

/-- A recent one-confirmed block has an honest supporter in the caller's tally. -/
private theorem walk_exists_honest_supporter {limit : ℕ}
    (committees : CommitteesFollow e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode}
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
  have inside := walk_supporters_in_window committees caller bounded origins headOk stateOk slotOk
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

/-- A strictly earlier block in the same epoch rules out the epoch boundary. -/
private theorem walk_not_boundary {slot earlier : Slot}
    (lt : earlier < slot)
    (same : computeEpochAtSlot preset earlier = computeEpochAtSlot preset slot) :
    isStartSlotAtEpoch preset slot = .ok false := by
  unfold isStartSlotAtEpoch computeSlotsSinceEpochStart
  rw [computeStartSlotAtEpoch_computeEpochAtSlot]
  simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, decide_eq_false_iff_not]
  intro zero
  have zeroNat := congrArg UInt64.toNat zero
  have boundary := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot)).2
  have sameNat := congrArg UInt64.toNat same
  simp only [computeEpochAtSlot, UInt64.toNat_div] at sameNat boundary
  have le := Nat.div_mul_le_self earlier.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [sameNat] at le
  have upper := slot.toNat_lt
  have lower := (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
  have strict := UInt64.lt_iff_toNat_lt.mp lt
  simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zeroNat
  omega

/-- A recorded supporter places its supported block strictly before the store's slot. -/
private theorem walk_supported_slot_lt {store : Store preset fork}
    {source : BeaconState preset fork} {v : ValidatorIndex} {root : Root}
    {block : BeaconBlock preset fork} {slot : Slot}
    (origins : store.VotesHaveOrigins config)
    (known : store.blocks[root]? = some block)
    (slotOk : store.getCurrentSlot config = .ok slot)
    (supporter : v ∈ store.supportersOf source ⟨root, .pending⟩) : block.slot < slot := by
  obtain ⟨message, supported, latest, _, supportedOk, descends⟩ :=
    store.exists_of_voteCountsFor (Store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨attestation, rfl, origin⟩ := origins latest
  obtain ⟨votedBlock, votedKnown, votedLe⟩ := origin.voted
  obtain ⟨same, sameKnown, below⟩ := Store.slot_le_of_isAncestor known descends
  have rootEq := Store.getSupportedNode_root supportedOk
  change supported.root = attestation.data.beaconBlockRoot at rootEq
  rw [rootEq, votedKnown, Option.some.injEq] at sameKnown
  subst same
  obtain ⟨readSlot, readOk, past⟩ := origin.past
  rw [slotOk, Except.ok.injEq] at readOk
  subst readSlot
  exact UInt64.lt_of_le_of_lt (UInt64.le_trans below votedLe) past

/-- A checked supported root has a recent source at itself or a descendant. -/
private theorem walk_recent_source {store : Store preset fork} {fcr : FastConfirmationStore}
    {head start root : Root} {epoch : Epoch} {slot : Slot} {block : BeaconBlock preset fork}
    (checked : store.Checked config fcr head start root)
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (slotOk : store.getCurrentSlot config = .ok slot)
    (known : store.blocks[root]? = some block)
    (past : block.slot < slot)
    (headAbove : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    ∃ tip checkpoint,
      (store.getVotingSource config tip = .ok checkpoint ∨
        store.unrealizedJustification tip = .ok checkpoint) ∧
      epoch.toNat ≤ checkpoint.epoch.toNat + 2 ∧
      store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  have rootEpochOk : store.getBlockEpoch root = .ok (computeEpochAtSlot preset block.slot) := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr known, bind, Except.bind, pure, Except.pure]
  by_cases same : computeEpochAtSlot preset block.slot = epoch
  · have current : computeEpochAtSlot preset slot = epoch := by
      simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using epochOk
    have away := walk_not_boundary past (same.trans current.symm)
    obtain ⟨readEpoch, readSlot, rootEpoch, startEpoch, readEpochOk, readSlotOk,
      readRootEpochOk, _, _, branches⟩ := checked
    rw [epochOk, Except.ok.injEq] at readEpochOk
    rw [slotOk, Except.ok.injEq] at readSlotOk
    rw [rootEpochOk, Except.ok.injEq] at readRootEpochOk
    subst readEpoch
    subst readSlot
    subst rootEpoch
    rcases branches with previous | current
    · exact False.elim (previous.2.1 same)
    · obtain ⟨checkpoint, read, recent⟩ := current.1 away
      exact ⟨head, checkpoint, Or.inr read, by omega, headAbove⟩
  · obtain ⟨tip, checkpoint, read, recent, above⟩ :=
      walk_checked_source checked epochOk rootEpochOk same
    refine ⟨tip, checkpoint, Or.inl read, recent, ?_⟩
    rcases above with rfl | above
    · exact Store.isAncestor_self known
    · exact above

omit [DecidablePred (· ∈ J)] in
/-- Up-to-date honest stores at the same time read the same epoch. -/
private theorem walk_same_time_epoch {anchor : Store preset fork}
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (callerCurrent : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (receiverCurrent : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (same : (e.world n).time = (e.world k).time) {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
    ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch := by
  have clock : ((e.world k).state w).timeMs = ((e.world n).state u).timeMs :=
    UInt64.toNat_inj.mp (receiverCurrent.1.trans (same.symm.trans callerCurrent.1.symm))
  have left := (e.clock_bounds u n).1
  have right := (e.clock_bounds w k).1
  rw [anchored u caller] at left
  rw [anchored w receiver] at right
  simpa only [Store.getCurrentStoreEpoch, Store.getCurrentSlot, clock,
    right.trans left.symm] using epochOk

/-- A past honest supporter delivers the block once the caller establishes receiver finality. -/
private theorem walk_known_of_honest_supporter {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (fits : DelayFits fork config genesisTimeMs Δ)
    (preGloas : fork < .glamsterdam) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    (admitted : BlocksAdmitted e 0 Δ last) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {u v w : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) (receiver : w ∈ J)
    {n k : ℕ} (later : (e.world n).time ≤ (e.world k).time) (kBound : (e.world k).time ≤ last)
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
  have nBound := later.trans kBound
  obtain ⟨m, earlier, pastBlock, pastKnown, delivered⟩ := e.past_block_of_honest_supporter
    slots fits oneBlock anchorStore anchored caller honest callerCurrent nBound within supporter
  have mBound := (e.monotone_time earlier.le).trans nBound
  have same := oneBlock v honest u caller m n mBound nBound root pastBlock block pastKnown known
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
    (oneBlock u caller v honest n m nBound mBound) boundaryOk above ⟨block, pastKnown⟩ checkpoint
  exact (e.blocks_of_partiallySynchronous sync oneBlock admitted anchorStore anchored honest
    receiver (by simpa using delivered.trans later) kBound receiverCurrent finalizedKnown
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) pastKnown pastCheckpoint).1

omit [DecidablePred (· ∈ J)] in
/-- A checked root with an honest supporter is held by every up-to-date receiver then. -/
private theorem walk_known_at_call {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (fits : DelayFits fork config genesisTimeMs Δ) (before : fork < .glamsterdam)
    {last : ℕ} (oneBlock : OneBlockPerRoot e last) (admitted : BlocksAdmitted e 0 Δ last)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon last)
    {u v w : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) (receiver : w ∈ J)
    {n k : ℕ} (same : (e.world n).time = (e.world k).time) (bounded : (e.world k).time ≤ last)
    (callerCurrent : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (receiverCurrent : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {epoch : Epoch} {slot : Slot}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock)
    {source : BeaconState preset fork} (within : source.RegistryWithinLimit)
    {fcr : FastConfirmationStore} {head start root : Root} {block : BeaconBlock preset fork}
    (checked : ((e.world n).state u).Checked config fcr head start root)
    (known : ((e.world n).state u).blocks[root]? = some block)
    (recent : epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (headAbove : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (origins : ((e.world n).state u).VotesHaveOrigins config)
    (supporter : v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩) :
    ((e.world k).state w).blocks[root]? = some block := by
  classical
  have receiverEpoch := walk_same_time_epoch anchored caller receiver callerCurrent receiverCurrent
    same epochOk
  have past := walk_supported_slot_lt origins known slotOk supporter
  obtain ⟨tip, checkpoint, sourceRead, sourceRecent, above⟩ :=
    walk_recent_source checked epochOk slotOk known past headAbove
  have finality := walk_finalized_read_below_source anchorStore anchored sound slots positive window
    anchorSlot anchorBoundary before chain caller receiver (same ▸ bounded) bounded epochOk
    receiverEpoch inHorizon
    anchorHorizon nonzero child known above sourceRead sourceRecent recent
  exact walk_known_of_honest_supporter sync slots fits before oneBlock admitted anchorStore anchored
    anchorSlot anchorBoundary caller honest receiver (Nat.le_of_eq same) bounded callerCurrent
    receiverCurrent within known supporter
    (e.finalized_known_of_prefix anchorStore sound anchored slots anchorSlot before chain receiver
      bounded receiverEpoch inHorizon) finality

omit [DecidablePred (· ∈ J)] in
/-- Boundary admission persists; equal-time events use admission at that event itself. -/
private theorem walk_known_after_call {slot : Slot} {begin : UInt64}
    (prompt : Prompt e begin.toNat)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (started : e.startTime ≤ begin.toNat) {root : Root} {block : BeaconBlock preset fork}
    (atCall : ∀ w ∈ J, ∀ k, (e.world k).time = begin.toNat →
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
      ((e.world k).state w).blocks[root]? = some block)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ}
    (later : begin.toNat ≤ (e.world k).time)
    (current : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) : ((e.world k).state w).blocks[root]? = some block := by
  by_cases same : (e.world k).time = begin.toNat
  · exact atCall w receiver k same current
  obtain ⟨arrival, time, ready⟩ := (prompt w receiver slot begin beginOk started le_rfl).1
  have ordered : arrival ≤ k := by
    by_contra h
    have reverse := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp at reverse
    omega
  exact e.blocks_of_le ordered (atCall w receiver arrival time ready)

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

omit [DecidablePred (· ∈ J)] in
/-- Holding the stored root also holds every ancestor read along its caller-side walk. -/
private theorem walk_known_ancestor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) {last : ℕ}
    (oneBlock : OneBlockPerRoot e last)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {root member : Root} {block rootBlock : BeaconBlock preset fork}
    (known : ((e.world n).state u).blocks[member]? = some block)
    (received : ((e.world k).state w).blocks[root]? = some rootBlock)
    (path : ((e.world n).state u).getAncestor ⟨root, .pending⟩ block.slot =
      .ok ⟨member, .pending⟩) : ((e.world k).state w).blocks[member]? = some block := by
  have reached := e.reachable
    (fun v hv => (anchored v hv) ▸ Store.Reachable.anchor anchorStore)
  obtain ⟨b, held⟩ := (reached n u caller).known_of_ancestor_walk (reached k w receiver)
    (oneBlock u caller w receiver n k nBound kBound) ⟨rootBlock, received⟩ path
  have same := oneBlock u caller w receiver n k nBound kBound member block b known held
  exact same.symm ▸ held

/-- A nonempty walk separates its newly read roots from its supplied accumulator. -/
private theorem walk_without_acc {store : Store preset fork} {tip terminal : Root}
    {acc roots : List Root}
    (walked : store.getAncestorRoots tip terminal acc = .ok roots) (nonempty : roots ≠ []) :
    ∃ fresh, roots = fresh ++ acc ∧ store.getAncestorRoots tip terminal = .ok fresh := by
  have replace : ∀ otherAcc, ∃ fresh, roots = fresh ++ acc ∧
      store.getAncestorRoots tip terminal otherAcc = .ok (fresh ++ otherAcc) := by
    intro otherAcc
    fun_induction Store.getAncestorRoots store tip terminal acc generalizing roots otherAcc with
    | case1 => cases walked
    | case2 tip acc block found ih =>
      rw [bind_ok_iff] at walked
      obtain ⟨terminalBlock, terminalOk, walked⟩ := walked
      split at walked
      · exact False.elim (nonempty (Except.ok.inj walked).symm)
      · rename_i above
        dsimp only at walked
        split at walked
        · rename_i parentEq
          refine ⟨[tip], (Except.ok.inj walked).symm, ?_⟩
          rw [Store.getAncestorRoots, found]
          simp [terminalOk, above, parentEq,
            bind, Except.bind, pure, Except.pure]
        · rename_i parentNe
          split at walked
          · cases walked
          · rename_i parent parentFound
            split at walked
            · rename_i lower
              obtain ⟨fresh, shape, read⟩ := ih parent parentFound lower walked nonempty
                (tip :: otherAcc)
              refine ⟨fresh ++ [tip], by simpa using shape, ?_⟩
              rw [Store.getAncestorRoots, found]
              simp only [terminalOk, above, parentNe, bind, Except.bind, ↓reduceIte]
              rw [parentFound]
              simpa only [lower, ↓reduceDIte, List.append_assoc, List.singleton_append] using read
            · cases walked
  obtain ⟨fresh, shape, read⟩ := replace []
  exact ⟨fresh, shape, by simpa using read⟩

/-- New walk entries never have slots above the tip. -/
private theorem walk_slots_bounded {store : Store preset fork} {tip terminal : Root}
    {acc roots : List Root} {tipBlock : BeaconBlock preset fork}
    (known : store.blocks[tip]? = some tipBlock)
    (walked : store.getAncestorRoots tip terminal acc = .ok roots) :
    ∀ member ∈ roots, member ∈ acc ∨
      ∃ block, store.blocks[member]? = some block ∧ block.slot ≤ tipBlock.slot := by
  fun_induction Store.getAncestorRoots store tip terminal acc generalizing roots tipBlock with
  | case1 => simp_all
  | case2 tip acc block found ih =>
    have eq := Option.some.inj (found.symm.trans known)
    subst tipBlock
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
        · exact Or.inr ⟨block, found, UInt64.le_refl _⟩
        · exact Or.inl mem
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            intro member mem
            rcases ih parent parentFound lower parentFound walked member mem with old | fresh
            · rcases List.mem_cons.mp old with rfl | old
              · exact Or.inr ⟨block, found, UInt64.le_refl _⟩
              · exact Or.inl old
            · obtain ⟨b, held, below⟩ := fresh
              exact Or.inr ⟨b, held, UInt64.le_trans below (UInt64.le_of_lt lower)⟩
          · cases walked

/-- Every root before the tip in a walk has a strictly smaller slot. -/
private theorem walk_before_tip {store : Store preset fork} {tip terminal : Root}
    {acc older : List Root} {tipBlock : BeaconBlock preset fork}
    (known : store.blocks[tip]? = some tipBlock)
    (walked : store.getAncestorRoots tip terminal acc = .ok (older ++ tip :: acc)) :
    tip ∉ older := by
  rw [Store.getAncestorRoots, known] at walked
  simp only [bind_ok_iff] at walked
  obtain ⟨terminalBlock, _, walked⟩ := walked
  split at walked
  · simp [pure, Except.pure] at walked
  · split at walked
    · have lengths := congrArg List.length (Except.ok.inj walked)
      have empty : older = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_append, List.length_cons] at lengths
        omega
      simp [empty]
    · split at walked
      · cases walked
      · rename_i parent parentFound
        split at walked
        · rename_i lower
          obtain ⟨fresh, shape, read⟩ := walk_without_acc walked (by simp)
          have eq : older = fresh := List.append_cancel_right shape
          subst older
          intro member
          obtain ⟨b, held, below⟩ :=
            (walk_slots_bounded parentFound read tip member).resolve_left (by simp)
          rw [known, Option.some.injEq] at held
          subst b
          have := UInt64.lt_iff_toNat_lt.mp lower
          have := UInt64.le_iff_toNat_le.mp below
          omega
        · cases walked

/-- Splitting at a returned root gives the walk ending at that root. -/
private theorem walk_prefix {store : Store preset fork} {tip terminal root : Root}
    {acc front back : List Root}
    (walked : store.getAncestorRoots tip terminal acc = .ok (front ++ root :: back))
    (outside : root ∉ acc) :
    store.getAncestorRoots root terminal = .ok (front ++ [root]) := by
  fun_induction Store.getAncestorRoots store tip terminal acc generalizing front back with
  | case1 => cases walked
  | case2 tip acc block found ih =>
    by_cases same : root = tip
    · subst root
      have full : store.getAncestorRoots tip terminal acc = .ok (front ++ tip :: back) := by
        rw [Store.getAncestorRoots, found]
        exact walked
      rcases Store.getAncestorRoots_eq_nil_or full with empty | ⟨older, shape⟩
      · simp at empty
      have read := full
      rw [shape] at read
      have unique := (List.append_cons_inj_of_notMem (walk_before_tip found read) outside).mp
        shape.symm
      obtain ⟨fresh, freshShape, freshRead⟩ := walk_without_acc read (by simp)
      have freshEq : older ++ [tip] = fresh := by
        exact List.append_cancel_right (bs := acc) (by simpa using freshShape)
      simpa only [← freshEq, unique.1] using freshRead
    · rw [bind_ok_iff] at walked
      obtain ⟨terminalBlock, _, walked⟩ := walked
      split at walked
      · simp [pure, Except.pure] at walked
      · dsimp only at walked
        split at walked
        · have member : root ∈ tip :: acc := by
            rw [Except.ok.inj walked]
            simp
          exact False.elim ((List.mem_cons.mp member).elim same outside)
        · split at walked
          · cases walked
          · rename_i parent parentFound
            split at walked
            · rename_i lower
              exact ih parent parentFound lower walked (by simp [same, outside])
            · cases walked

/-- A root covered by justification needs no vote-weight comparison. -/
private theorem walk_head_of_covered {store : Store preset fork}
    (before : fork < .glamsterdam) {root : Root} {head : ForkChoiceNode}
    (covered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true)
    (headOk : store.getHead config = .ok head) :
    store.isAncestor head ⟨root, .pending⟩ = .ok true := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [Store.getHead, notGloas, false_and, ↓reduceIte, bind_ok_iff] at headOk
  obtain ⟨nodes, _, headOk⟩ := headOk
  exact Store.getHeadFrom_descends before rfl covered headOk

/-- A successful head walk weighs children at each held ancestor on its path. -/
private theorem walk_head_visits {store : Store preset fork}
    {tally : Except ForkChoiceError VoteTally} {nodes : List ForkChoiceNode}
    (before : fork < .glamsterdam) {target : Root} {targetBlock : BeaconBlock preset fork} :
    ∀ {start head : ForkChoiceNode} {startBlock : BeaconBlock preset fork},
      start.payloadStatus = .pending → store.blocks[start.root]? = some startBlock →
      startBlock.slot ≤ targetBlock.slot →
      store.getAncestor head targetBlock.slot = .ok ⟨target, .pending⟩ →
      store.getHeadFrom config tally nodes start = .ok head →
      ∃ result, store.heaviestChild config tally nodes ⟨target, .pending⟩ = .ok result := by
  intro start
  induction start using Store.getHeadFrom.induct store with
  | _ start ih =>
    intro head startBlock pending startKnown below path walk
    by_cases same : start = (⟨target, .pending⟩ : ForkChoiceNode)
    · rw [Store.getHeadFrom] at walk
      cases read : store.heaviestChild config tally nodes start with
      | error error => simp [read, bind, Except.bind] at walk
      | ok result => exact ⟨result, same ▸ read⟩
    rw [Store.getHeadFrom] at walk
    cases read : store.heaviestChild config tally nodes start with
    | error error => simp [read, bind, Except.bind] at walk
    | ok result =>
      cases result with
      | none =>
        simp only [read, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at walk
        subst head
        rw [Store.getAncestor_of_le startKnown below] at path
        exact False.elim (same (Except.ok.inj path))
      | some child =>
        simp only [read, bind, Except.bind] at walk
        split at walk
        · rename_i rank
          obtain ⟨children, weighted, childrenOk, weightedOk, choice⟩ := Store.heaviestChild_eq read
          obtain ⟨key, mem, _⟩ := chooseHeaviest_some choice
          obtain ⟨source, member, pair⟩ := mapM_ok_mem weightedOk _ mem
          obtain ⟨rfl, _⟩ := Store.weighNode_ok_iff.mp pair
          obtain ⟨childPending, childBlock, childKnown, parent⟩ :=
            (Store.mem_getNodeChildren before childrenOk).mp (List.mem_filter.mp member).1
          dsimp only at childPending childKnown
          have higher : startBlock.slot < childBlock.slot := by
            simp only [Store.nodeRank, childKnown, startKnown, childPending, pending,
              ↓reduceIte] at rank
            have := childBlock.slot.toNat_lt
            have := startBlock.slot.toNat_lt
            rw [UInt64.lt_iff_toNat_lt]
            omega
          by_cases childBelow : childBlock.slot ≤ targetBlock.slot
          · exact ih child rank childPending childKnown childBelow path walk
          · have upper := Store.getAncestor_getHeadFrom before walk childPending childKnown
            rw [Store.getAncestor_trans (UInt64.le_of_lt (UInt64.not_le.mp childBelow)) upper,
              Store.getAncestor_of_gt before childKnown childBelow (parent ▸ startKnown) higher,
              parent] at path
            have startNode : (⟨start.root, .pending⟩ : ForkChoiceNode) = start := by
              cases start
              simp_all
            rw [startNode, Store.getAncestor_of_le startKnown below] at path
            exact False.elim (same (Except.ok.inj path))
        · cases walk

/-- A viable child of a visited parent has a successful justified-state score read. -/
private theorem walk_score_read {store : Store preset fork}
    (before : fork < .glamsterdam) {state : BeaconState preset fork}
    {nodes : List ForkChoiceNode} {head : ForkChoiceNode} {root : Root}
    {block parent justified : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (parentKnown : store.blocks[block.parentRoot]? = some parent)
    (justifiedKnown : store.blocks[store.justifiedCheckpoint.root]? = some justified)
    (below : justified.slot ≤ parent.slot)
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (parentAbove : store.isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    (headOk : store.getHead config = .ok head) :
    ∃ score, store.getAttestationScore ⟨root, .pending⟩ state = .ok score := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [Store.getHead, notGloas, false_and, ↓reduceIte, tree, bind, Except.bind] at headOk
  obtain ⟨result, read⟩ := walk_head_visits before rfl justifiedKnown below
    (Store.getAncestor_of_isAncestor_of_lt before parentKnown parentAbove) headOk
  obtain ⟨children, weighted, childrenOk, weightedOk, _⟩ := Store.heaviestChild_eq read
  have member : (⟨root, .pending⟩ : ForkChoiceNode) ∈ children.filter (· ∈ nodes) := by
    apply List.mem_filter.mpr
    exact ⟨(Store.mem_getNodeChildren before childrenOk).mpr ⟨rfl, block, known, rfl⟩,
      by simpa using viable⟩
  obtain ⟨weighed, _, weightOk⟩ := exists_mem_of_mapM_ok weightedOk member
  have weightOk := (Store.weighNode_ok_iff.mp weightOk).2.1
  simp only [Store.getWeight, notGloas, ↓reduceIte, Store.justifiedTally_of_state stateOk,
    bind, Except.bind, pure, Except.pure, Bool.false_eq_true] at weightOk
  cases scoreOk : store.scoreFromTally (store.tallyVotes state) ⟨root, .pending⟩ with
  | error error => simp [scoreOk] at weightOk
  | ok score => exact ⟨score, scoreOk⟩

/-- A viable node not covered by justification has its parent at or above justification. -/
private theorem walk_justified_below_parent {store : Store preset fork}
    (lower : store.ParentsBelow) (before : fork < .glamsterdam)
    {nodes : List ForkChoiceNode} {root : Root} {block parent : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (parentKnown : store.blocks[block.parentRoot]? = some parent)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (uncovered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ ≠ .ok true) :
    ∃ justified, store.blocks[store.justifiedCheckpoint.root]? = some justified ∧
      justified.slot ≤ parent.slot := by
  have treeWalk : store.filterNodeTree config ⟨store.justifiedCheckpoint.root, .pending⟩ =
      .ok nodes := tree
  obtain ⟨justified, justifiedKnown⟩ := (Store.filterNodeTree_mem treeWalk _
    (Store.filterNodeTree_self treeWalk (by intro empty; simp [empty] at viable))).2.1
  refine ⟨justified, justifiedKnown, ?_⟩
  have ancestor := (Store.filterNodeTree_ancestor (lower := lower) before treeWalk _ viable).1
  rcases ancestor.eq_or_parent with same | above
  · have same := Option.some.inj same
    change store.justifiedCheckpoint.root = root at same
    apply False.elim
    apply uncovered
    simpa only [same] using Store.isAncestor_self (node := ⟨root, .pending⟩) known
  · rw [Store.blockTree_parent_of known] at above
    have le := above.height_le
    rw [Store.blockTree_height_of justifiedKnown, Store.blockTree_height_of parentKnown] at le
    exact UInt64.le_iff_toNat_le.mpr (by omega)

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

/-- Each parent in the confirmed walk still extends its terminal block.

The terminal itself is not a member, since every member has a strictly later slot. -/
private theorem walk_parent_below {store : Store preset fork}
    (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    {tip terminal : Root} {roots : List Root} {terminalBlock : BeaconBlock preset fork}
    (terminalKnown : store.blocks[terminal]? = some terminalBlock)
    (walked : store.getAncestorRoots tip terminal = .ok roots) :
    ∀ member ∈ roots, ∀ block, store.blocks[member]? = some block →
      store.isAncestor ⟨block.parentRoot, .pending⟩ ⟨terminal, .pending⟩ = .ok true := by
  have terminalOutside : terminal ∉ roots := by
    intro mem
    obtain ⟨b, t, bOk, tOk, lt⟩ :=
      Store.slot_lt_of_mem_getAncestorRoots walked (by simp) mem
    have bEq := Except.ok.inj ((Store.block_ok_iff.mpr terminalKnown).symm.trans bOk)
    have tEq := Except.ok.inj ((Store.block_ok_iff.mpr terminalKnown).symm.trans tOk)
    subst b
    subst t
    exact UInt64.lt_irrefl _ lt
  have all := walk_members_induction (fun r =>
      store.isAncestor ⟨r, .pending⟩ ⟨terminal, .pending⟩ = .ok true ∧
      ∀ block, store.blocks[r]? = some block → r ∈ roots →
        store.isAncestor ⟨block.parentRoot, .pending⟩ ⟨terminal, .pending⟩ = .ok true)
    walked ⟨Store.isAncestor_self terminalKnown, by
      intro block known mem
      exact False.elim (terminalOutside mem)⟩ (fun r mem block known parent => by
      obtain ⟨parentBlock, parentKnown, _⟩ :=
        Store.slot_le_of_isAncestor terminalKnown parent.1
      refine ⟨Store.isAncestor_of_parent before known parentKnown
        (lower r block parentBlock known parentKnown) parent.1, ?_⟩
      intro same sameKnown _
      cases Option.some.inj (known.symm.trans sameKnown)
      exact parent.1) (by simp)
  intro member mem block known
  exact (all member mem).2 block known mem

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

/-- The late-duty majority in the receiver's own state puts the node on the head chain. -/
private theorem walk_head_of_duty_majority {store : Store preset fork}
    {state : BeaconState preset fork} {config : Config} {nodes : List ForkChoiceNode}
    {node head : ForkChoiceNode} {score : Gwei} {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] (duty : ValidatorIndex → Prop) [DecidablePred duty]
    (within : state.RegistryWithinLimit) (lower : store.ParentsBelow)
    (before : fork < .glamsterdam)
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : node ∈ nodes)
    (scoreOk : store.getAttestationScore node state = .ok score)
    (supported : ∀ v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset,
      v ∈ J → duty v → v ∈ store.supportersOf state node)
    (majority : stake (fun v => balanceAt state v.toNat)
        ((unslashedActiveBalances state).map (·.1)).toFinset + store.boostScore config <
      2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧ duty v})
    (headOk : store.getHead config = .ok head) :
    store.isAncestor head node = .ok true := by
  classical
  have total := walk_tally_stake within (fun _ => True)
  simp only [Finset.filter_true] at total
  -- Every honest validator of the tally with a duty supports the node.
  have counted : stake (fun v => balanceAt state v.toNat)
      {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧ duty v} ≤
      score.toNat := by
    rw [← Store.stake_supportersOf within scoreOk]
    apply stake_mono
    intro v member
    obtain ⟨inside, honest, dutied⟩ := Finset.mem_filter.mp member
    exact supported v inside honest dutied
  apply Store.isAncestor_getHead_of_majority_withBoost lower before stateOk tree viable scoreOk
    ?_ headOk
  rw [total]
  omega


/-- A successful receiver clock read bounds the start time of its current slot. -/
private theorem walk_slot_time {clock : UInt64} {slot : Slot}
    (read : computeSlotAtTimeMs config genesisTimeMs clock = .ok slot) :
    ∃ start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧ start ≤ clock := by
  unfold computeSlotAtTimeMs at read
  simp only [bind_ok_iff] at read
  obtain ⟨elapsed, elapsedOk, divided⟩ := read
  obtain ⟨_, elapsedValue⟩ := subChecked_ok_iff.mp elapsedOk
  obtain ⟨_, slotValue⟩ := divChecked_ok_iff.mp divided
  have productLe : slot.toNat * config.SLOT_DURATION_MS.toNat ≤ elapsed.toNat := by
    rw [slotValue]
    exact Nat.div_mul_le_self _ _
  have productBound : slot.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 :=
    productLe.trans_lt elapsed.toNat_lt
  have productOk := mulChecked_of_lt productBound
  have productValue := (mulChecked_ok_iff.mp productOk).2
  have sumBound : genesisTimeMs.toNat + (slot * config.SLOT_DURATION_MS).toNat < 2 ^ 64 := by
    have := clock.toNat_lt
    omega
  have sumOk := addChecked_of_lt sumBound
  have sumValue := (addChecked_ok_iff.mp sumOk).2
  refine ⟨genesisTimeMs + slot * config.SLOT_DURATION_MS, ?_, ?_⟩
  · simp only [computeTimeAtSlotMs, productOk, sumOk, bind, Except.bind]
  · exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- A complete epoch cannot fit inside one instant when both durations are positive. -/
private theorem walk_no_complete_at_call
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (time : ℕ) : ¬CompleteEpochWithin preset config genesisTimeMs time time := by
  rintro ⟨epoch, first, next, firstTime, nextTime, _, nextOk, firstOk, endOk, low, high⟩
  have nextValue := (addChecked_ok_iff.mp nextOk).2
  have duration := UInt64.lt_iff_toNat_lt.mp slots
  unfold computeTimeAtSlotMs at firstOk endOk
  simp only [bind_ok_iff] at firstOk endOk
  obtain ⟨firstProduct, firstProductOk, firstSumOk⟩ := firstOk
  obtain ⟨nextProduct, nextProductOk, nextSumOk⟩ := endOk
  have fp := (mulChecked_ok_iff.mp firstProductOk).2
  have np := (mulChecked_ok_iff.mp nextProductOk).2
  have fs := (addChecked_ok_iff.mp firstSumOk).2
  have ns := (addChecked_ok_iff.mp nextSumOk).2
  have strict := Nat.mul_lt_mul_of_pos_right (show first.toNat < next.toNat by omega) duration
  omega

/-- The initial-phase age bound holds at every successful receiver clock, between ticks too. -/
private theorem walk_receiver_age_at_clock {slot current : Slot} {begin clock : UInt64}
    {parentEpoch : Epoch}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (clockOk : computeSlotAtTimeMs config genesisTimeMs clock = .ok current)
    (recent : (computeEpochAtSlot preset slot).toNat ≤ parentEpoch.toNat + 1)
    (initial : ¬CompleteEpochWithin preset config genesisTimeMs begin.toNat clock.toNat) :
    (computeEpochAtSlot preset current).toNat ≤ parentEpoch.toNat + 2 := by
  obtain ⟨endpoint, endpointOk, below⟩ := walk_slot_time clockOk
  apply walk_receiver_age positive beginOk endpointOk recent
  rintro ⟨epoch, first, next, firstTime, nextTime, firstOk, nextOk, firstTimeOk, nextTimeOk,
    fresh, complete⟩
  apply initial
  exact ⟨epoch, first, next, firstTime, nextTime, firstOk, nextOk, firstTimeOk, nextTimeOk,
    fresh, complete.trans (UInt64.le_iff_toNat_le.mp below)⟩

/-- Complete-epoch duties imply descent using only the receiver's justified balances. -/
private theorem walk_late_head {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (before : fork < .glamsterdam) {first time : ℕ} (oneBlock : OneBlockPerRoot e time)
    (admitted : BlocksAdmitted e 0 Δ time) (votes : Votes e.startTime time e)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
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
    {root : Root} (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (current : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {block parent : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    (parentKnown : ((e.world k).state w).blocks[block.parentRoot]? = some parent)
    (rootFinal : ∀ k' ≤ k, ∃ boundary,
      computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ block.slot ∧
      ((e.world k).state w).getCheckpointBlock root
        ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok ((e.world k').state w).finalizedCheckpoint.root)
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (within : state.RegistryWithinLimit) (lower : ((e.world k).state w).ParentsBelow)
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (parentAbove : ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (uncovered : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ ≠ .ok true)
    (margin : LateMargin config genesisTimeMs assignment J first time state
      (((e.world k).state w).boostScore config)) :
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true := by
  classical
  obtain ⟨epoch, begin, next, beginTime, endTime, beginOk, nextOk, beginTimeOk, endTimeOk,
    fresh, complete, majority⟩ := margin
  obtain ⟨justified, justifiedKnown, below⟩ :=
    walk_justified_below_parent lower before known parentKnown tree viable uncovered
  obtain ⟨score, scoreOk⟩ := walk_score_read before known parentKnown justifiedKnown below stateOk
    tree viable parentAbove headOk
  let duty := fun v => ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
    assignment.committee v slot = some committeeIndex
  apply walk_head_of_duty_majority duty within lower before stateOk tree viable scoreOk ?_
    majority headOk
  intro v active honest dutied
  exact (e.mem_supportersOf_of_duty_epoch sync slots positive window ring before oneBlock admitted
    votes fits prompt anchorStore sound anchorSlot anchorBoundary anchored noVotes started chain
    inHorizon nonzero large few beginOk nextOk beginTimeOk endTimeOk fresh complete safe receiver
    atTime current known (fun j le _ _ => Or.inl (rootFinal j le)) stateOk within honest active
    dutied).resolve_right uncovered

/-- The call-time balance bound supplies admission before the walk induction starts. -/
private theorem walk_admitted_root {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (fits : DelayFits fork config genesisTimeMs Δ) (before : fork < .glamsterdam)
    {last : ℕ} (oneBlock : OneBlockPerRoot e last) (admitted : BlocksAdmitted e 0 Δ last)
    (committees : CommitteesFollow e last) {epoch : Epoch} {slot : Slot} {begin : UInt64}
    (prompt : Prompt e begin.toNat)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon last)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (current : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat) (started : e.startTime ≤ begin.toNat)
    (callBound : (e.world n).time ≤ last)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock)
    {source headState : BeaconState preset fork} {head : ForkChoiceNode}
    {fcr : FastConfirmationStore} {start root : Root} {block : BeaconBlock preset fork}
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (headStateOk : ((e.world n).state u).blockState head.root = .ok headState)
    (known : ((e.world n).state u).blocks[root]? = some block)
    (recent : epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (notFuture : block.slot ≤ slot)
    (headAbove : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {shift : ℕ} (weights : WeightBounds e source (e.world n).time (e.world n).time shift)
    (confirmed : ((e.world n).state u).isOneConfirmed config head.root source
      (((e.world n).state u).tallyVotes source) root = .ok true) :
    ∀ w ∈ J, ∀ k, (e.world n).time ≤ (e.world k).time → (e.world k).time ≤ last →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) → ((e.world k).state w).blocks[root]? = some block := by
  have forward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) n u caller
  have within := BeaconState.registryWithinLimit_of_lt before source
  obtain ⟨v, supporter, honest⟩ := walk_exists_honest_supporter committees caller callBound
    forward.votesHaveOrigins headOk headStateOk slotOk epochOk known recent notFuture within
    aligned increment (weights.dishonest u caller n le_rfl)
    (fun first last participants read => weights.sourceByzantine u caller n head.root first last
      participants rfl read) confirmed
  intro w receiver k later _ ready
  apply walk_known_after_call prompt beginOk started (root := root) (block := block) ?_
    receiver (atSlot ▸ later) ready
  intro x hx j same ready
  exact walk_known_at_call sync slots positive window fits before oneBlock admitted anchorStore
    anchored sound anchorSlot anchorBoundary chain caller honest hx (atSlot.trans same.symm)
    (by omega) current ready epochOk slotOk inHorizon anchorHorizon nonzero child within
    checked known
    recent headAbove forward.votesHaveOrigins supporter

/-- The receiver's committee window bounds all siblings in the initial phase.

The cap counts members, so every counted sibling vote must enter that same window. -/
private theorem walk_initial_head {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor) (before : fork < .glamsterdam)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {limit : ℕ} (committees : CommitteesFollow e limit) (follows : HeadFollowsSupport e limit)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    (current : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (lower : ((e.world k).state w).ParentsBelow)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {head : ForkChoiceNode} {state : BeaconState preset fork} {root : Root}
    {block parent : BeaconBlock preset fork} {slot first last beforeBlock : Slot}
    {epoch : Epoch} {window participants : Std.TreeSet ValidatorIndex}
    {score : Gwei} {nodes : List ForkChoiceNode}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (blockOk : ((e.world k).state w).block root = .ok block)
    (parentOk : ((e.world k).state w).block block.parentRoot = .ok parent)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (age : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok window)
    (scoreOk : computeProposerScore config state = .ok score)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first beforeBlock =
      .ok participants)
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (parentAbove : ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    (margin : stake (fun v => balanceAt state v.toNat) (Store.activeMembers state window) +
        score.toNat <
      stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).parentVotersOf state participants block parent | v ∈ J} +
        2 * stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J}) :
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true := by
  apply follows.follows w receiver k bounded head state root block parent slot epoch first last
    beforeBlock
    window score nodes participants current headOk stateOk blockOk parentOk slotOk epochOk age
    firstOk lastOk beforeOk windowOk scoreOk participantsOk tree viable parentAbove ?_ margin
  intro child childBlock voter held parentEq counted active
  exact e.mem_activeMembers_of_sibling_vote anchorStore sound anchorSlot anchorBoundary anchored
    before lookahead committees receiver bounded current lower nonzero headOk stateOk blockOk
    parentOk
    slotOk epochOk age firstOk lastOk windowOk parentAbove held parentEq counted active

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
    (preGloas : fork < .glamsterdam) {limit : ℕ} (admitted : BlocksAdmitted e 0 Δ limit)
    (oneBlock : OneBlockPerRoot e limit)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (votes : Votes e.startTime limit e)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e limit) (committees : CommitteesFollow e limit)
    (follows : HeadFollowsSupport e limit)
    {horizon anchorEpoch : Epoch} {margin : ℕ}
    (chain : FinalizedPrefix e horizon limit)
    (unique : OneJustifiedPerEpoch e horizon limit)
    (pins : HonestThirdPins e anchorEpoch horizon margin limit)
    (voted : JustifiedByHonestVote e anchorEpoch horizon limit) (included : TargetIncluded e limit)
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
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit → SafeAt e time root := by
  classical
  intro time afterCall bounded
  have callBound := afterCall.trans bounded
  have forward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore)
  have reached := fun k w hw => (forward k w hw).reachable
  have rootMem : root ∈ chain ++ root :: later := by simp
  have prefixWalk := walk_prefix walked (by simp)
  obtain ⟨rootBlock, startBlock, rootOk, startOk, rootLater⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) rootMem
  have rootKnown := Store.block_ok_iff.mp rootOk
  have startKnown := Store.block_ok_iff.mp startOk
  have rootRecent := walk_member_recent checked walked rootMem epochOk rootKnown
  have headAbove : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true := by
    rcases walk_member_ancestor preGloas walked root rootMem with impossible | ⟨b, held, path⟩
    · cases impossible
    · simp [Store.isAncestor, Store.block_ok_iff.mpr held, path, bind, Except.bind,
        pure, Except.pure]
  obtain ⟨headBlock, headKnown, _⟩ := Store.slot_le_of_isAncestor rootKnown headAbove
  obtain ⟨headState, headStateHeld, _⟩ := (reached n u caller).blockStatesFromParents headKnown
  obtain ⟨readSlot, readSlotOk, blocksBound, _⟩ :=
    (forward n u caller).slots_le_current slots (UInt64.le_of_eq anchorSlot)
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  have epochValue : epoch = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using
      epochOk.symm
  have anchorHorizon : getCurrentEpoch anchorState ≤ horizon := by
    obtain ⟨r, _, held⟩ := (reached n u caller).anchor_known
    have bound := UInt64.le_iff_toNat_le.mp (blocksBound r anchorBlock held)
    rw [anchorSlot] at bound
    apply UInt64.le_trans _ (inHorizon u caller n epoch callBound epochOk)
    rw [epochValue]
    exact UInt64.le_iff_toNat_le.mpr (Nat.div_le_div_right bound)
  have child : rootBlock ≠ anchorBlock := by
    intro same
    have bound := UInt64.le_iff_toNat_le.mp ((reached n u caller).anchorSlot_le_block startKnown)
    have strict := UInt64.lt_iff_toNat_lt.mp rootLater
    rw [same] at strict
    omega
  have started : e.startTime ≤ begin.toNat := by
    have le := e.monotone_time (Nat.zero_le n)
    simpa [Execution.world_zero, World.initial, atSlot] using le
  -- The zero-length range supplies honest support without assuming prior safety of the root.
  have callWeights := weights _ callBound (walk_no_complete_at_call slots positive _)
  have known := walk_admitted_root sync slots positive window fits preGloas oneBlock admitted
    committees (prompt.of_le (by omega)) anchorStore anchored sound anchorSlot anchorBoundary
    (by assumption) caller upToDate
    epochOk slotOk beginOk atSlot started callBound (inHorizon u caller n epoch callBound epochOk)
    anchorHorizon (nonzero u caller n callBound) ⟨root, rootBlock, rootKnown, child⟩ checked
    headOk (Store.blockState_ok_iff.mpr headStateHeld) rootKnown rootRecent
    (blocksBound root rootBlock rootKnown) headAbove
    (Store.Reachable.checkpointState_aligned sound (reached n u caller) maxAligned sourceOk)
    increment callWeights (allConfirmed root (by simp))
  -- Slack excludes the current-epoch boundary case required by checkpoint coverage.
  have atStart : ∀ s re ep,
      ((e.world n).state u).getCurrentSlot config = .ok s →
      isStartSlotAtEpoch preset s = .ok true →
      ((e.world n).state u).getCurrentStoreEpoch config = .ok ep →
      ((e.world n).state u).getBlockEpoch root = .ok re → re = ep →
      root = ((e.world n).state u).finalizedCheckpoint.root := by
    intro s re ep sOk boundary epOk reOk same
    have eq := Except.ok.inj (sOk.symm.trans slotOk)
    subst s
    obtain ⟨support, threshold, supportOk, thresholdOk, _⟩ :=
      Store.isOneConfirmed_eq_ok_true_iff.mp (allConfirmed root (by simp))
    obtain ⟨s, block, parent, score, first, last, maximum, discount, adversary,
      sOk, blockOk, parentOk, scoreOk, firstOk, lastOk, maximumOk, discountOk, adversaryOk⟩ :=
      Store.computeSafetyThreshold_eq_ok thresholdOk
    have eq := Except.ok.inj (sOk.symm.trans slotOk)
    subst s
    obtain ⟨beforeBlock, participants, _, beforeOk, participantsOk, _, _⟩ :=
      Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
        firstOk discountOk
    have strict := slack root (by simp) block parent first last beforeBlock participants maximum
      score support discount adversary blockOk parentOk firstOk lastOk beforeOk participantsOk
      maximumOk scoreOk supportOk discountOk adversaryOk
    exact False.elim (e.rootEpoch_ne_of_slack_at_epoch_start anchorStore anchored anchorSlot
      preGloas caller slotOk boundary epOk reOk blockOk parentOk firstOk lastOk maximumOk supportOk
      discountOk strict same)
  -- Keep the checked root fixed while advancing through only its confirmed prefix.
  apply walk_time_members_induction (SafeAt e) prefixWalk startSafe ?_ time afterCall bounded root
    (by simp)
  intro now afterNow boundedNow earlier member mem block held parentSafe
  have rootSafe := fun t lower upper => earlier t lower upper root (by simp)
  have coverage := e.coveredOrViableAt_of_checked sync slots positive window
    (by omega) preGloas (admitted.of_le boundedNow) (oneBlock.of_le boundedNow)
    (votes.of_le boundedNow) fits (prompt.of_le boundedNow) (committees.of_le boundedNow)
    { reads := fun w hw k bounded => follows.reads w hw k (bounded.trans boundedNow)
      follows := fun w hw k bounded => follows.follows w hw k (bounded.trans boundedNow) }
    (‹FinalizedPrefix e horizon limit›.of_le boundedNow) (unique.of_le boundedNow)
    (pins.of_le boundedNow) (voted.of_le boundedNow) (included.of_le boundedNow) anchorStore
    sound anchorSlot anchored anchorOk anchorBoundary caller upToDate
    ⟨slot, begin, slotOk, beginOk, atSlot⟩ headOk checked headAbove atStart
    (previousHead.imp_right (by
      rintro ⟨k, before, previous, previousSlot, ready, read, eq, oldSlot, next⟩
      exact ⟨k, before, previous, previousSlot, slot, ready, read, eq, oldSlot, slotOk, next⟩))
    targetVotes lineage (by
      intro ep previous s epOk sOk boundary next startEpoch
      have eq := Except.ok.inj (sOk.symm.trans slotOk)
      subst s
      exact previousLineage ep previous epOk boundary next startEpoch)
    afterNow (fun w hw k le => nonzero w hw k (le.trans boundedNow))
    (fun w hw k ep le => inHorizon w hw k ep (le.trans boundedNow))
    (fun w hw k c s le => supply w hw k c s (le.trans boundedNow))
    (fun w hw k le => anchorParent w hw k (le.trans boundedNow))
    (fun w hw k s le => large w hw k s (le.trans boundedNow)) long boost
    (fun t lower upper => startSafe t lower (upper.trans boundedNow)) rootSafe
    (fun w hw k eq ready => ⟨rootBlock, known w hw k (afterNow.trans_eq eq.symm)
      (eq.trans_le boundedNow) ready⟩)
  intro w receiver k receiverHead atNow ready receiverHeadOk
  have receiverBound : (e.world k).time ≤ limit := atNow ▸ boundedNow
  have receiverLower := (reached k w receiver).parentsBelow (UInt64.le_of_eq anchorSlot)
    (anchorParent w receiver k receiverBound)
  have received := known w receiver k (afterNow.trans_eq atNow.symm) receiverBound ready
  obtain ⟨state, current, score, nodes, stateOk, currentOk, scoreOk, tree, reads⟩ :=
    follows.reads w receiver k receiverBound receiverHead ready receiverHeadOk
  have receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have memberPath : ((e.world n).state u).getAncestor ⟨root, .pending⟩ block.slot =
      .ok ⟨member, .pending⟩ := by
    rcases walk_member_ancestor preGloas prefixWalk member mem with impossible | ⟨b, bHeld, path⟩
    · cases impossible
    · cases Option.some.inj (held.symm.trans bHeld)
      exact path
  have memberKnown := walk_known_ancestor anchorStore anchored oneBlock caller receiver callBound
    receiverBound held
    received memberPath
  have memberAbove : ((e.world k).state w).isAncestor ⟨root, .pending⟩ ⟨member, .pending⟩ =
      .ok true := by
    apply Store.isAncestor_of_same_blocks (reached k w receiver) preGloas
      (oneBlock u caller w receiver n k callBound receiverBound) held memberKnown
      ((reached n u caller).anchorSlot_le_block held) ⟨rootBlock, received⟩
    simp [Store.isAncestor, Store.block_ok_iff.mpr held, memberPath, bind, Except.bind,
      pure, Except.pure]
  -- Coverage of the stored root also covers every earlier member, but need not make it viable.
  have memberCoverage := walk_covered_ancestor (reached k w receiver) anchorSlot receiverLower
    preGloas memberKnown memberAbove tree (coverage w receiver k nodes atNow ready tree)
  by_cases covered : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨member, .pending⟩ = .ok true
  · exact walk_head_of_covered preGloas covered receiverHeadOk
  have viable := memberCoverage.resolve_left covered
  have rootFinal := (e.rootFinal_or_justified_covers anchorStore sound anchored slots anchorSlot
    preGloas (by assumption) receiver receiverBound receiverEpochOk
    (inHorizon w receiver k _ receiverBound receiverEpochOk) receiverLower memberKnown tree
    memberCoverage).resolve_left covered
  have parentAbove := parentSafe w receiver k receiverHead atNow ready receiverHeadOk
  obtain ⟨support, threshold, supportOk, thresholdOk, _⟩ :=
    Store.isOneConfirmed_eq_ok_true_iff.mp (allConfirmed member mem)
  obtain ⟨s, b, parent, boost, first, last, maximum, discount, adversary,
    sOk, bOk, parentOk, boostOk, firstOk, lastOk, maximumOk, discountOk, adversaryOk⟩ :=
    Store.computeSafetyThreshold_eq_ok thresholdOk
  have sEq := Except.ok.inj (sOk.symm.trans slotOk)
  subst s
  have bEq := Except.ok.inj (bOk.symm.trans (Store.block_ok_iff.mpr held))
  subst b
  have parentRead := parentAbove
  unfold Store.isAncestor at parentRead
  rw [bind_ok_iff] at parentRead
  obtain ⟨receiverParent, receiverParentOk, _⟩ := parentRead
  have receiverParentKnown := Store.block_ok_iff.mp receiverParentOk
  have sameParent := oneBlock u caller w receiver n k callBound receiverBound block.parentRoot
    parent receiverParent
    (Store.block_ok_iff.mp parentOk) receiverParentKnown
  subst receiverParent
  -- Late duties use the receiver's own justified balances, without transporting caller weights.
  by_cases complete : CompleteEpochWithin preset config genesisTimeMs (e.world n).time now
  · have rootUncovered : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ ≠ .ok true := by
      intro rootCovered
      exact covered (Store.isAncestor_trans_of_lt preGloas received memberKnown rootCovered
        memberAbove)
    exact walk_late_head sync slots positive window (by omega) preGloas
      (oneBlock.of_le boundedNow) (admitted.of_le boundedNow)
      (votes.of_le (by omega)) fits (prompt.of_le (by omega)) anchorStore sound anchorSlot
      anchorBoundary anchored noVotes (atSlot ▸ started)
      (‹FinalizedPrefix e horizon limit›.of_le boundedNow)
      (fun x hx j ep le => inHorizon x hx j ep (le.trans boundedNow))
      (fun x hx j le => nonzero x hx j (le.trans boundedNow))
      (fun x hx j s le => large x hx j s (le.trans boundedNow))
      (fun x hx j s total le => few x hx j s total (le.trans boundedNow))
      (fun t low high => earlier t low high member mem) receiver atNow ready memberKnown
      receiverParentKnown rootFinal stateOk (BeaconState.registryWithinLimit_of_lt preGloas state)
      receiverLower tree viable parentAbove receiverHeadOk covered
      (by simpa only [atNow] using (late w receiver k state (atNow ▸ complete) receiverBound ready
        stateOk rootUncovered))
  have clocks := (e.clock_bounds u n).1
  have receiverClocks := (e.clock_bounds w k).1
  rw [anchored u caller] at clocks
  rw [anchored w receiver] at receiverClocks
  have currentLe : slot ≤ current := by
    apply computeSlotAtTimeMs_mono (laterMs := ((e.world k).state w).timeMs)
      (UInt64.le_iff_toNat_le.mpr (by rw [upToDate.1, ready.1]; exact afterNow.trans_eq atNow.symm))
      (mapError_ok_iff.mp slotOk)
    simpa only [Store.getCurrentSlot, receiverClocks.trans clocks.symm] using
      (mapError_ok_iff.mp currentOk)
  obtain ⟨beforeBlock, participants, _, beforeOk, participantsOk, _, _⟩ :=
    Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount bOk parentOk firstOk discountOk
  have slotPositive : 1 ≤ current.toNat := by
    have := (subChecked_ok_iff.mp lastOk).1
    have := UInt64.le_iff_toNat_le.mp currentLe
    simp only [UInt64.toNat_one] at *
    omega
  -- Checked subtraction is justified by the successful caller read and monotonic clocks.
  have receiverLastOk : subChecked current 1 = .ok (current - 1) := by
    apply subChecked_ok_iff.mpr
    exact ⟨slotPositive, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr slotPositive)⟩
  have lastLt : current - 1 < current := by
    have := (subChecked_ok_iff.mp receiverLastOk).2
    apply UInt64.lt_iff_toNat_lt.mpr
    simp only [UInt64.toNat_one] at *
    omega
  have beforeLt : beforeBlock < current := by
    have := (subChecked_ok_iff.mp beforeOk).2
    have bound := UInt64.le_iff_toNat_le.mp (blocksBound member block held)
    have currentBound := UInt64.le_iff_toNat_le.mp currentLe
    apply UInt64.lt_iff_toNat_lt.mpr
    simp only [UInt64.toNat_one] at *
    omega
  obtain ⟨receiverWindow, receiverWindowOk⟩ := reads first (current - 1) lastLt
  obtain ⟨receiverParticipants, receiverParticipantsOk⟩ := reads first beforeBlock beforeLt
  have parentBelow := walk_parent_below preGloas lower startKnown prefixWalk member mem block held
  obtain ⟨sameParent, sameParentKnown, startLe⟩ := Store.slot_le_of_isAncestor startKnown parentBelow
  have eq := Option.some.inj ((Store.block_ok_iff.mp parentOk).symm.trans sameParentKnown)
  subst sameParent
  have recentParent : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1 := by
    obtain ⟨ep, s, re, se, epOk, _, _, seOk, recentStart, _⟩ := checked
    have epEq := Except.ok.inj (epOk.symm.trans epochOk)
    subst ep
    have seEq : se = computeEpochAtSlot preset startBlock.slot := by
      simpa [Store.getBlockEpoch, startOk, bind, Except.bind, pure, Except.pure] using seOk.symm
    have bound := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp startLe)
    rw [seEq, epochValue] at recentStart
    simp only [computeEpochAtSlot, UInt64.toNat_div] at *
    omega
  -- An honest signed vote identifies the model's genesis time with the common store clock.
  have receiverClock : computeSlotAtTimeMs config genesisTimeMs ((e.world k).state w).timeMs =
      .ok current := by
    obtain ⟨v, supporter, honest⟩ := walk_exists_honest_supporter committees caller callBound
      (forward n u caller).votesHaveOrigins headOk (Store.blockState_ok_iff.mpr headStateHeld)
      slotOk epochOk rootKnown rootRecent (blocksBound root rootBlock rootKnown)
      (BeaconState.registryWithinLimit_of_lt preGloas balanceSource)
      (Store.Reachable.checkpointState_aligned sound (reached n u caller) maxAligned sourceOk)
      increment (callWeights.dishonest u caller n le_rfl)
      (fun first last participants read => callWeights.sourceByzantine u caller n head.root
        first last participants rfl read) (allConfirmed root (by simp))
    obtain ⟨message, supported, latest, _, _, _⟩ :=
      ((e.world n).state u).exists_of_voteCountsFor
        (Store.voteCountsFor_of_mem_supportersOf supporter)
    obtain ⟨a, msg, seen, rfl, signed, _⟩ :=
      e.exists_signed_origin_of_latestMessages anchorStore anchored caller latest
    obtain ⟨j, _, maySign⟩ := e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
    obtain ⟨_, _, _, genesis, _⟩ := maySign
    have receiverGenesis : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
      rw [(e.clock_bounds w k).1, anchored w receiver, ← anchored v honest,
        ← (e.clock_bounds v j).1, genesis]
    simpa only [Store.getCurrentSlot, receiverGenesis] using (mapError_ok_iff.mp currentOk)
  have age := walk_receiver_age_at_clock positive beginOk receiverClock recentParent
    (by simpa only [← atSlot, ready.1, atNow] using complete)
  have historicalKnown : ∃ b, ((e.world n).state u).blocks[historical]? = some b := by
    unfold Store.getBlockEpoch at historicalEpochOk
    obtain ⟨b, read, _⟩ := bind_ok_iff.mp historicalEpochOk
    exact ⟨b, Store.block_ok_iff.mp read⟩
  obtain ⟨historicalBlock, historicalKnown⟩ := historicalKnown
  have parentHistorical := Store.isAncestor_trans_of_lt preGloas startKnown historicalKnown
    parentBelow startBelow
  have memberOnHead : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨member, .pending⟩ = .ok true := by
    apply Store.isAncestor_trans_of_lt preGloas rootKnown held headAbove
    simp [Store.isAncestor, Store.block_ok_iff.mpr held, memberPath, bind, Except.bind,
      pure, Except.pure]
  -- The transport uses the same guarded committee cap as the receiver's head rule.
  have transported := e.honest_support_of_historical_anchor sync slots positive window lookahead
    preGloas (admitted.of_le boundedNow) (oneBlock.of_le boundedNow) half
    (votes.of_le boundedNow) fits (prompt.of_le boundedNow) (committees.of_le boundedNow)
    anchorStore sound anchorSlot
    anchorBoundary anchored noVotes caller upToDate ⟨head, headOk, rfl⟩ slotOk beginOk atSlot
    bOk parentOk sourceOk boostOk firstOk lastOk beforeOk maximumOk participantsOk
    (BeaconState.registryWithinLimit_of_lt preGloas balanceSource)
    (Store.Reachable.checkpointState_aligned sound (reached n u caller) maxAligned sourceOk)
    increment supportOk discountOk adversaryOk (allConfirmed member mem)
    (slack member mem block parent first last beforeBlock participants maximum boost support discount
      adversary bOk parentOk firstOk lastOk beforeOk participantsOk maximumOk boostOk supportOk
      discountOk adversaryOk) afterNow (weights now boundedNow complete)
    (‹FinalizedPrefix e horizon limit›.of_le boundedNow)
    (fun x hx j ep le => inHorizon x hx j ep (le.trans boundedNow))
    (fun x hx j le => nonzero x hx j (le.trans boundedNow))
    (fun x hx j s le => large x hx j s (le.trans boundedNow))
    (fun x hx j s total le => few x hx j s total (le.trans boundedNow))
    (fun x hx j s le => unslashed x hx j s (le.trans boundedNow))
    (fun x hx j c s le => supply x hx j c s (le.trans boundedNow))
    (fun t lo hi => earlier t lo hi member mem) memberOnHead parentHistorical epochOk
    historicalEpochOk recent epochStartOk epochStartTimeOk historicalSafe receiver atNow ready
    memberKnown (fun j le _ => Or.inl (rootFinal j le)) receiverHeadOk parentAbove stateOk currentOk
    receiverEpochOk age receiverLastOk receiverWindowOk scoreOk receiverParticipantsOk
  apply walk_initial_head anchorStore sound anchorSlot anchorBoundary anchored preGloas lookahead
    committees follows receiver receiverBound ready receiverLower
    (nonzero w receiver k receiverBound)
    receiverHeadOk stateOk (Store.block_ok_iff.mpr memberKnown)
    (Store.block_ok_iff.mpr receiverParentKnown) currentOk receiverEpochOk age firstOk receiverLastOk
    beforeOk receiverWindowOk scoreOk receiverParticipantsOk tree viable parentAbove
    (transported.resolve_right covered)

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
        HonestTargetVotes e margin u k head.root ∧
        ∃ slot begin, ((e.world k).state u).getCurrentSlot config = .ok slot ∧
          computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
          (e.world k).time = begin.toNat) ∧
      ∀ time, (e.world k).time ≤ time → time ≤ limit → SafeAt e time origin)

/-- The call's committee bounds count honest targets without assuming honest equivocation. -/
private theorem Execution.call_targetVotes {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (sound : Invariant anchorState)
    (slots : 0 < config.SLOT_DURATION_MS) {limit : ℕ} (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot}
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
    caller bounded
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
    (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {limit : ℕ} (votes : Votes e.startTime limit e)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e limit)
    (committees : CommitteesFollow e limit) (follows : HeadFollowsSupport e limit)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e limit) (admitted : BlocksAdmitted e 0 Δ limit)
    (included : TargetIncluded e limit)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon limit)
    (unique : OneJustifiedPerEpoch e horizon limit)
    {threshold margin : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (headDrifts : ∀ w ∈ J, ∀ n head headState epoch, (e.world n).time ≤ limit →
      ((e.world n).state w).getPulledUpHeadState config head = .ok headState →
      ((e.world n).state w).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ v ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
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
    {shift : ℕ}
    (bounds : RuleBounds e u events (getFastConfirmationStore anchor) margin shift limit)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt e u events (getFastConfirmationStore anchor) i n fcr after)
    (callBound : (e.world n).time ≤ limit)
    (earlier : ∀ i' < i, ∀ n' fcr' after',
      CallAt e u events (getFastConfirmationStore anchor) i' n' fcr' after' →
      (e.world n').time ≤ limit →
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
        start chain caller epochOk nonzero inHorizon)
    intro epoch currentOk
    exact (e.finalizedCheckpoint_eq_or_blockEpoch_add_two_le positiveSlotsNat window anchored
      sound caller (start u caller) (nonzero u caller n callBound) currentOk).resolve_left same
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
      obtain ⟨nextOk, _, delayed⟩ := call_slots_order fits
        (by omega : slot.toNat = oldSlot.toNat + 1) oldTimeOk beginOk atOldSlot atSlot
      have inv := earlier j (Nat.lt_succ_self j) m before fcr previous (by omega)
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
      obtain ⟨nextOk, eventLt, delayed⟩ :=
        call_slots_order fits sum oldTimeOk beginOk atOldSlot atSlot
      have inv := earlier j (Nat.lt_succ_self j) m before fcr previous (by omega)
      have known := e.call_root_known anchored sound start positiveSlotsNat window caller
        (nonzero u caller m (by omega)) (lower m (List.mem_of_getElem? previous.1)) previous.2.2
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
    nonzero start
    (fun w hw k state bounded counts _ upper => large w hw k state bounded counts upper)
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
      exact e.safeAt_observed sync positiveSlotsNat window slots fits preGloas
        oneBlock admitted anchored sound start chain unique voted caller delayed.le oldEpochOk
        epochOk epochNext slotOk boundary beginOk atSlot found age nonzero inHorizon
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
      caller callBound
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
          caller (start u caller) (nonzero u caller n callBound) checked
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
          obtain ⟨_, eventLt, delayed⟩ :=
            call_slots_order fits sum oldTimeOk beginOk atOldSlot atSlot
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
            window caller (nonzero u caller m (by omega))
            (lower m (List.mem_of_getElem? previousCall.1))
            previousCall.2.2
          have rootSame : oldRootEpoch = previous :=
            Except.ok.inj ((e.getBlockEpoch_of_le eventLt.le oldRootOk).symm.trans rootOk)
          obtain ⟨k, beforeK, origin, originOk, below, target, originSafe⟩ :=
            (earlier j (Nat.lt_succ_self j) m before fcr previousCall (by omega)).2.2 previous
              oldEpochOk
              (rootSame ▸ oldRootOk)
          exact ⟨k, beforeK.trans eventLt.le, origin, rootOk,
            e.getBlockEpoch_of_le eventLt.le originOk, e.isAncestor_of_le eventLt.le below,
            target, fun time lower upper => originSafe time lower (upper.trans bounded)⟩
      · left
        have same := e.finalizedCheckpoint_eq_of_checked positiveSlotsNat window anchored sound
          caller (start u caller) (nonzero u caller n bounded)
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
    (fun w hw k state bounded counts _ upper => large w hw k state bounded counts upper) headDrifts
    unslashed
  have few : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon → getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} <
        2 * total.toNat := by
    intro w hw k state total bounded counts epochLe totalOk
    have epochLeNat := UInt64.le_iff_toNat_le.mp epochLe
    have bound := byzantine w hw k state total bounded counts (by omega) totalOk
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
      boost long
      votes fits prompt committees follows chain unique pins voted included anchored sound anchorSlot
      anchorAtBoundary start rfl noVotes maxAligned increment caller (upToDate n member) (lower n member)
      slotOk beginOk atSlot headOk
      ⟨_, slot, rootEpoch, startEpoch, epochOk, slotOk, rootEpochOk, startEpochOk, recent, checkedCases⟩
      sourceOk walked confirmedAll previousHead targetVotes (boundedLineage callBound)
      (previousLineage callBound) epochOk startBelow historicalOk historicalRecent epochStartOk
      epochStartTimeOk (fun earlier lower beforeCall => historicalSafe earlier lower (Nat.le_trans (Nat.le_of_lt beforeCall) callBound))
      startFacts.2 weights slack late anchorParent nonzero inHorizon
      (fun w hw k state bounded counts epochLe => large w hw k state bounded counts
        (by have := UInt64.le_iff_toNat_le.mp epochLe; omega)) few unslashed supply
        time afterCall bounded
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
          targetVotes slot slotOk (currentRootInside rootSame), slot, begin, slotOk, beginOk,
          atSlot⟩, walkSafe⟩

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

The honest validators vote as their duty asks, and are prompt, up to the last time `limit`.

No duty or slot boundary after `limit` is assumed.

Each other hypothesis on stores, events or signed votes reads only events up to `limit`.

A hypothesis that relates two events bounds both of them.

A signed vote that a hypothesis counts is sent by the time of the counting store's event.

Only synchrony speaks of the whole execution.

The committees of the stores follow the assignment, and the head follows honest support.

Those two facts are parts of issue 1458.

Partial synchrony delivers blocks into views; `BlocksAdmitted` supplies handler admission.

A target with an honest quorum is included within an epoch, Assumption 3.

Up to the horizon, the facts of Casper FFG hold.

The finalized block of an honest store is on the chain of each later justified checkpoint.

Two justified checkpoints of one epoch are the same.

Each counting state bounds Byzantine current-or-previous-epoch voters against its active stake.

This bound gives an honest signer directly, without a reference-state drift.

Each checkpoint state that an honest store reads has at most `stakeCapGwei` of active stake.

That cap, two hundred million ether, keeps the sums of balances that the rule reads within 64 bits.

The boost percentage is at most 100, so the boost of one slot stays within 64 bits too.

The margin covers the drift of such a state from the pulled-up state of a head, over two epochs.

Each block that an honest store holds has a nonzero state root.

No honest store holds a block at the parent root of the anchor block, up to the last time.

This excludes stores that hold that root; it is not an assumption on hashes.

With it, the parents of the blocks of each honest store are at lower slots.

The implementation-level bounds of `RuleBounds` hold, with that margin and a weight shift.

They generalize Assumption 2 of the paper and apply only to calls that confirm by a walk.

Each honest store up to the last time is in an epoch at most the horizon.

The start of the next slot is at most the last time, so every call is before it.

Then the block that the last call stores is safe from the start of the next slot.

It stays safe to the last time.

An execution from an anchor after genesis starts at epoch `a + MIN_SEED_LOOKAHEAD + 1` or later.

Here `a` is the epoch of the anchor state, and `_syncStart` reads the bound in natural numbers.

The bound is the anchor store's genesis time plus the slot length times the slots before that epoch.

Every honest tick is at or after the start, so a store reaches that epoch at its first tick.

Before that epoch a store with only the anchor's history admits no block.

Its boost update reads an ancestor below the anchor's slot, and the anchor's parent is not held.

With `1 ≤ MIN_SEED_LOOKAHEAD`, this is at least two epochs after the anchor.

The anchor need not be finalized, and a genesis anchor needs no such start.

The proof does not use this premise: it only fixes which executions the theorem describes.

The proof is a strong induction on the calls, with `Execution.callInvariant_step`.

In [verified-fast-confirmation][vfc], this is `confirmed_root_safe_from_next_slot`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.safeAt_confirmedRoot {Δ : ℕ} (sync : e.Synchronous Δ)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {limit : ℕ} (votes : Votes e.startTime limit e)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e limit)
    (committees : CommitteesFollow e limit) (follows : HeadFollowsSupport e limit)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e limit) (admitted : BlocksAdmitted e 0 Δ limit)
    (included : TargetIncluded e limit)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    (_syncStart : (getCurrentEpoch anchorState).toNat = 0 ∨
      anchor.genesisTimeMs.toNat + ((getCurrentEpoch anchorState).toNat +
        preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat *
          config.SLOT_DURATION_MS.toNat ≤ e.startTime)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon limit)
    (unique : OneJustifiedPerEpoch e horizon limit)
    {threshold margin : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (headDrifts : ∀ w ∈ J, ∀ n head headState epoch, (e.world n).time ≤ limit →
      ((e.world n).state w).getPulledUpHeadState config head = .ok headState →
      ((e.world n).state w).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ v ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
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
    {shift : ℕ}
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
  -- Every call up to the last time keeps the invariant, by strong induction on its index.
  have invariant : ∀ i n fcr after,
      CallAt e u events (getFastConfirmationStore anchor) i n fcr after →
      (e.world n).time ≤ limit →
      CallInvariant e margin limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro n fcr after calls callBound
      exact e.callInvariant_step sync half boost slots long window lookahead votes fits prompt
        committees
        follows preGloas oneBlock admitted included anchored sound anchorSlot anchorAtBoundary
        start noVotes maxAligned increment chain unique byzantine unslashed supply positive enough
        large nonzero headDrifts caller upToDate lower atSlots bounds inHorizon anchorParent calls
        callBound fun i' lt n' fcr' after' calls' => ih i' lt n' fcr' after' calls'
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
  -- The last call starts its slot, so it is before the following slot and the last time.
  obtain ⟨callSlot, begin, callSlotOk, _, beginOk, atSlot⟩ := atSlots _ n index
  have sameSlot : callSlot = slot := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst callSlot
  have callBound := fits.call_before_next_slot nextOk beginOk followingOk atSlot nonempty
  exact (invariant _ n fcr stored calls (by omega)).1 slot next following slotOk nextOk followingOk

end Models.Network

end EthLib.Consensus
