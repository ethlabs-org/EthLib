module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Statements: a block that the rule confirms stays in the filtered tree of each honest store

This file states step 6 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

The fork choice of a store filters out a block when no leaf above it has a recent voting source.

The rule confirms a block after checks on the checkpoints of its head, and this file names them.

The first statement reads those checks off a call of the rule.

The second bounds the count that the rule makes for the target of its epoch.

Honest validators hold that count: each has voted for the target or has still to vote.

It reads the store of the caller alone, and takes no safety of the target.

The third gives the result, for each honest store at a later time.

It holds the confirmed block in its filtered tree, or its justified block is above that block.

The third statement takes the facts of Casper FFG as hypotheses, with a horizon and a margin.

An honest validator that has still to vote signs the target of its head at its own slot.

Before the later time the block is safe, so that target is on the chain of the block.

So a checkpoint that an honest third signs cannot conflict with the block.

It also takes Assumption 3 of the paper, in the form that `TargetIncluded` gives it here.

The result is a theorem of [verified-fast-confirmation][vfc].

It is `Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

There one registry weighs each count, so a third of the stake is the same in each state.

Here the margin covers the change of the balances between the states of two counts.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The checks that the rule has passed when it confirms a block after the one it starts from.

The start is in the current epoch or the one before.

A block of the current epoch after a start of the epoch before needs the target to be justified.

Away from the start of the epoch, such a block needs more.

The unrealized justification of the head must be recent.

A block of the epoch before needs a recent voting source.

That source is the one of the block, or the one of the head of the slot before.

In the second case the block is on the chain of that head.

Away from the start of the epoch, it also needs that no conflicting checkpoint can be justified.

Then the head, or the head of the slot before, has a recent unrealized justification. -/
def Checked (store : Store preset fork) (config : Config) (fcr : FastConfirmationStore)
    (head start root : Root) : Prop :=
  ∃ epoch slot rootEpoch startEpoch,
    store.getCurrentStoreEpoch config = .ok epoch ∧ store.getCurrentSlot config = .ok slot ∧
    store.getBlockEpoch root = .ok rootEpoch ∧ store.getBlockEpoch start = .ok startEpoch ∧
    epoch.toNat ≤ startEpoch.toNat + 1 ∧
    ((startEpoch.toNat + 1 = epoch.toNat ∧ rootEpoch ≠ epoch ∧
      (∃ source, store.getVotingSource config fcr.previousSlotHead = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2 ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨root, .pending⟩ = .ok true) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
        ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
          store.unrealizedJustification tip = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1)) ∨
      ((isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      (rootEpoch = epoch → startEpoch ≠ epoch →
        store.willCurrentTargetBeJustified config head = .ok true) ∧
      (rootEpoch ≠ epoch →
        (∃ source, store.getVotingSource config root = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2) ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true))))

/-- Reading a later root of a walk cannot decrease the block epoch. -/
private theorem walk_epoch_le {head start root : Root} {roots : List Root}
    {startEpoch rootEpoch : Epoch}
    (walked : store.getAncestorRoots head start = .ok roots) (member : root ∈ roots)
    (startOk : store.getBlockEpoch start = .ok startEpoch)
    (rootOk : store.getBlockEpoch root = .ok rootEpoch) : startEpoch ≤ rootEpoch := by
  obtain ⟨b, t, bOk, tOk, lt⟩ := slot_lt_of_mem_getAncestorRoots walked (by simp) member
  simp [getBlockEpoch, bOk, tOk, bind, Except.bind, pure, Except.pure] at startOk rootOk
  subst startEpoch
  subst rootEpoch
  exact UInt64.le_iff_toNat_le.mpr (by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lt)))

/-- A loop over an increasing walk records a target check whenever it crosses the start epoch. -/
private theorem target_checked_loop {head start init out : Root} {roots : List Root}
    {body : Root → Root → Except ForkChoiceError (ForInStep Root)}
    (walked : store.getAncestorRoots head start = .ok roots)
    (initial : ∀ se ie, store.getBlockEpoch start = .ok se →
      store.getBlockEpoch init = .ok ie → se ≤ ie ∧
        (se ≠ ie → store.willCurrentTargetBeJustified config head = .ok true))
    (step : ∀ x s r, body x s = .ok r →
      r = .done s ∨ r = .yield x ∧
        ∃ se, store.getBlockEpoch s = .ok se ∧
          ∀ xe, store.getBlockEpoch x = .ok xe →
            (se < xe → store.willCurrentTargetBeJustified config head = .ok true))
    (looped : forIn roots init body = .ok out) :
    ∀ se oe, store.getBlockEpoch start = .ok se → store.getBlockEpoch out = .ok oe →
      se ≤ oe ∧ (se ≠ oe → store.willCurrentTargetBeJustified config head = .ok true) := by
  apply forIn_ok_invariant (fun _ s => ∀ se ie, store.getBlockEpoch start = .ok se →
    store.getBlockEpoch s = .ok ie → se ≤ ie ∧
      (se ≠ ie → store.willCurrentTargetBeJustified config head = .ok true))
    _ initial ?_ ?_ (fun _ h => h) looped
  · intro read x rest s s' split holds stepped
    rcases step x s _ stepped with stopped | ⟨went, ie, oldOk, crossed⟩
    · cases stopped
    obtain rfl := ForInStep.yield.inj went
    intro se xe startOk xOk
    have le := walk_epoch_le walked (split ▸ (by simp)) startOk xOk
    refine ⟨le, ?_⟩
    intro different
    -- A successful step reads the old state epoch before it can yield.
    by_cases checked : store.willCurrentTargetBeJustified config head = .ok true
    · exact checked
    have old := holds se ie startOk oldOk
    have same : se = ie := by
      by_contra different
      exact checked (old.2 different)
    subst ie
    exact crossed xe xOk (UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.le_iff_toNat_le.mp le
      have := mt UInt64.toNat_inj.mp different
      omega))
  · intro read x rest s s' split holds stepped
    rcases step x s _ stepped with stopped | ⟨went, crossed⟩
    · exact ForInStep.done.inj stopped ▸ holds
    · cases went

/-- The descendant search checks the same start that its caller selected. -/
theorem findLatestConfirmedDescendant_checked {fcr : FastConfirmationStore}
    {head start root : Root} (_lower : store.ParentsBelow)
    (recent : ∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
      store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1)
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨ store.Checked config fcr head start root := by
  unfold findLatestConfirmedDescendant at found
  rw [bind_ok_iff] at found
  obtain ⟨epoch, epochOk, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨slot, slotOk, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨atStart, atStartOk, found⟩ := found
  extract_lets arith recentCheck source tally confirmedRoot finish current previous at found
  have notStart (h : isStartSlotAtEpoch preset slot = .ok false) : atStart = false :=
    Except.ok.inj (atStartOk.symm.trans h)
  have recentNat {e : Epoch} {gap : UInt64}
      (checked : recentCheck e gap = .ok true) : epoch.toNat ≤ e.toNat + gap.toNat := by
    simp only [recentCheck, arith, bind_ok_iff] at checked
    obtain ⟨sum, sumOk, checked⟩ := checked
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    have le : epoch ≤ sum := by simpa [pure, Except.pure] using checked.symm
    have := UInt64.le_iff_toNat_le.mp le
    omega
  let previousChecks (mid : Root) : Prop :=
    ∃ se, store.getBlockEpoch start = .ok se ∧
      (mid = start ∨ ∃ me source, store.getBlockEpoch mid = .ok me ∧
        se.toNat + 1 = epoch.toNat ∧ me ≠ epoch ∧
        store.getVotingSource config fcr.previousSlotHead = .ok source ∧
        epoch.toNat ≤ source.epoch.toNat + 2 ∧
        store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨mid, .pending⟩ = .ok true ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
          ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
            store.unrealizedJustification tip = .ok justification ∧
            epoch.toNat ≤ justification.epoch.toNat + 1))
  -- The gates of the first walk supply checks shared by every root that it accepts.
  have reach : ∃ previousEpochOk se, store.getBlockEpoch start = .ok se ∧
      (previousEpochOk = true →
        se.toNat + 1 = epoch.toNat ∧
        ∃ votingSource, store.getVotingSource config fcr.previousSlotHead = .ok votingSource ∧
          epoch.toNat ≤ votingSource.epoch.toNat + 2 ∧
          (isStartSlotAtEpoch preset slot = .ok false →
            store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
            ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
              store.unrealizedJustification tip = .ok justification ∧
              epoch.toNat ≤ justification.epoch.toNat + 1)) ∧
      previous previousEpochOk = .ok root := by
    clear_value previous
    simp only [bind_ok_iff] at found
    obtain ⟨se, seOk, sum, sumOk, found⟩ := found
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    split at found
    · exact ⟨false, se, seOk, by simp, found⟩
    · rename_i same
      have seValue : se.toNat + 1 = epoch.toNat := by
        have equal : sum = epoch := by simpa using same
        subst sum
        simpa using sumValue.symm
      simp only [bind_ok_iff] at found
      obtain ⟨votingSource, votingOk, sourceRecent, sourceRecentOk, found⟩ := found
      split at found
      · exact ⟨false, se, seOk, by simp, found⟩
      · rename_i sourcePass
        have sourceBound : epoch.toNat ≤ votingSource.epoch.toNat + 2 :=
          recentNat (by have pass : sourceRecent = true := by simpa using sourcePass
                        exact pass ▸ sourceRecentOk)
        split at found
        · rename_i firstSlot
          refine ⟨true, se, seOk, fun _ => ⟨seValue, votingSource, votingOk, sourceBound, ?_⟩,
            found⟩
          intro h
          have := notStart h
          simp_all
        · simp only [bind_ok_iff] at found
          obtain ⟨noConflict, noConflictOk, found⟩ := found
          split at found
          · exact ⟨false, se, seOk, by simp, found⟩
          · rename_i noConflictPass
            have noConflictOk : store.willNoConflictingCheckpointBeJustified config head =
                .ok true := by
              have pass : noConflict = true := by simpa using noConflictPass
              exact pass ▸ noConflictOk
            simp only [bind_ok_iff] at found
            obtain ⟨justification, justificationOk, justificationRecent, justificationRecentOk,
              found⟩ := found
            split at found
            · rename_i justificationPass
              refine ⟨true, se, seOk, fun _ => ⟨seValue, votingSource, votingOk, sourceBound,
                fun _ => ⟨noConflictOk, fcr.previousSlotHead, justification, Or.inr rfl,
                  justificationOk, ?_⟩⟩, found⟩
              exact recentNat (justificationPass ▸ justificationRecentOk)
            · simp only [bind_ok_iff] at found
              obtain ⟨headJustification, headJustificationOk, headRecent, headRecentOk, found⟩ :=
                found
              refine ⟨headRecent, se, seOk, fun passed => ⟨seValue, votingSource, votingOk,
                sourceBound, fun _ => ⟨noConflictOk, head, headJustification, Or.inl rfl,
                  headJustificationOk, ?_⟩⟩, found⟩
              exact recentNat (passed ▸ headRecentOk)
  clear found
  obtain ⟨previousEpochOk, se, seOk, previousOk, found⟩ := reach
  -- Each accepted root adds its own epoch and ancestry checks to those shared checks.
  have first : ∃ mid, previousChecks mid ∧ current () mid = .ok root := by
    simp only [previous] at found
    split at found
    · rename_i passed
      obtain ⟨seValue, votingSource, votingOk, sourceBound, boundary⟩ := previousOk passed
      rw [bind_ok_iff] at found
      obtain ⟨walk, walked, found⟩ := found
      rw [bind_ok_iff] at found
      obtain ⟨mid, looped, found⟩ := found
      refine ⟨mid, ⟨se, seOk, ?_⟩, found⟩
      have accepted := forIn_ok_last_kept (kept := fun x => ∃ me,
          store.getBlockEpoch x = .ok me ∧ me ≠ epoch ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨x, .pending⟩ = .ok true) (by
        intro x s r stepped
        rw [bind_ok_iff] at stepped
        obtain ⟨me, meOk, stepped⟩ := stepped
        split at stepped
        · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
        · rename_i different
          rw [bind_ok_iff] at stepped
          obtain ⟨onChain, onChainOk, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · rename_i onChainPass
            simp only [bind_ok_iff] at stepped
            obtain ⟨_, -, _, -, confirmed, confirmedOk, stepped⟩ := stepped
            split at stepped
            · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
            · exact Or.inr ⟨by simpa [pure, Except.pure] using stepped.symm,
                me, meOk, different, by simp_all⟩) looped
      rcases accepted with same | ⟨before, after, split, all⟩
      · exact Or.inl same
      · obtain ⟨me, meOk, different, ancestry⟩ := all mid (by simp)
        exact Or.inr ⟨me, votingSource, meOk, seValue, different, votingOk, sourceBound,
          ancestry, boundary⟩
    · exact ⟨start, ⟨se, seOk, Or.inl rfl⟩, found⟩
  clear found
  obtain ⟨mid, firstChecks, found⟩ := first
  have firstResult : mid = start ∨ store.Checked config fcr head start mid := by
    obtain ⟨se, seOk, same | ⟨me, source, meOk, seValue, different, sourceOk,
      sourceBound, ancestry, boundary⟩⟩ := firstChecks
    · exact Or.inl same
    · exact Or.inr ⟨epoch, slot, me, se, epochOk, slotOk, meOk, seOk,
        recent epoch se epochOk seOk, Or.inl ⟨seValue, different,
          ⟨source, sourceOk, sourceBound, ancestry⟩, boundary⟩⟩
  simp -zeta only [current] at found
  extract_lets tentative currentBody at found
  have reach : ∃ currentEpochOk,
      (currentEpochOk = true → isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      currentBody currentEpochOk = .ok root := by
    clear_value currentBody
    split at found
    · rename_i firstSlot
      refine ⟨true, fun _ h => ?_, found⟩
      have := notStart h
      simp_all
    · simp only [bind_ok_iff] at found
      obtain ⟨justification, justificationOk, verdict, verdictOk, found⟩ := found
      exact ⟨verdict, fun h _ => ⟨justification, justificationOk,
        recentNat (h ▸ verdictOk)⟩, found⟩
  clear found
  obtain ⟨currentEpochOk, currentChecks, found⟩ := reach
  simp -zeta only [currentBody] at found
  split at found
  · rename_i passed
    rw [bind_ok_iff] at found
    obtain ⟨walk, walked, found⟩ := found
    rw [bind_ok_iff] at found
    obtain ⟨last, looped, found⟩ := found
    extract_lets tentativeRoot accepted acceptBody at found
    change store.getBlockEpoch last >>= _ = .ok root at found
    rw [bind_ok_iff] at found
    obtain ⟨lastEpoch, lastEpochOk, found⟩ := found
    -- Rejection restores the first walk's result, not the tentative result of the second walk.
    have acceptedResult : root = mid ∨ root = last ∧
        (lastEpoch ≠ epoch →
          (∃ source, store.getVotingSource config last = .ok source ∧
            epoch.toNat ≤ source.epoch.toNat + 2) ∧
          (isStartSlotAtEpoch preset slot = .ok false →
            store.willNoConflictingCheckpointBeJustified config head = .ok true)) := by
      have finishResult {accept : Bool} (ended : acceptBody accept = .ok root) :
          (accept = true ∧ root = last) ∨ (accept = false ∧ root = mid) := by
        simp only [acceptBody, finish] at ended
        split at ended
        · exact Or.inl ⟨by assumption, by simpa [pure, Except.pure, tentativeRoot, accepted]
            using ended.symm⟩
        · rename_i notAccepted
          have rejected : accept = false := Bool.eq_false_iff.mpr notAccepted
          exact Or.inr ⟨rejected, by simpa [pure, Except.pure] using ended.symm⟩
      split at found
      · rename_i isCurrent
        simp only [pure, Except.pure, bind, Except.bind] at found
        rcases finishResult (accept := true) found with ⟨_, same⟩ | ⟨bad, _⟩
        · exact Or.inr ⟨same, fun h => False.elim (h isCurrent)⟩
        · cases bad
      · rw [bind_ok_iff] at found
        obtain ⟨votingSource, votingOk, found⟩ := found
        rw [bind_ok_iff] at found
        obtain ⟨sourceRecent, sourceRecentOk, found⟩ := found
        split at found
        · simp only [pure, Except.pure, bind, Except.bind] at found
          rcases finishResult (accept := false) found with ⟨bad, _⟩ | ⟨_, same⟩
          · cases bad
          · exact Or.inl same
        · rename_i recentPass
          have pass : sourceRecent = true := by simpa using recentPass
          have bound := recentNat (pass ▸ sourceRecentOk)
          split at found
          · rename_i firstSlot
            simp only [pure, Except.pure, bind, Except.bind] at found
            rcases finishResult (accept := true) found with ⟨_, same⟩ | ⟨bad, _⟩
            · refine Or.inr ⟨same, fun _ => ⟨⟨votingSource, votingOk, bound⟩, ?_⟩⟩
              intro h
              have := notStart h
              simp_all
            · cases bad
          · rw [bind_ok_iff] at found
            obtain ⟨accept, acceptOk, found⟩ := found
            rcases finishResult found with ⟨rfl, same⟩ | ⟨_, same⟩
            · exact Or.inr ⟨same, fun _ => ⟨⟨votingSource, votingOk, bound⟩,
                fun _ => acceptOk⟩⟩
            · exact Or.inl same
    rcases acceptedResult with rfl | ⟨rfl, acceptedChecks⟩
    · exact firstResult
    · have target := target_checked_loop (config := config) walked (by
        intro me ie meOk ieOk
        have same : me = ie := Except.ok.inj (meOk.symm.trans ieOk)
        subst ie
        exact ⟨UInt64.le_refl _, by simp⟩) (by
        intro x s r stepped
        simp only [bind_ok_iff] at stepped
        obtain ⟨xe, xeOk, se, oldOk, stepped⟩ := stepped
        split at stepped
        · rename_i crosses
          rw [bind_ok_iff] at stepped
          obtain ⟨check, checkOk, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · rename_i checkPass
            simp only [bind_ok_iff] at stepped
            obtain ⟨_, -, _, -, _, -, stepped⟩ := stepped
            split at stepped
            · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
            · refine Or.inr ⟨by simpa [pure, Except.pure] using stepped.symm, se, oldOk, ?_⟩
              intro _ _ _
              simp_all
        · rename_i noCross
          simp only [bind_ok_iff] at stepped
          obtain ⟨_, -, _, -, _, -, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · refine Or.inr ⟨by simpa [pure, Except.pure] using stepped.symm, se, oldOk, ?_⟩
            intro other otherOk lt
            obtain rfl : xe = other := Except.ok.inj (xeOk.symm.trans otherOk)
            exact absurd lt noCross) looped
      obtain ⟨se, seOk, firstCases⟩ := firstChecks
      have startToMid : ∃ me, store.getBlockEpoch mid = .ok me := by
        rcases firstCases with rfl | ⟨me, source, meOk, rest⟩
        · exact ⟨se, seOk⟩
        · exact ⟨me, meOk⟩
      obtain ⟨me, meOk⟩ := startToMid
      have lastTarget := target me lastEpoch meOk lastEpochOk
      refine Or.inr ⟨epoch, slot, lastEpoch, se, epochOk, slotOk, lastEpochOk, seOk,
        recent epoch se epochOk seOk, Or.inr ⟨currentChecks passed, ?_, acceptedChecks⟩⟩
      intro lastCurrent startDifferent
      have midDifferent : me ≠ lastEpoch := by
        intro same
        subst me
        rcases firstCases with same | ⟨_, _, midOk, seValue, midNotCurrent, _⟩
        · subst mid
          have := Except.ok.inj (seOk.symm.trans meOk)
          exact startDifferent (this.trans lastCurrent)
        · have := Except.ok.inj (midOk.symm.trans meOk)
          exact midNotCurrent (this.trans lastCurrent)
      exact lastTarget.2 midDifferent
  · have same : root = mid := by simpa [finish, pure, Except.pure] using found.symm
    exact same ▸ firstResult

/-- The selected start carries both its reset checks and its descendant search.

The start is the one that the rule selects, not only one of its three candidates.

The rule first keeps the block stored before, when that block passes three checks.

Its epoch is the current one or the one before.

It is on the chain of the head.

At the start of an epoch, its chain is still safe.

Otherwise the rule falls back to the finalized block.

Call the block that this step gives the base.

The rule then takes the observed justified block in place of the base, when four checks pass.

The slot starts an epoch, and the observed block is of the epoch before.

The observed checkpoint is the unrealized justification of the head.

The base is at an earlier slot than the observed block.

Otherwise the start is the base.

These cases exclude one another, so the start is the one that the rule computes. -/
theorem getLatestConfirmed_checked_start {fcr : FastConfirmationStore} {head root : Root}
    (lower : store.ParentsBelow)
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      (∃ base,
        (base = fcr.confirmedRoot ∧
            ((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)) ∨
          base = store.finalizedCheckpoint.root ∧
            ¬((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true))) ∧
        (start = base ∧
            ¬(isStartSlotAtEpoch preset slot = .ok true ∧
              (∃ observedBlock epoch,
                store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
                store.getCurrentStoreEpoch config = .ok epoch ∧
                Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
              store.unrealizedJustification head =
                .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
              ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
                baseBlock.slot < observedBlock.slot) ∨
          start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
            isStartSlotAtEpoch preset slot = .ok true ∧
            (∃ observedBlock epoch,
              store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
              store.getCurrentStoreEpoch config = .ok epoch ∧
              Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
            store.unrealizedJustification head =
              .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
            ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
              store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
              baseBlock.slot < observedBlock.slot)) ∧
      (root = start ∨ store.Checked config fcr head start root ∧
        store.findLatestConfirmedDescendant config fcr head start = .ok root) := by
  unfold getLatestConfirmed at latest
  rw [bind_ok_iff] at latest
  obtain ⟨currentEpoch, epochFound, latest⟩ := latest
  rw [bind_ok_iff] at latest
  obtain ⟨slot, slotFound, latest⟩ := latest
  refine ⟨slot, ?_⟩
  extract_lets arith confirmedRoot observed finish observedRoot afterReset finalizedRoot
    resetBody at latest
  -- The three checks that keep the block stored before.
  let kept : Prop :=
    (∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
      store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
      epoch.toNat ≤ blockEpoch.toNat + 1) ∧
    store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
    (isStartSlotAtEpoch preset slot = .ok true →
      store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)
  -- Keep the reset decision paired with the continuation that consumes it.
  have reset : ∃ reset, (reset = false → kept) ∧ (reset = true → ¬kept) ∧
      resetBody reset = .ok root := by
    clear_value resetBody
    rw [bind_ok_iff] at latest
    obtain ⟨blockEpoch, blockEpochOk, latest⟩ := latest
    rw [bind_ok_iff] at latest
    obtain ⟨sum, sumOk, latest⟩ := latest
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    simp only [UInt64.toNat_one] at sumValue
    -- The epoch check of `kept` is the negation of the staleness test of the rule.
    have epochCheck : (∃ epoch be, store.getCurrentStoreEpoch config = .ok epoch ∧
        store.getBlockEpoch fcr.confirmedRoot = .ok be ∧ epoch.toNat ≤ be.toNat + 1) ↔
        ¬sum < currentEpoch := by
      constructor
      · rintro ⟨epoch, be, epochOk, beOk, le⟩ stale
        obtain rfl : currentEpoch = epoch := Except.ok.inj (epochFound.symm.trans epochOk)
        obtain rfl : blockEpoch = be := Except.ok.inj (blockEpochOk.symm.trans beOk)
        have := UInt64.lt_iff_toNat_lt.mp stale
        omega
      · intro fresh
        have := UInt64.not_lt.mp fresh
        refine ⟨currentEpoch, blockEpoch, epochFound, blockEpochOk, ?_⟩
        have := UInt64.le_iff_toNat_le.mp this
        omega
    split at latest
    · rename_i stale
      exact ⟨true, by simp, fun _ held => epochCheck.mp held.1 stale, latest⟩
    · rename_i fresh
      rw [bind_ok_iff] at latest
      obtain ⟨onChain, ancestry, latest⟩ := latest
      split at latest
      · rename_i offChain
        refine ⟨true, by simp, fun _ held => ?_, latest⟩
        have same := Except.ok.inj (ancestry.symm.trans held.2.1)
        simp [same] at offChain
      · rename_i isOnChain
        obtain rfl : onChain = true := by simpa using isOnChain
        rw [bind_ok_iff] at latest
        obtain ⟨atStart, startChecked, latest⟩ := latest
        split at latest
        · rename_i startTrue
          obtain rfl : atStart = true := by simpa using startTrue
          rw [bind_ok_iff] at latest
          obtain ⟨safe, chainChecked, latest⟩ := latest
          refine ⟨!safe, fun notReset => ⟨epochCheck.mpr fresh, ancestry, fun _ => ?_⟩,
            fun isReset held => ?_, latest⟩
          · obtain rfl : safe = true := by simpa using notReset
            exact chainChecked
          · have same := Except.ok.inj (chainChecked.symm.trans (held.2.2 startChecked))
            simp [same] at isReset
        · rename_i notStart
          refine ⟨false, fun _ => ⟨epochCheck.mpr fresh, ancestry, fun isStart => ?_⟩,
            by simp, latest⟩
          exact absurd (Except.ok.inj (startChecked.symm.trans isStart)) (by simpa using notStart)
  clear latest
  obtain ⟨reset, keeps, drops, latest⟩ := reset
  have base : ∃ base, (base = fcr.confirmedRoot ∧ kept ∨
      base = store.finalizedCheckpoint.root ∧ ¬kept) ∧ afterReset () base = .ok root := by
    cases reset
    · exact ⟨fcr.confirmedRoot, Or.inl ⟨rfl, keeps rfl⟩, latest⟩
    · exact ⟨store.finalizedCheckpoint.root, Or.inr ⟨rfl, drops rfl⟩, latest⟩
  clear latest keeps drops
  obtain ⟨base, baseCase, latest⟩ := base
  -- The observed checkpoint replaces this base exactly when all four replacement checks pass.
  let over : Prop :=
    isStartSlotAtEpoch preset slot = .ok true ∧
    (∃ observedBlock epoch,
      store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
      store.getCurrentStoreEpoch config = .ok epoch ∧
      Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
    store.unrealizedJustification head = .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
    ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
      store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
      baseBlock.slot < observedBlock.slot
  have start : ∃ start, (start = base ∧ ¬over ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧ over) ∧
      finish () start = .ok root := by
    clear_value finish
    simp only [afterReset, bind_ok_iff] at latest
    obtain ⟨atStart, startChecked, observedBlock, observedFound, observedEpoch, epochAdded,
      justified, justification, baseBlock, baseFound, latest⟩ := latest
    split at latest
    · rename_i replaced
      refine ⟨observedRoot, Or.inr ⟨rfl, replaced.1 ▸ startChecked,
        ⟨observedBlock, currentEpoch, observedFound, epochFound,
          replaced.2.1 ▸ mapError_ok_iff.mp epochAdded⟩,
        justification.trans (congrArg Except.ok replaced.2.2.1.symm),
        baseBlock, observedBlock, baseFound, observedFound, replaced.2.2.2⟩, latest⟩
    · rename_i kept'
      refine ⟨base, Or.inl ⟨rfl, ?_⟩, latest⟩
      rintro ⟨isStart, ⟨ob, epoch, obFound, epochOk, added⟩, headJustified, bb, ob', bbFound,
        ob'Found, lower'⟩
      apply kept'
      obtain rfl : atStart = true := Except.ok.inj (startChecked.symm.trans isStart)
      obtain rfl : ob = observedBlock := Except.ok.inj (obFound.symm.trans observedFound)
      obtain rfl : ob' = ob := Except.ok.inj (ob'Found.symm.trans obFound)
      obtain rfl : bb = baseBlock := Except.ok.inj (bbFound.symm.trans baseFound)
      obtain rfl : epoch = currentEpoch := Except.ok.inj (epochOk.symm.trans epochFound)
      have sameEpoch : observedEpoch = epoch :=
        Except.ok.inj ((mapError_ok_iff.mp epochAdded).symm.trans added)
      have sameJustified : justified = fcr.currentEpochObservedJustifiedCheckpoint :=
        Except.ok.inj (justification.symm.trans headJustified)
      exact ⟨rfl, sameEpoch, sameJustified.symm, lower'⟩
  clear latest
  obtain ⟨start, startCase, latest⟩ := start
  refine ⟨start, slotFound, ⟨base, baseCase, startCase⟩, ?_⟩
  simp only [finish, bind_ok_iff] at latest
  obtain ⟨startEpoch, startOk, sum, sumOk, latest⟩ := latest
  split at latest
  · rename_i recentStart
    have recent : ∀ epoch se, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok se → epoch.toNat ≤ se.toNat + 1 := by
      intro epoch se epochOk seOk
      obtain rfl : currentEpoch = epoch := Except.ok.inj (epochFound.symm.trans epochOk)
      obtain rfl : startEpoch = se := Except.ok.inj (startOk.symm.trans seOk)
      have value := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
      have le := UInt64.le_iff_toNat_le.mp recentStart
      simp only [UInt64.toNat_one] at value
      omega
    rcases findLatestConfirmedDescendant_checked lower recent latest with same | checked
    · exact Or.inl same
    · exact Or.inr ⟨checked, latest⟩
  · exact Or.inl (Except.ok.inj latest).symm

/-- Step 6, the checks: the latest confirmed block is a start, or has passed the checks.

The start is the block stored before, the finalized block or the observed justified block.

Each known block must sit at a later slot than its known parent.

The proof reads the two walks of the rule, as `findLatestConfirmedDescendant_eq_or` does.

Two witnesses of [verified-fast-confirmation][vfc] hold the same checks.

They are `PreviousSelectedEntryWitness` and `TentativeSelectedResultWitness`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem getLatestConfirmed_checked {fcr : FastConfirmationStore} {head root : Root}
    (lower : store.ParentsBelow)
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ start, (start = fcr.confirmedRoot ∨ start = store.finalizedCheckpoint.root ∨
        start = fcr.currentEpochObservedJustifiedCheckpoint.root) ∧
      (root = start ∨ store.Checked config fcr head start root) := by
  obtain ⟨slot, start, _, ⟨base, baseCase, startCase⟩, result⟩ :=
    getLatestConfirmed_checked_start lower latest
  refine ⟨start, ?_, result.imp id And.left⟩
  rcases startCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · rcases baseCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- A successful target check supplies a two-thirds bound in its counting state. -/
theorem two_thirds_le_of_willCurrentTargetBeJustified {head : Root}
    (checked : store.willCurrentTargetBeJustified config head = .ok true) :
    ∃ state total support,
      store.getPulledUpHeadState config head = .ok state ∧
      getTotalActiveBalance state = .ok total ∧
      store.computeHonestFfgSupportForCurrentTarget config head = .ok support ∧
      2 * total.toNat ≤ 3 * support.toNat := by
  simp only [willCurrentTargetBeJustified, bind_ok_iff, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at checked
  obtain ⟨state, stateOk, total, totalOk, support, supportOk, doubled, doubledOk,
    tripled, tripledOk, bound⟩ := checked
  have two := (mulChecked_ok_iff.mp doubledOk).2
  have three := (mulChecked_ok_iff.mp tripledOk).2
  have le : doubled.toNat ≤ tripled.toNat :=
    UInt64.le_iff_toNat_le.mp (of_decide_eq_true bound)
  refine ⟨state, total, support, stateOk, totalOk, supportOk, ?_⟩
  simpa only [two, three, UInt64.toNat_ofNat] using le

/-- A no-conflict check either names a justified target or supplies a strict one-third bound. -/
theorem justified_or_one_third_lt_of_willNoConflictingCheckpointBeJustified {head : Root}
    (checked : store.willNoConflictingCheckpointBeJustified config head = .ok true) :
    store.getCurrentTarget config head = .ok store.unrealizedJustifiedCheckpoint ∨
      ∃ state total support,
        store.getPulledUpHeadState config head = .ok state ∧
        getTotalActiveBalance state = .ok total ∧
        store.computeHonestFfgSupportForCurrentTarget config head = .ok support ∧
        total.toNat < 3 * support.toNat := by
  simp only [willNoConflictingCheckpointBeJustified, bind_ok_iff] at checked
  obtain ⟨target, targetOk, checked⟩ := checked
  split at checked
  · rename_i same
    exact .inl (same ▸ targetOk)
  · simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at checked
    obtain ⟨state, stateOk, total, totalOk, support, supportOk, tripled, tripledOk,
      bound⟩ := checked
    have three := (mulChecked_ok_iff.mp tripledOk).2
    have lt : total.toNat < tripled.toNat :=
      UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true bound)
    refine .inr ⟨state, total, support, stateOk, totalOk, supportOk, ?_⟩
    simpa only [three, UInt64.toNat_ofNat] using lt

/-- A successful target-support count is the discounted score plus the remaining honest share. -/
theorem computeHonestFfgSupportForCurrentTarget_eq
    {head : Root} {state : BeaconState preset fork} {slot epochStart lastSlot : Slot}
    {total soFar support : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (slotOk : store.getCurrentSlot config = .ok slot)
    (totalOk : getTotalActiveBalance state = .ok total)
    (startOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (soFarOk : store.computeCommitteeWeightBetweenSlots head state epochStart lastSlot = .ok soFar)
    (supportOk : store.computeHonestFfgSupportForCurrentTarget config head = .ok support) :
    ∃ score adversary,
      store.getCurrentTargetScore config head = .ok score ∧
      store.computeAdversarialWeight config head state epochStart lastSlot = .ok adversary ∧
      support.toNat = score.toNat - adversary.toNat +
        (total.toNat - soFar.toNat) / 100 *
          (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
  simp only [computeHonestFfgSupportForCurrentTarget, slotOk, stateOk,
    mapError_ok_iff, bind_ok_iff] at supportOk
  obtain ⟨s, sOk, st, stOk, t, tOk, score, scoreOk, first, firstOk, last, lastOk',
    weight, weightOk, remaining, remainingOk, share, shareOk, future, futureOk,
    adversary, adversaryOk, sumOk⟩ := supportOk
  cases Except.ok.inj sOk
  cases Except.ok.inj stOk
  rw [totalOk, Except.ok.injEq] at tOk
  subst t
  rw [startOk, Except.ok.injEq] at firstOk
  subst first
  rw [lastOk, Except.ok.injEq] at lastOk'
  subst last
  rw [soFarOk, Except.ok.injEq] at weightOk
  subst weight
  have remainingNat := (subChecked_ok_iff.mp remainingOk).2
  have shareNat := (subChecked_ok_iff.mp shareOk).2
  have futureNat := (mulChecked_ok_iff.mp futureOk).2
  have sumNat := (addChecked_ok_iff.mp sumOk).2
  refine ⟨score, adversary, scoreOk, adversaryOk, ?_⟩
  simpa only [toNat_saturatingSub, futureNat, UInt64.toNat_div, remainingNat, shareNat,
    UInt64.toNat_ofNat] using sumNat

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- Honest validators hold the count that the rule makes for the target of a head, with a margin.

The store is that of a validator at an event, and the head is a block of it.

The rule counts the honest votes that the target of the current epoch will get, at the least.

Some honest validators are active in the pulled-up state of the head.

Each has signed a vote with that target, or is in no committee of the epoch so far.

Three times their stake is at least three times the count plus the margin.

The stake is read in the pulled-up state of the head.

In [verified-fast-confirmation][vfc], `noConflict_arithmeticBranch_oneThird` gives this set.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def HonestTargetVotes
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (margin : ℕ) (u : ValidatorIndex) (n : ℕ) (head : Root) : Prop :=
  ∀ state support target slot epochStart lastSlot participants,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    ((e.world n).state u).computeHonestFfgSupportForCurrentTarget config head = .ok support →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
    subChecked slot 1 = .ok lastSlot →
    ((e.world n).state u).getCommitteesBetweenSlots head epochStart lastSlot = .ok participants →
    ∃ voters : Finset ValidatorIndex,
      (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
        (SignsTarget e v target (e.world n).time ∨ v ∉ participants)) ∧
      3 * support.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters

/-- Assumption 3 of the paper: a target with an honest quorum is included within an epoch.

An honest store counts honest votes for the checkpoint of an epoch on the chain of a block.

Two thirds of the active balance of the pulled-up state of a head sign that target.

Their votes are sent by the time of the counting store's event.

The block is safe from a first time on.

Take an honest store that is up to date at that time or later.

Its epoch is two epochs after the target or later.

It holds a block above the given one, of an epoch before that, with the target included.

Included means that the unrealized justification of that block is not before the target.

Both stores are at events up to the last time `limit`.

In [verified-fast-confirmation][vfc], this is `EventualCheckpointInclusion.included`.

Its conclusion there is `A32IncludedAtTip`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetIncluded
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (limit : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n, (e.world n).time ≤ limit →
    ∀ head state total root rootEpoch target, ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
    rootEpoch ≤ target.epoch →
    ((e.world n).state u).getCheckpointBlock root target.epoch = .ok target.root →
    (∀ v ∈ voters, v ∈ J ∧ SignsTarget e v target (e.world n).time) →
    2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit → (e.world n).time ≤ (e.world k).time →
      (∀ time, (e.world n).time ≤ time → time < (e.world k).time → SafeAt e time root) →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
      target.epoch.toNat + 2 ≤ current.toNat →
      ∃ (seed : Root) (seedBlock : BeaconBlock preset fork) (justification : Checkpoint),
        ((e.world k).state w).blocks[seed]? = some seedBlock ∧
        ((e.world k).state w).isAncestor ⟨seed, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
        (computeEpochAtSlot preset seedBlock.slot).toNat < target.epoch.toNat + 2 ∧
        ((e.world k).state w).unrealizedJustifications[seed]? = some justification ∧
        target.epoch.toNat ≤ justification.epoch.toNat

/-- A block extends an origin whose target the rule checked in the block's epoch.

The origin and the block have the same epoch, which can precede the current epoch.

The anchor is an origin without a target check.

For any other origin, an earlier up-to-date call checked a head above that origin.

There the rule found that the target of the epoch will be justified.

Honest validators held the count of the rule for that target, with the margin.

The origin is safe from that event to the later one.

A later block need not have existed at the event that checked the origin.

A call of the rule makes that check only when it enters the epoch.

A later call that starts from a block of the epoch relies on the earlier check.

In [verified-fast-confirmation][vfc], `AcceptedHistoricalA32CurrentLineageAt` holds this record.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetChecked
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (margin : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (epoch : Epoch) (root : Root) : Prop :=
  ∃ k ≤ n, ∃ origin,
    ((e.world n).state u).getBlockEpoch root = .ok epoch ∧
    ((e.world n).state u).getBlockEpoch origin = .ok epoch ∧
    ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
    (origin = anchorRoot ∨ ∃ head,
      UpToDate config checks sources (e.world k).time ((e.world k).view u) ((e.world k).state u) ∧
      ((e.world k).state u).getCurrentStoreEpoch config = .ok epoch ∧
      ((e.world k).state u).getHead config = .ok head ∧
      ((e.world k).state u).willCurrentTargetBeJustified config head.root = .ok true ∧
      ((e.world k).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
      HonestTargetVotes e margin u k head.root) ∧
    ∀ time, (e.world k).time ≤ time → time ≤ (e.world n).time → SafeAt e time origin

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

omit [DecidablePred (· ∈ J)] in
/-- Inclusion up to a time gives inclusion up to every earlier time. -/
theorem TargetIncluded.of_le {last later : ℕ} (included : TargetIncluded e later)
    (le : last ≤ later) : TargetIncluded e last :=
  fun u caller n nBound head state total root rootEpoch target voters stateOk totalOk epochOk
    rootEpochOk rootLe blockOk signed quorum w receiver k current kBound =>
    included u caller n (nBound.trans le) head state total root rootEpoch target voters stateOk
      totalOk epochOk rootEpochOk rootLe blockOk signed quorum w receiver k current
      (kBound.trans le)

omit [DecidablePred (· ∈ J)] in
/-- A latest vote's checkpoint target has been signed by the event that holds the vote. -/
theorem Execution.signsTarget_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {n : ℕ} {v : ValidatorIndex} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message)
    {target : Checkpoint}
    (targetOk : ((e.world n).state u).getCheckpointForBlock message.root
      (getLatestMessageEpoch preset message) = .ok target) :
    SignsTarget e v target (e.world n).time := by
  obtain ⟨attestation, m, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start caller found
  have epoch : getLatestMessageEpoch preset message = attestation.data.target.epoch := by
    rw [same]
    unfold getLatestMessageEpoch LatestMessage.ofAttestation
    split
    · exact origin.targetEpoch.symm
    · rfl
  have root : message.root = attestation.data.beaconBlockRoot := by rw [same]; rfl
  rw [epoch, root] at targetOk
  have targetEq : attestation.data.target = target := by
    simpa [Store.getCheckpointForBlock, origin.targetRoot] using targetOk
  exact ⟨n, le_rfl, m, e.view_subset_sent n u seen, attestation.data, signed, targetEq⟩

/-- Step 6, the count: honest validators hold the count of the rule for the target, with a margin.

The caller is an honest validator, and each honest store starts from the store of the anchor.

Each latest vote of an honest validator in the store of the caller is a vote that it signed.

The Byzantine validators hold at most β of the committees of the epoch so far, Assumption 2.

So the votes for the target less the weight of the adversary are honest votes.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

The stake is read in the pulled-up state of the head.

The statement reads the store of the caller alone, and takes no safety of the target.

The RANDAO buffer is longer than the lower seed lookahead plus one, as `CommitteesFollow` asks.

The proof follows two lemmas of [verified-fast-confirmation][vfc].

The first is `noConflict_arithmeticBranch_oneThird`.

The second is `currentTarget_remaining_honest_le_future_weight`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honestTargetVotes_of_byzantineStakeAtMost {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {limit : ℕ} (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) {margin : ℕ}
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ limit)
    {head : Root} {state : BeaconState preset fork}
    {slot epochStart lastSlot : Slot} {total soFar : Gwei}
    {participants : Std.TreeSet ValidatorIndex}
    (headOk : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (totalOk : getTotalActiveBalance state = .ok total)
    (aligned : EffectiveBalancesAligned state)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (startOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (soFarOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head state epochStart
      lastSlot = .ok soFar)
    (participantsOk : ((e.world n).state u).getCommitteesBetweenSlots head epochStart lastSlot =
      .ok participants)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      (Store.activeMembers state participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (dishonest : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J)
    (remaining : 3 * ((total.toNat - soFar.toNat) / 100 *
        (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat)) + margin ≤
      3 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∉ participants ∧ v ∈ J}) :
    HonestTargetVotes e margin u n head := by
  sorry

omit [DecidablePred (· ∈ J)] in
/-- A signed target before a slot has an earlier honest duty with the same target. -/
theorem Execution.exists_maySign_of_signsTargetBefore
    {v : ValidatorIndex} (honest : v ∈ J) {target : Checkpoint} {slot : Slot} {last : ℕ}
    (signed : SignsTargetBefore e v target slot last) :
    ∃ k data,
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k).time ((e.world k).view v) ((e.world k).state v) data ∧
      data.target = target ∧ data.slot < slot := by
  obtain ⟨n, _, message, sent, data, member, targetOk, before⟩ := signed
  obtain ⟨k, _, duty⟩ := e.exists_maySign_of_signed sent member honest
  exact ⟨k, data, duty, targetOk, before⟩

omit [DecidablePred (· ∈ J)] in
/-- Prefix safety applies at the original signing event of an honest target vote. -/
theorem Execution.head_supports_of_maySign
    {v : ValidatorIndex} (honest : v ∈ J) {k : ℕ} {data : AttestationData}
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k).time ((e.world k).view v) ((e.world k).state v) data)
    {first time : ℕ} {root : Root}
    (afterFirst : first ≤ (e.world k).time) (before : (e.world k).time < time)
    (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root) :
    ∃ head, ((e.world k).state v).getHead config = .ok head ∧
      ((e.world k).state v).isAncestor head ⟨root, .pending⟩ = .ok true := by
  obtain ⟨_, _, _, _, current, made, _⟩ := duty
  obtain ⟨head, _, _, _, headOk, _⟩ := made
  exact ⟨head, headOk, safe _ afterFirst before v honest k head rfl current headOk⟩

omit [DecidablePred (· ∈ J)] in
/-- An honest validator signs at most one target in each epoch. -/
theorem Execution.target_eq_of_signsTarget
    (slots : 0 < config.SLOT_DURATION_MS) {v : ValidatorIndex} (honest : v ∈ J)
    {first second : Checkpoint} {last last' : ℕ} (one : SignsTarget e v first last)
    (two : SignsTarget e v second last')
    (epoch : first.epoch = second.epoch) : first = second := by
  obtain ⟨n, _, m, sent, data, signed, target⟩ := one
  obtain ⟨k, _, other, otherSent, otherData, otherSigned, otherTarget⟩ := two
  have nonslashable := e.isSlashableAttestationData_of_signed slots
    (e.monotone_sent (Nat.le_max_left n k) sent)
    (e.monotone_sent (Nat.le_max_right n k) otherSent) signed otherSigned honest
  have sameEpoch : data.target.epoch = otherData.target.epoch := by
    rw [target, otherTarget, epoch]
  have same : data = otherData := by
    by_contra different
    simp [isSlashableAttestationData, different, sameEpoch] at nonslashable
  exact target.symm.trans ((congrArg AttestationData.target same).trans otherTarget)

omit [DecidablePred (· ∈ J)] in
/-- A pinned checkpoint is the counted target, or one of its signers is still uncounted.

The second case needs the prefix-safety argument at that signer's duty. -/
theorem Execution.target_eq_or_unseen_signer_of_pins
    (slots : 0 < config.SLOT_DURATION_MS) {anchorEpoch horizon : Epoch} {margin : ℕ}
    {last : ℕ} (pins : HonestThirdPins e anchorEpoch horizon margin last)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (nBound : (e.world n).time ≤ last)
    {head : Root}
    {state : BeaconState preset fork} {total : Gwei} {epoch : Epoch}
    {target checkpoint : Checkpoint} {voters : Finset ValidatorIndex}
    {participants : Std.TreeSet ValidatorIndex}
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (totalOk : getTotalActiveBalance state = .ok total)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (bounded : epoch ≤ horizon) (afterAnchor : anchorEpoch < epoch)
    (targetEpoch : target.epoch = epoch)
    (members : ∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
      (SignsTarget e v target (e.world n).time ∨ v ∉ participants))
    (large : total.toNat + margin < 3 * stake (fun v => balanceAt state v.toNat) voters)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (kBound : (e.world k).time ≤ last)
    {slot : Slot}
    (justified : ((e.world k).state w).Justified checkpoint)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (checkpointEpoch : checkpoint.epoch = epoch) :
    checkpoint = target ∨
      ∃ v ∈ voters, v ∈ J ∧ v ∉ participants ∧
        SignsTargetBefore e v checkpoint slot (e.world k).time := by
  obtain ⟨v, member, signed⟩ := pins u caller n nBound head state total epoch voters
    stateOk totalOk epochOk bounded (fun v hv => (members v hv).1)
    (fun v hv => (members v hv).2.1) large w receiver k kBound checkpoint slot
    justified slotOk checkpointEpoch afterAnchor
  rcases (members v member).2.2 with counted | unseen
  · exact .inl (e.target_eq_of_signsTarget slots (members v member).1 signed.signsTarget
      counted (checkpointEpoch.trans targetEpoch.symm))
  · exact .inr ⟨v, member, (members v member).1, unseen, signed⟩

/-- A duty in an epoch or later cannot precede that epoch's start time. -/
theorem epoch_start_le_attestation_deadline
    {epoch : Epoch} {first slot : Slot} {begin : UInt64} {time : ℕ}
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs first = .ok begin)
    (later : epoch ≤ computeEpochAtSlot preset slot)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) :
    begin.toNat ≤ time := by
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have epochLe := UInt64.le_iff_toNat_le.mp later
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochLe
  have firstLe : first ≤ slot := UInt64.le_iff_toNat_le.mpr (by
    rw [firstNat]
    exact (Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe).trans
      (Nat.div_mul_le_self _ _))
  obtain ⟨start, due, startOk, _, timeEq⟩ := deadline
  obtain ⟨begin', beginOk', _, beginLe⟩ := exists_timeAtSlotMs_of_le firstLe startOk
  have same := Except.ok.inj (beginOk.symm.trans beginOk')
  subst begin'
  have := UInt64.le_iff_toNat_le.mp beginLe
  omega

omit [DecidablePred (· ∈ J)] in
/-- An honest vote for an epoch or later has a duty no earlier than that epoch's start. -/
theorem Execution.exists_maySign_after_epoch_start_of_signsTargetBefore
    {v : ValidatorIndex} (honest : v ∈ J) {target : Checkpoint} {slot first : Slot}
    {epoch : Epoch} {begin : UInt64}
    {last : ℕ} (signed : SignsTargetBefore e v target slot last)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs first = .ok begin)
    (later : epoch ≤ target.epoch) :
    ∃ k data,
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k).time ((e.world k).view v) ((e.world k).state v) data ∧
      data.target = target ∧ data.slot < slot ∧ begin.toNat ≤ (e.world k).time := by
  obtain ⟨k, data, duty, targetOk, before⟩ :=
    e.exists_maySign_of_signsTargetBefore honest signed
  have dutyCopy := duty
  obtain ⟨_, _, deadline, _, _, made, _⟩ := dutyCopy
  obtain ⟨_, _, _, _, _, _, _, _, dataOk⟩ := made
  have epochOk := target_epoch_eq_of_getAttestationData dataOk
  refine ⟨k, data, duty, targetOk, before, ?_⟩
  apply epoch_start_le_attestation_deadline firstOk beginOk _ deadline
  rwa [← epochOk, targetOk]

/-- A duty before a representable slot has its deadline strictly before that slot starts. -/
theorem DelayFits.deadline_lt_later_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot last : Slot} {endTime : UInt64} {time : ℕ}
    (before : slot < last)
    (endOk : computeTimeAtSlotMs config genesisTimeMs last = .ok endTime)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) :
    time + Δ < endTime.toNat := by
  have slotLt := UInt64.lt_iff_toNat_lt.mp before
  have lastBound := last.toNat_lt
  have nextBound : slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by simp; omega
  have nextOk := addChecked_of_lt nextBound
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have nextLe : slot + 1 ≤ last := UInt64.le_iff_toNat_le.mpr (by
    simp only [UInt64.toNat_one] at nextNat; omega)
  obtain ⟨start, startOk, _, _⟩ := exists_timeAtSlotMs_of_le (UInt64.le_of_lt before) endOk
  obtain ⟨following, followingOk, _, followingLe⟩ := exists_timeAtSlotMs_of_le nextLe endOk
  exact (fits.before_boundary nextOk startOk followingOk deadline).trans_le
    (UInt64.le_iff_toNat_le.mp followingLe)

omit [DecidablePred (· ∈ J)] in
/-- Prefix safety covers a later-epoch target's honest duty after an epoch-start call. -/
theorem Execution.exists_supporting_head_of_signsTargetBefore_epoch_start
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {v : ValidatorIndex} (honest : v ∈ J) {target : Checkpoint} {slot first : Slot}
    {epoch : Epoch} {begin endTime : UInt64} {time : ℕ} {root : Root}
    {last : ℕ} (signed : SignsTargetBefore e v target slot last)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs first = .ok begin)
    (endOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok endTime)
    (endLe : endTime.toNat ≤ time) (later : epoch ≤ target.epoch)
    (safe : ∀ earlier, begin.toNat ≤ earlier → earlier < time → SafeAt e earlier root) :
    ∃ k data head,
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k).time ((e.world k).view v) ((e.world k).state v) data ∧
      data.target = target ∧ begin.toNat ≤ (e.world k).time ∧ (e.world k).time < time ∧
      ((e.world k).state v).getHead config = .ok head ∧
      ((e.world k).state v).isAncestor head ⟨root, .pending⟩ = .ok true := by
  obtain ⟨k, data, duty, targetOk, before, afterBegin⟩ :=
    e.exists_maySign_after_epoch_start_of_signsTargetBefore honest signed firstOk beginOk later
  have dutyCopy := duty
  obtain ⟨_, _, deadline, _⟩ := dutyCopy
  have bound := fits.deadline_lt_later_slot before endOk deadline
  have beforeTime : (e.world k).time < time := by omega
  obtain ⟨head, headOk, supports⟩ :=
    e.head_supports_of_maySign honest duty afterBegin beforeTime safe
  exact ⟨k, data, head, duty, targetOk, afterBegin, beforeTime, headOk, supports⟩

/-- A defined current slot has a representable start no later than the clock. -/
theorem exists_slot_start_of_current_slot {clock : UInt64} {slot : Slot}
    (current : computeSlotAtTimeMs config genesisTimeMs clock = .ok slot) :
    ∃ begin, computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧ begin ≤ clock := by
  unfold computeSlotAtTimeMs at current
  simp only [bind_ok_iff] at current
  obtain ⟨elapsed, elapsedOk, slotOk⟩ := current
  have elapsedNat := (subChecked_ok_iff.mp elapsedOk).2
  have slotNat := (divChecked_ok_iff.mp slotOk).2
  have offsetLe : slot.toNat * config.SLOT_DURATION_MS.toNat ≤ elapsed.toNat := by
    rw [slotNat]
    exact Nat.div_mul_le_self _ _
  have offsetBound : slot.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 :=
    offsetLe.trans_lt elapsed.toNat_lt
  have offsetOk := mulChecked_of_lt offsetBound
  have offsetNat := (mulChecked_ok_iff.mp offsetOk).2
  have genesisLe := (subChecked_ok_iff.mp elapsedOk).1
  have bound : genesisTimeMs.toNat + (slot * config.SLOT_DURATION_MS).toNat < 2 ^ 64 := by
    have := clock.toNat_lt
    omega
  have beginOk := addChecked_of_lt bound
  have beginNat := (addChecked_ok_iff.mp beginOk).2
  refine ⟨genesisTimeMs + slot * config.SLOT_DURATION_MS, ?_,
    UInt64.le_iff_toNat_le.mpr (by omega)⟩
  simp only [computeTimeAtSlotMs, offsetOk, bind, Except.bind, beginOk]

omit [DecidablePred (· ∈ J)] in
/-- An honest justified target has a supporting head after an epoch-start call. -/
theorem Execution.exists_supporting_head_of_justified_epoch_start
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {anchorEpoch horizon : Epoch} {last : ℕ}
    (voted : JustifiedByHonestVote e anchorEpoch horizon last)
    {anchor : Store preset fork} (anchored : ∀ w ∈ J, e.start w = anchor)
    {w : ValidatorIndex} (receiver : w ∈ J) {n : ℕ} (nBound : (e.world n).time ≤ last)
    {checkpoint : Checkpoint} {slot first : Slot}
    {epoch : Epoch} {begin : UInt64} {root : Root}
    (justified : ((e.world n).state w).Justified checkpoint)
    (slotOk : ((e.world n).state w).getCurrentSlot config = .ok slot)
    (current : UpToDate config checks sources (e.world n).time ((e.world n).view w)
      ((e.world n).state w))
    (afterAnchor : anchorEpoch < checkpoint.epoch) (bounded : checkpoint.epoch ≤ horizon)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs first = .ok begin)
    (later : epoch ≤ checkpoint.epoch)
    (safe : ∀ earlier, begin.toNat ≤ earlier → earlier < (e.world n).time →
      SafeAt e earlier root) :
    ∃ v ∈ J, ∃ k data head,
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k).time ((e.world k).view v) ((e.world k).state v) data ∧
      data.target = checkpoint ∧ begin.toNat ≤ (e.world k).time ∧
      (e.world k).time < (e.world n).time ∧
      ((e.world k).state v).getHead config = .ok head ∧
      ((e.world k).state v).isAncestor head ⟨root, .pending⟩ = .ok true := by
  obtain ⟨v, honest, signed⟩ := voted w receiver n nBound checkpoint slot justified slotOk
    afterAnchor bounded
  obtain ⟨k, data, duty, _, _⟩ := e.exists_maySign_of_signsTargetBefore honest signed
  obtain ⟨_, _, _, genesis, _⟩ := duty
  have senderGenesis := (e.clock_bounds v k).1
  have receiverGenesis := (e.clock_bounds w n).1
  rw [anchored v honest] at senderGenesis
  rw [anchored w receiver] at receiverGenesis
  have common : ((e.world n).state w).genesisTimeMs = genesisTimeMs :=
    receiverGenesis.trans (senderGenesis.symm.trans genesis)
  have slotOk' := mapError_ok_iff.mp slotOk
  change computeSlotAtTimeMs config ((e.world n).state w).genesisTimeMs
    ((e.world n).state w).timeMs = .ok slot at slotOk'
  rw [common] at slotOk'
  obtain ⟨endTime, endOk, endLe⟩ := exists_slot_start_of_current_slot slotOk'
  have endLe' : endTime.toNat ≤ (e.world n).time := by
    rw [← current.1]
    exact UInt64.le_iff_toNat_le.mp endLe
  obtain ⟨k, data, head, rest⟩ :=
    e.exists_supporting_head_of_signsTargetBefore_epoch_start fits honest signed
      firstOk beginOk endOk endLe' later safe
  exact ⟨v, honest, k, data, head, rest⟩

/-- A slot-start call's messages arrive strictly before the following slot starts. -/
theorem DelayFits.call_before_next_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {begin following : UInt64} {callTime endpoint : ℕ}
    (nextOk : addChecked slot 1 = .ok next)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (atSlot : callTime = begin.toNat)
    (later : following.toNat ≤ endpoint) : callTime + Δ < endpoint := by
  obtain ⟨due, dueOk⟩ := fits.1
  have bound := fits.2 slot next begin due following nextOk beginOk dueOk followingOk
  omega

/-- Step 6, the result: a block that passed the checks is not filtered out at a later time.

The caller is an honest validator whose store is up to date, and its rule passed the checks.

The block is on the chain of the head of the caller.

The head of the slot before, as the rule tracks it, was a head of the store of the caller.

Away from the start of an epoch, honest validators hold the count of the rule for the target.

They hold it with the margin.

Each has voted for that target or has still to vote in the epoch.

A start of the current epoch is the block of the anchor, or the rule checked its target before.

From the call to just before the later time, the block is safe.

The start of the rule is safe from the call to the later time.

Up to the horizon, two justified checkpoints of one epoch are the same.

An honest third, with the margin, signs each justified checkpoint of its epoch.

Each justified checkpoint after the anchor, up to the horizon, has an honest vote.

Slots last a positive time, so an honest validator signs one target in an epoch.

The RANDAO buffer is longer than the lower seed lookahead plus one, as `CommitteesFollow` asks.

A target with an honest quorum is included within an epoch, Assumption 3.

Each honest store up to the later time is in an epoch at most the horizon.

Then each honest store at the later time holds the block in its filtered tree.

Otherwise its justified block is above the block.

The proof follows a theorem of [verified-fast-confirmation][vfc] and the lemmas under it.

It is `Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.coveredOrViableAt_of_checked {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (oneBlock : OneBlockPerRoot e time)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (committees : CommitteesFollow e time)
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
      isStartSlotAtEpoch preset slot = .ok false → HonestTargetVotes e margin u n head.root)
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
    (startSafe : ∀ earlier, (e.world n).time ≤ earlier → earlier ≤ time → SafeAt e earlier start)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    (known : ∀ w ∈ J, ∀ k, (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ∃ block, ((e.world k).state w).blocks[root]? = some block) :
    CoveredOrViableAt e time root := by
  sorry

end Models.Network

end EthLib.Consensus
