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

/-- The target score is a sum of balances over the successful latest-target tests. -/
theorem getCurrentTargetScore_eq_sum
    {head : Root} {state : BeaconState preset fork} {target : Checkpoint} {score : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (targetOk : store.getCurrentTarget config head = .ok target)
    (scoreOk : store.getCurrentTargetScore config head = .ok score) :
    ∃ counted : List ValidatorIndex,
      (getActiveValidatorIndices state (getCurrentEpoch state)).filterM
        (fun index => return !(← validatorAt state index).slashed) =
          (Except.ok counted : Except ForkChoiceError (List ValidatorIndex)) ∧
      score.toNat = (counted.map fun index =>
        match store.latestMessages[index]? with
        | none => 0
        | some message =>
          if index ∈ store.equivocatingIndices then 0
          else if (store.getCheckpointForBlock message.root
            (getLatestMessageEpoch preset message)).toOption = some target
          then balanceAt state index.toNat else 0).sum := by
  simp only [getCurrentTargetScore, targetOk, stateOk, bind_ok_iff] at scoreOk
  obtain ⟨t, tOk, s, sOk, counted, countedOk, summed⟩ := scoreOk
  cases Except.ok.inj tOk
  cases Except.ok.inj sOk
  refine ⟨counted, countedOk, toNat_eq_of_sumGwei summed ?_⟩
  intro index member computed valueOk
  cases latest : store.latestMessages[index]? with
  | none =>
    have zero : computed = 0 := by simpa [latest, pure, Except.pure] using valueOk.symm
    simp [zero]
  | some message =>
    by_cases equivocating : index ∈ store.equivocatingIndices
    · have zero : computed = 0 := by
        simpa [latest, equivocating, pure, Except.pure] using valueOk.symm
      simp [equivocating, zero]
    · simp only [latest, equivocating, ite_false, bind_ok_iff] at valueOk
      obtain ⟨checkpoint, checkpointOk, valueOk⟩ := valueOk
      by_cases same : target = checkpoint
      · subst checkpoint
        simp only [ite_true] at valueOk
        simpa [latest, equivocating, checkpointOk, Except.toOption] using
          toNat_eq_balanceAt_of_effectiveBalance valueOk
      · have zero : computed = 0 := by simpa [same, pure, Except.pure] using valueOk.symm
        simp [equivocating, checkpointOk, Ne.symm same, zero, Except.toOption]

/-- A successful total-balance read makes the target score a finite stake, without duplicates. -/
theorem getCurrentTargetScore_eq_stake
    {head : Root} {state : BeaconState preset fork} {target : Checkpoint} {score total : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (targetOk : store.getCurrentTarget config head = .ok target)
    (totalOk : getTotalActiveBalance state = .ok total)
    (scoreOk : store.getCurrentTargetScore config head = .ok score) :
    ∃ counted : List ValidatorIndex,
      (getActiveValidatorIndices state (getCurrentEpoch state)).filterM
        (fun index => return !(← validatorAt state index).slashed) =
          (Except.ok counted : Except ForkChoiceError (List ValidatorIndex)) ∧
      counted.Nodup ∧
      score.toNat = stake (fun v => balanceAt state v.toNat)
        (counted.toFinset.filter fun index => (match store.latestMessages[index]? with
          | none => false
          | some message => decide (index ∉ store.equivocatingIndices ∧
            (store.getCheckpointForBlock message.root
              (getLatestMessageEpoch preset message)).toOption = some target)) = true) := by
  obtain ⟨counted, countedOk, summed⟩ := getCurrentTargetScore_eq_sum stateOk targetOk scoreOk
  simp only [getTotalActiveBalance, bind_ok_iff] at totalOk
  obtain ⟨active, activeOk, _⟩ := totalOk
  have distinct : (getActiveValidatorIndices state (getCurrentEpoch state)).Nodup := by
    have sorted := sorted_of_getActiveValidatorIndicesChecked_ok activeOk
    rw [getActiveValidatorIndicesChecked_ok activeOk] at sorted
    exact sorted.imp UInt64.ne_of_lt
  have keptDistinct := (sublist_of_filterM_ok countedOk).nodup distinct
  refine ⟨counted, countedOk, keptDistinct, ?_⟩
  rw [stake, Finset.sum_filter, List.sum_toFinset _ keptDistinct, summed]
  congr 1
  apply List.map_congr_left
  intro index _
  cases store.latestMessages[index]? with
  | none => simp
  | some message =>
    by_cases equiv : index ∈ store.equivocatingIndices <;> simp [equiv]

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

An honest store counts honest votes for the target of its current epoch.

Two thirds of the active balance of the pulled-up state of a head sign that target.

Their votes are sent by the time of the counting store's event.

Take an honest store that is up to date at that event or later, two epochs after the target.

A block that it holds has the target as its checkpoint, and its epoch is at most the target's.

The block is safe from the start of the epoch after the target to the time of that store.

Then the store holds a block above it, of an epoch before its own, with the target included.

Included means that the unrealized justification of that block is not before the target.

Both stores are at events up to the last time `limit`.

This is a counted-vote adapter for Assumption 3.2 of arXiv 2405.00549v4, Section 4.2.

No theorem here proves it equivalent to that assumption, in either direction.

The paper takes a block `b` and an epoch `e` at least the epoch of `b`, after GST.

It asks that `b` be canonical throughout epoch `e + 1`.

It also asks a condition on the votes in each view, for a link from a given source to `C(b, e)`.

That condition discounts slashed stake, and it holds for every view of a descendant block.

By the start of epoch `e + 2` each honest view then holds `b' ⪰ b`, of an epoch before `e + 2`.

The assumption says that `C(b, e)` is included in `AU(b')`.

Here the target plays the role of `C(b, e)`, read at the later store.

Safety asks this of each time from the start of epoch `e + 1` up to that store.

Every honest store that is up to date at an event of that time has its head above the block.

The votes are one count, for the target only, against one pulled-up head state.

Here the seed is a block above the given one, of an epoch before `target + 2`, like `b'`.

The conclusion is that the unrealized justification of the seed is of the target's epoch or later.

It does not say that the target itself is included.

The block is any such block of the later store, not one that the counting store already held.

The shape follows `EventualCheckpointInclusion.included` in [verified-fast-confirmation][vfc].

Its conclusion there is `A32IncludedAtTip`, with the seed above the block it is applied to.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetIncluded
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (limit : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n, (e.world n).time ≤ limit →
    ∀ head state total target, ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch →
    (∀ v ∈ voters, v ∈ J ∧ SignsTarget e v target (e.world n).time) →
    2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit → (e.world n).time ≤ (e.world k).time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
      target.epoch.toNat + 2 ≤ current.toNat →
      ∀ root rootEpoch, ((e.world k).state w).getBlockEpoch root = .ok rootEpoch →
      rootEpoch ≤ target.epoch →
      ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
      ∀ next first begin, addChecked target.epoch 1 = .ok next →
      computeStartSlotAtEpoch preset next = .ok first →
      computeTimeAtSlotMs config genesisTimeMs first = .ok begin →
      (∀ time, begin.toNat ≤ time → time < (e.world k).time → SafeAt e time root) →
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

That call was at the start of its slot, and the record keeps that time.

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
      HonestTargetVotes e margin u k head.root ∧
      ∃ slot begin, ((e.world k).state u).getCurrentSlot config = .ok slot ∧
        computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
        (e.world k).time = begin.toNat) ∧
    ∀ time, (e.world k).time ≤ time → time ≤ (e.world n).time → SafeAt e time origin

theorem ancestor_pending_of_walk {store : Store preset fork}
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
theorem anchor_walk_of_reachable {store anchor : Store preset fork}
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

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J} [DecidablePred (· ∈ J)]

omit [DecidablePred (· ∈ J)] in
/-- Each block that an honest store holds has the block of the anchor on its chain.

The call history uses this when its historical anchor is the block of the anchor. -/
theorem Execution.isAncestor_anchor_of_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block) :
    ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨anchor.finalizedCheckpoint.root, .pending⟩ = .ok true := by
  have reached := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨anchorKnown, walks⟩ := anchor_walk_of_reachable anchored reached
  exact ancestor_pending_of_walk anchorKnown (walks ⟨root, .pending⟩ block known fun _ => rfl).2

omit [DecidablePred (· ∈ J)] in
/-- Every held block reads an epoch-aligned anchor at the anchor's checkpoint boundary. -/
theorem walk_anchor_read {anchor : Store preset fork}
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
/-- Inclusion up to a time gives inclusion up to every earlier time. -/
theorem TargetIncluded.of_le {last later : ℕ} (included : TargetIncluded e later)
    (le : last ≤ later) : TargetIncluded e last :=
  fun u caller n nBound head state total target voters stateOk totalOk epochOk signed quorum w
    receiver k current kBound =>
    included u caller n (nBound.trans le) head state total target voters stateOk totalOk epochOk
      signed quorum w receiver k current (kBound.trans le)

omit [DecidablePred (· ∈ J)] in
/-- Assignment agrees with a current-epoch prefix without an anchor-slot alignment premise. -/
theorem CommitteesFollow.assigned_current_epoch {limit : ℕ}
    (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    (forward : Store.ForwardReachable config anchorState anchorBlock ((e.world k).state w))
    {head : ForkChoiceNode} {current first last : Slot} {participants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset current) = .ok first)
    (past : last < current)
    (found : ((e.world k).state w).getCommitteesBetweenSlots head.root first last =
      .ok participants) :
    ∀ v ∈ J, v ∈ participants ↔ ∃ slot committeeIndex,
      first ≤ slot ∧ slot ≤ last ∧ assignment.committee v slot = some committeeIndex := by
  exact committees.assigned w honest k bounded head current first last participants headOk
    slotOk past (fun _ read => forward.retained_current_epoch retained slotOk firstOk read) found

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

omit [DecidablePred (· ∈ J)] in
/-- An honest latest voter for the current epoch belongs to its past committee prefix. -/
theorem Execution.mem_participants_of_latest_current_epoch {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {limit : ℕ}
    (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n : ℕ}
    (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot first last : Slot} {participants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first)
    (lastOk : subChecked slot 1 = .ok last)
    (participantsOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants)
    {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message)
    (epochOk : getLatestMessageEpoch preset message = computeEpochAtSlot preset slot) :
    v ∈ participants := by
  obtain ⟨attestation, m, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start caller found
  obtain ⟨k, _, index, assigned, _⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
  have epoch : computeEpochAtSlot preset attestation.data.slot =
      computeEpochAtSlot preset slot := by
    rw [same] at epochOk
    unfold getLatestMessageEpoch LatestMessage.ofAttestation at epochOk
    split at epochOk
    · exact epochOk
    · exact origin.targetEpoch ▸ epochOk
  obtain ⟨current, currentOk, past⟩ := origin.past
  have eq := Except.ok.inj (currentOk.symm.trans slotOk)
  subst current
  have lastEq := (subChecked_ok_iff.mp lastOk).2
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  have lastLt : last < slot := by
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_one] at lastEq
    omega
  have high : attestation.data.slot ≤ last := by
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one] at lastEq
    omega
  have low : first ≤ attestation.data.slot := by
    have firstEq := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
    have divLe := Nat.div_mul_le_self attestation.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have epochNat := congrArg UInt64.toNat epoch
    simp only [computeEpochAtSlot, UInt64.toNat_div] at firstEq epochNat
    rw [epochNat] at divLe
    rw [UInt64.le_iff_toNat_le]
    omega
  have forward := e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored) n u caller
  exact (committees.assigned_current_epoch retained caller bounded forward headOk slotOk
    firstOk lastLt participantsOk v honest).mpr ⟨attestation.data.slot, index, low, high, assigned⟩

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
  classical
  intro readState support target readSlot first last members stateRead supportOk targetOk
    slotRead firstRead lastRead membersRead
  have stateEq := Except.ok.inj (stateRead.symm.trans stateOk)
  subst readState
  have slotEq := Except.ok.inj (slotRead.symm.trans slotOk)
  subst readSlot
  have firstEq := Except.ok.inj (firstRead.symm.trans startOk)
  subst first
  have lastEq := Except.ok.inj (lastRead.symm.trans lastOk)
  subst last
  have membersEq := Except.ok.inj (membersRead.symm.trans participantsOk)
  subst members
  obtain ⟨node, headRead, rfl⟩ := headOk
  obtain ⟨score, adversary, scoreOk, adversaryOk, supportEq⟩ :=
    Store.computeHonestFfgSupportForCurrentTarget_eq stateOk slotOk totalOk startOk lastOk
      soFarOk supportOk
  obtain ⟨counted, countedOk, _, scoreEq⟩ :=
    Store.getCurrentTargetScore_eq_stake stateOk targetOk totalOk scoreOk
  let scored := counted.toFinset.filter fun index => (match
      ((e.world n).state u).latestMessages[index]? with
    | none => false
    | some message => decide (index ∉ ((e.world n).state u).equivocatingIndices ∧
        (((e.world n).state u).getCheckpointForBlock message.root
          (getLatestMessageEpoch preset message)).toOption = some target)) = true
  let outside := {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset |
    v ∉ participants ∧ v ∈ J}
  let honest := scored.filter (· ∈ J)
  have totalRead := totalOk
  simp only [getTotalActiveBalance, bind_ok_iff] at totalRead
  obtain ⟨active, activeOk, _⟩ := totalRead
  have activeEq := getActiveValidatorIndicesChecked_ok activeOk
  have countedActive : ∀ v ∈ counted, v ∈ activeVoters state := by
    intro v member
    exact List.mem_toFinset.mpr (mem_of_filterM_ok countedOk member)
  have countedFound : ∀ v ∈ counted, ∃ validator,
      state.validators.data[v.toNat]? = some validator ∧
      isActiveValidator validator (getCurrentEpoch state) = true := by
    intro v member
    apply (mem_iff_of_getActiveValidatorIndicesChecked_ok activeOk).mp
    rw [activeEq]
    exact mem_of_filterM_ok countedOk member
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have targetEpoch : target.epoch = computeEpochAtSlot preset slot := by
    simp only [Store.getCurrentTarget, epochOk, Store.getCheckpointForBlock, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at targetOk
    obtain ⟨_, rfl, _, _, rfl⟩ := targetOk
    rfl
  have headStateRead : ∃ headState,
      ((e.world n).state u).blockState node.root = .ok headState := by
    have read := stateOk
    rw [Store.getPulledUpHeadState, bind_ok_iff] at read
    exact read.imp fun _ h => h.1
  obtain ⟨headState, headStateOk⟩ := headStateRead
  have scoredMessage : ∀ v ∈ scored, ∃ message,
      ((e.world n).state u).latestMessages[v]? = some message ∧
      v ∉ ((e.world n).state u).equivocatingIndices ∧
      ((e.world n).state u).getCheckpointForBlock message.root
        (getLatestMessageEpoch preset message) = .ok target := by
    intro v member
    have test := (Finset.mem_filter.mp member).2
    cases found : ((e.world n).state u).latestMessages[v]? with
    | none => simp [found] at test
    | some message =>
      simp only [found, decide_eq_true_eq] at test
      refine ⟨message, rfl, test.1, ?_⟩
      cases read : ((e.world n).state u).getCheckpointForBlock message.root
          (getLatestMessageEpoch preset message) with
      | error error => simp [read, Except.toOption] at test
      | ok checkpoint =>
        have eq : checkpoint = target := by simpa [read, Except.toOption] using test.2
        exact congrArg Except.ok eq
  have scoredIn : scored ⊆ Store.activeMembers state participants := by
    intro v member
    obtain ⟨message, latest, _, checkpointOk⟩ := scoredMessage v member
    obtain ⟨attestation, _, _, same, _, origin⟩ :=
      e.exists_signed_origin_of_latestMessages anchored start caller latest
    have messageEpoch : getLatestMessageEpoch preset message = target.epoch := by
      simp only [Store.getCheckpointForBlock, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at checkpointOk
      obtain ⟨_, _, eq⟩ := checkpointOk
      exact congrArg Checkpoint.epoch eq
    have epoch : attestation.data.target.epoch = computeEpochAtSlot preset slot := by
      rw [same] at messageEpoch
      unfold getLatestMessageEpoch LatestMessage.ofAttestation at messageEpoch
      split at messageEpoch
      · exact origin.targetEpoch.trans (messageEpoch.trans targetEpoch)
      · exact messageEpoch.trans targetEpoch
    obtain ⟨current, currentOk, past⟩ := origin.past
    have currentEq := Except.ok.inj (currentOk.symm.trans slotOk)
    subst current
    have low : epochStart ≤ attestation.data.slot := by
      have firstNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
      have divLe := Nat.div_mul_le_self attestation.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      change (computeEpochAtSlot preset attestation.data.slot).toNat *
        preset.SLOTS_PER_EPOCH.toNat ≤ attestation.data.slot.toNat at divLe
      rw [← origin.targetEpoch, epoch] at divLe
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have high : attestation.data.slot ≤ lastSlot := by
      have := (subChecked_ok_iff.mp lastOk).2
      have := UInt64.lt_iff_toNat_lt.mp past
      rw [UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_one] at *
      omega
    obtain ⟨targetState, index, committee, cached, below, committeeOk, inside⟩ :=
      origin.exists_mem_committee
    obtain ⟨common, headRun, targetRun, final, fixed, headRing, targetRing⟩ :=
      committees.common u caller n bounded node headState (computeEpochAtSlot preset slot)
        v attestation targetState headRead headStateOk epochOk (by rw [epoch])
          (by rw [epoch]; omega) origin cached
    have headKept := headRun.committeesKept final fixed headRing
    have targetKept := targetRun.committeesKept final fixed targetRing
    have sameCommittee := (headKept _ index origin.targetEpoch.symm).trans
      (targetKept _ index origin.targetEpoch.symm).symm
    have sameActive := (headRun.active.getActiveValidatorIndices_eq fixed).trans
      (targetRun.active.getActiveValidatorIndices_eq fixed).symm
    have count :
        getCommitteeCountPerSlot headState (computeEpochAtSlot preset attestation.data.slot) =
        getCommitteeCountPerSlot targetState (computeEpochAtSlot preset attestation.data.slot) := by
      simp only [← origin.targetEpoch, getCommitteeCountPerSlot, sameActive]
    exact Store.mem_activeMembers.mpr ⟨Store.mem_getCommitteesBetweenSlots participantsOk
      low high headStateOk (count ▸ below) (sameCommittee.trans committeeOk) inside,
        countedFound v (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)⟩
  -- The Byzantine cap covers counted Byzantine voters and the disjoint known equivocators.
  obtain ⟨weight, equivocation, weightOk, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok adversaryOk
  obtain ⟨readMembers, readMembersOk, equivocationEq⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have readMembersEq := Except.ok.inj
    (readMembersOk.symm.trans participantsOk)
  subst readMembers
  have cap := Store.threshold_mul_stake_le_of_computeAdversarialWeight weightOk equivocationOk
    adversaryOk (Store.stake_le_computeCommitteeWeightBetweenSlots participantsOk weightOk
      fun _ member => Store.mem_activeMembers.mp member)
      (fun _ _ => Nat.mod_eq_zero_of_dvd
        (dvd_balanceAt_of_aligned aligned (Nat.dvd_of_mod_eq_zero increment) _))
  have badIn : scored.filter (· ∉ J) ∪ ((e.world n).state u).equivocatorsOf state participants ⊆
      (Store.activeMembers state participants).filter (· ∉ J) := by
    intro v member
    rcases Finset.mem_union.mp member with member | member
    · exact Finset.mem_filter.mpr ⟨scoredIn (Finset.mem_filter.mp member).1,
        (Finset.mem_filter.mp member).2⟩
    · have parts := Finset.mem_filter.mp member
      exact Finset.mem_filter.mpr ⟨parts.1, dishonest v parts.2⟩
  have apart : Disjoint (scored.filter (· ∉ J))
      (((e.world n).state u).equivocatorsOf state participants) := by
    apply Finset.disjoint_left.mpr
    intro v member equiv
    exact (scoredMessage v (Finset.mem_filter.mp member).1).choose_spec.2.1
      (Finset.mem_filter.mp equiv).2
  have badBound := stake_mono (w := fun v => balanceAt state v.toNat) badIn
  rw [stake, Finset.sum_union apart, ← stake, ← stake, equivocationEq] at badBound
  have badLe : stake (fun v => balanceAt state v.toNat) (scored.filter (· ∉ J)) ≤
      adversary.toNat := by
    have byzantineBound := byzantine.2
    nlinarith
  have splitStake : stake (fun v => balanceAt state v.toNat) honest +
      stake (fun v => balanceAt state v.toNat) (scored.filter (· ∉ J)) =
      stake (fun v => balanceAt state v.toNat) scored :=
    Finset.sum_filter_add_sum_filter_not scored (· ∈ J) _
  have outsideActive : ∀ v ∈ outside, v ∈ activeVoters state := by
    intro v member
    obtain ⟨listed, _⟩ := Finset.mem_filter.mp member
    obtain ⟨⟨index, balance⟩, listed, eq⟩ := List.mem_map.mp (List.mem_toFinset.mp listed)
    simp only [unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at listed
    obtain ⟨validator, i, inZip, active, rfl, _⟩ := listed
    have found := List.mem_zipIdx_iff_getElem?.mp inZip
    simp only [Bool.and_eq_true] at active
    have active' := active.1
    have fits := lt_of_getActiveValidatorIndicesChecked_ok activeOk (by simpa using found) active'
    have indexNat : i.toUInt64.toNat = i := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
    apply List.mem_toFinset.mpr
    apply mem_getActiveValidatorIndices_of_isActiveAt
    apply isActiveAt_eq_true_iff.mpr
    exact ⟨validator, by simpa [← eq, indexNat] using found, active'⟩
  have disjoint : Disjoint honest outside := by
    apply Finset.disjoint_left.mpr
    intro v member other
    obtain ⟨scoredMem, honestMem⟩ := Finset.mem_filter.mp member
    obtain ⟨message, latest, _, checkpointOk⟩ := scoredMessage v scoredMem
    have messageEpoch : getLatestMessageEpoch preset message = computeEpochAtSlot preset slot := by
      simp only [Store.getCheckpointForBlock, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at checkpointOk
      obtain ⟨_, _, eq⟩ := checkpointOk
      exact (congrArg Checkpoint.epoch eq).trans targetEpoch
    exact (Finset.mem_filter.mp other).2.1
      (e.mem_participants_of_latest_current_epoch anchored start committees retained caller
        honestMem bounded headRead slotOk startOk lastOk participantsOk latest messageEpoch)
  refine ⟨honest ∪ outside, ?_, ?_⟩
  · intro v member
    rcases Finset.mem_union.mp member with member | member
    · obtain ⟨scoredMem, honestMem⟩ := Finset.mem_filter.mp member
      obtain ⟨message, latest, _, checkpointOk⟩ := scoredMessage v scoredMem
      exact ⟨honestMem, countedActive v
        (List.mem_toFinset.mp (Finset.mem_filter.mp scoredMem).1),
        Or.inl (e.signsTarget_of_latestMessages anchored start caller latest checkpointOk)⟩
    · exact ⟨(Finset.mem_filter.mp member).2.2, outsideActive v member,
        Or.inr (Finset.mem_filter.mp member).2.1⟩
  · have unionStake : stake (fun v => balanceAt state v.toNat) (honest ∪ outside) =
        stake (fun v => balanceAt state v.toNat) honest +
        stake (fun v => balanceAt state v.toNat) outside := Finset.sum_union disjoint
    change score.toNat = stake (fun v => balanceAt state v.toNat) scored at scoreEq
    rw [unionStake, supportEq]
    change 3 * _ + margin ≤ 3 * stake _ outside at remaining
    omega

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

/-- Both source selectors name a checkpoint covered by finalized-prefix agreement. -/
theorem walk_source_justified {store : Store preset fork} {root : Root}
    {checkpoint : Checkpoint}
    (read : store.getVotingSource config root = .ok checkpoint ∨
      store.unrealizedJustification root = .ok checkpoint)
    (later : GENESIS_EPOCH < checkpoint.epoch) : store.Justified checkpoint := by
  have cache : store.unrealizedJustifications[root]? = some checkpoint →
      store.Justified checkpoint :=
    fun entry => .inr (.inr ⟨later, .inr ⟨root, entry⟩⟩)
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
        exact .inr (.inr ⟨later, .inl ⟨root, state, stored, source.symm⟩⟩)
  · unfold Store.unrealizedJustification at unrealized
    cases entry : store.unrealizedJustifications[root]? with
    | none => simp [entry] at unrealized
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at unrealized
      exact cache (unrealized ▸ entry)

/-- A checkpoint read composes with an earlier checkpoint read even across empty slots. -/
theorem walk_checkpoint_trans {store : Store preset fork}
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
theorem walk_finalized_read_of_source {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last) (before : fork < .glamsterdam)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {root : Root} {checkpoint : Checkpoint} {boundary : Slot}
    (source : ((e.world n).state u).getVotingSource config root = .ok checkpoint ∨
      ((e.world n).state u).unrealizedJustification root = .ok checkpoint)
    (boundaryOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary)
    (read : ((e.world n).state u).getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (ordered : ((e.world k).state w).finalizedCheckpoint.epoch ≤ checkpoint.epoch)
    (inHorizon : checkpoint.epoch ≤ horizon) (later : GENESIS_EPOCH < checkpoint.epoch) :
    ((e.world n).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
  have priorRead := chain w receiver u caller k n kBound nBound checkpoint
    (walk_source_justified source later)
    ordered inHorizon
  have splitRead := priorRead
  unfold Store.getCheckpointBlock at splitRead
  simp only [bind_ok_iff] at splitRead
  obtain ⟨prior, priorOk, _⟩ := splitRead
  exact walk_checkpoint_trans boundaryOk (mapError_ok_iff.mp priorOk) ordered read priorRead before

/-- Coverage of a held root also covers each of its held ancestors. -/
theorem walk_covered_ancestor {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (lower : store.ParentsBelow) (before : fork < .glamsterdam)
    {root member : Root} {block : BeaconBlock preset fork} {nodes : List ForkChoiceNode}
    (known : store.blocks[member]? = some block)
    (descends : store.isAncestor ⟨root, .pending⟩ ⟨member, .pending⟩ = .ok true)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (covered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true ∨ (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
      ⟨member, .pending⟩ = .ok true ∨ (⟨member, .pending⟩ : ForkChoiceNode) ∈ nodes := by
  obtain ⟨rootBlock, rootKnown, _⟩ := Store.slot_le_of_isAncestor known descends
  rcases covered with covered | viable
  · exact Or.inl (Store.isAncestor_trans_of_lt before rootKnown known covered descends)
  have treeWalk : store.filterNodeTree config ⟨store.justifiedCheckpoint.root, .pending⟩ =
      .ok nodes := tree
  have ancestors := Store.filterNodeTree_ancestor (lower := lower) before treeWalk _ viable
  have memberAbove := (Store.isAncestor_iff (lower := lower) before known rfl descends).mp rfl
  rcases memberAbove.total ancestors.1 with above | below
  · left
    obtain ⟨_, justifiedKnown⟩ := (Store.filterNodeTree_mem treeWalk _
      (Store.filterNodeTree_self treeWalk (by intro empty; simp [empty] at viable))).2.1
    obtain ⟨ancestor, walk⟩ := Store.getAncestor_ok_of_orphans_le lower
      (node := ⟨store.justifiedCheckpoint.root, .pending⟩) (slot := block.slot)
      (fun r b held orphan => reached.orphans_le (UInt64.le_of_eq anchorSlot) held orphan known)
      justifiedKnown
    have rootEq := Store.getAncestor_root_eq (lower := lower)
      (node := ⟨member, .pending⟩) known walk above
    have pending := Store.getAncestor_pending_of_lt before rfl walk
    have ancestorEq : ancestor = (⟨member, .pending⟩ : ForkChoiceNode) := by
      cases ancestor
      simp_all
    rw [ancestorEq] at walk
    simp [Store.isAncestor, Store.block_ok_iff.mpr known, walk, bind, Except.bind,
      pure, Except.pure]
  · right
    obtain ⟨node, mem, rootEq⟩ := ancestors.2 (some member) below memberAbove
    have pending : node.payloadStatus = .pending := by
      rcases (Store.filterNodeTree_parent before rfl treeWalk node mem).2 with rfl | ⟨h, _⟩
      · rfl
      · exact h
    have eq : node = (⟨member, .pending⟩ : ForkChoiceNode) := by
      have rootEq := Option.some.inj rootEq
      cases node
      simp_all
    exact eq ▸ mem

/-- A pull-up can finalize the previous epoch, but no checkpoint more recent than that. -/
private theorem finalized_pull_bound {state after : BeaconState preset fork} {base : ℕ}
    (bound : state.finalizedCheckpoint.epoch.toNat ≤ base ∨
      state.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch state).toNat)
    (pulled : processJustificationAndFinalization state = .ok after) :
    after.finalizedCheckpoint.epoch.toNat ≤ base ∨
      after.finalizedCheckpoint.epoch.toNat + 1 ≤ (getCurrentEpoch state).toNat := by
  rcases processJustificationAndFinalization_ok pulled with rfl | ⟨t, p, c, weighed⟩
  · omega
  · obtain ⟨_, _, _, _, _, _, _, _, _, final⟩ :=
      weighJustificationAndFinalization_bits weighed
    rcases final with same | ⟨same, _, gap⟩ | ⟨same, _, gap⟩
    · rw [same]
      omega
    · rw [same]
      rcases gap with gap | ⟨_, gap⟩ <;> omega
    · rw [same]
      rcases gap with gap | ⟨_, gap⟩ <;> omega

private theorem finalized_advance_bound {state after : BeaconState preset fork} {base : ℕ}
    (bound : state.finalizedCheckpoint.epoch.toNat ≤ base ∨
      state.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch state).toNat)
    (advanced : advanceSlot config checks state = .ok after) :
    after.finalizedCheckpoint.epoch.toNat ≤ base ∨
      after.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch after).toNat := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advanced
  have frame := frame_processSlot cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- Crossing the boundary adds the second epoch of age to the pull-up bound.
    obtain ⟨justified, pulled, rest⟩ := processEpoch_frame epochedOk
    have cachedBound : cached.finalizedCheckpoint.epoch.toNat ≤ base ∨
        cached.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch cached).toNat := by
      simpa only [frame.finalized, getCurrentEpoch, frame.slot] using bound
    have bound' := finalized_pull_bound cachedBound pulled
    have step := nextSlot_epoch_of_boundary sum boundary
    rw [rest.toFrame.finalized]
    simp only [getCurrentEpoch_toNat, frame.slot] at bound' ⊢
    omega
  · rename_i inside
    cases Except.ok.inj epochedOk
    have step := nextSlot_epoch_of_inside sum inside
    simp only [getCurrentEpoch_toNat] at bound ⊢
    rw [frame.finalized, step]
    exact bound

private theorem finalized_slots_bound {state after : BeaconState preset fork} {base : ℕ}
    (holds : Invariant state)
    (bound : state.finalizedCheckpoint.epoch.toNat ≤ base ∨
      state.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch state).toNat)
    {count : ℕ} (advanced : advanceSlots config checks count state = .ok after) :
    after.finalizedCheckpoint.epoch.toNat ≤ base ∨
      after.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch after).toNat := by
  induction count generalizing state with
  | zero =>
    cases Except.ok.inj advanced
    exact bound
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at advanced
    obtain ⟨next, step, rest⟩ := advanced
    exact ih (advanceSlot_invariant holds step).1 (finalized_advance_bound bound step) rest

private theorem finalized_transition_bound {state after : BeaconState preset fork} {base : ℕ}
    {signed : SignedBeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (holds : Invariant state)
    (bound : state.finalizedCheckpoint.epoch.toNat ≤ base ∨
      state.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch state).toNat)
    (transition : stateTransition config checks engine state signed true = .ok after) :
    after.finalizedCheckpoint.epoch.toNat ≤ base ∨
      after.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch after).toNat := by
  obtain ⟨advanced, slots, _, _, block, _⟩ := stateTransition_ok transition
  have frame := frame_processBlock block
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
  obtain ⟨_, _, slots⟩ := slots
  simpa only [frame.finalized, getCurrentEpoch, frame.slot] using
    finalized_slots_bound holds bound slots

private theorem finalized_states_bound {store : Store preset fork}
    (sound : Invariant anchorState)
    (reached : Store.Reachable config anchorState anchorBlock store)
    {r : Root} {state : BeaconState preset fork} (found : store.blockStates[r]? = some state) :
    state.finalizedCheckpoint.epoch.toNat ≤ (getCurrentEpoch anchorState).toNat ∨
      state.finalizedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch state).toNat := by
  induction reached generalizing r state with
  | anchor made =>
    obtain ⟨_, _, _, states⟩ := getForkchoiceStore_maps made
    rw [states, getElem?_insert_root] at found
    split at found
    · cases Option.some.inj found
      exact .inl (UInt64.le_iff_toNat_le.mp
        (UInt64.le_trans (Store.finalized_le_currentJustified sound.ordered)
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _))))
    · simp at found
  | @block before after checks sources signed reached added ih =>
    rcases Store.onBlock_same_or_insert added with same | ⟨root, _, _, _, pre, post,
      preFound, transition, states⟩
    · exact ih (same ▸ found)
    rw [states, getElem?_insert_root] at found
    split at found
    · cases Option.some.inj found
      exact finalized_transition_bound ((reached.ordered sound).2 preFound)
        (ih preFound) transition
    · exact ih found
  | tick _ step ih => exact ih ((Store.onTick_frame step).2.2.2 ▸ found)
  | attestation _ step ih => exact ih ((Store.onAttestation_frame step).2.2 ▸ found)
  | attesterSlashing _ step ih => exact ih ((Store.onAttesterSlashing_frame step).2.2 ▸ found)
  | payloadAttestation _ step ih =>
    exact ih ((Store.onPayloadAttestationMessage_onlyPtcVotes step).frame.2.2 ▸ found)
  | envelope _ step ih => exact ih ((Store.onExecutionPayloadEnvelope_frame step).2.2 ▸ found)
  | inclusionList _ step ih => exact ih ((Store.onInclusionList_frame step).2.2 ▸ found)

/-- Realized finality is two epochs old; unrealized finality is one, except at the anchor. -/
def ResetAge (anchor : Checkpoint) (store : Store preset fork) (epoch : Epoch) : Prop :=
  (store.finalizedCheckpoint = anchor ∨
    (anchor.epoch < store.finalizedCheckpoint.epoch ∧
      store.finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat)) ∧
  (store.unrealizedFinalizedCheckpoint = anchor ∨
    (anchor.epoch < store.unrealizedFinalizedCheckpoint.epoch ∧
      store.unrealizedFinalizedCheckpoint.epoch.toNat + 1 ≤ epoch.toNat)) ∧
  anchor.epoch ≤ store.finalizedCheckpoint.epoch ∧
  anchor.epoch ≤ store.unrealizedFinalizedCheckpoint.epoch

private theorem resetAge_mono {anchor : Checkpoint} {s : Store preset fork} {a b : Epoch}
    (h : ResetAge anchor s a) (le : a ≤ b) : ResetAge anchor s b := by
  have le := UInt64.le_iff_toNat_le.mp le
  rcases h with ⟨hf, hu, lowF, lowU⟩
  exact ⟨hf.imp id (fun h => ⟨h.1, by omega⟩), hu.imp id (fun h => ⟨h.1, by omega⟩), lowF, lowU⟩

private theorem resetAge_update {anchor j f : Checkpoint} {s : Store preset fork} {epoch : Epoch}
    (h : ResetAge anchor s epoch)
    (bound : f.epoch.toNat ≤ anchor.epoch.toNat ∨ f.epoch.toNat + 2 ≤ epoch.toNat) :
    ResetAge anchor (s.updateCheckpoints j f) epoch := by
  unfold Store.updateCheckpoints
  rcases h with ⟨hf, hu, lowF, lowU⟩
  have low := UInt64.le_iff_toNat_le.mp lowF
  by_cases justified : s.justifiedCheckpoint.epoch < j.epoch <;>
    simp only [justified, ↓reduceIte] <;>
    split
  all_goals
    first
    | exact ⟨hf, hu, lowF, lowU⟩
    | rename_i advance
      have advance := UInt64.lt_iff_toNat_lt.mp advance
      exact ⟨.inr ⟨UInt64.lt_iff_toNat_lt.mpr (by dsimp only; omega), by dsimp only; omega⟩, hu,
        UInt64.le_iff_toNat_le.mpr (by dsimp only; omega), lowU⟩

private theorem resetAge_update_unrealized {anchor j f : Checkpoint}
    {s : Store preset fork} {epoch : Epoch} (h : ResetAge anchor s epoch)
    (bound : f.epoch.toNat ≤ anchor.epoch.toNat ∨ f.epoch.toNat + 1 ≤ epoch.toNat) :
    ResetAge anchor (s.updateUnrealizedCheckpoints j f) epoch := by
  unfold Store.updateUnrealizedCheckpoints
  rcases h with ⟨hf, hu, lowF, lowU⟩
  have low := UInt64.le_iff_toNat_le.mp lowU
  by_cases justified : s.unrealizedJustifiedCheckpoint.epoch < j.epoch <;>
    simp only [justified, ↓reduceIte] <;>
    split
  all_goals
    first
    | exact ⟨hf, hu, lowF, lowU⟩
    | rename_i advance
      have advance := UInt64.lt_iff_toNat_lt.mp advance
      exact ⟨hf, .inr ⟨UInt64.lt_iff_toNat_lt.mpr (by dsimp only; omega),
        by dsimp only; omega⟩, lowF,
        UInt64.le_iff_toNat_le.mpr (by dsimp only; omega)⟩

private theorem resetAge_realize {anchor : Checkpoint} {s : Store preset fork} {a b : Epoch}
    (h : ResetAge anchor s a) (lt : a < b) :
    ResetAge anchor (s.updateCheckpoints s.unrealizedJustifiedCheckpoint
      s.unrealizedFinalizedCheckpoint) b := by
  apply resetAge_update (resetAge_mono h (UInt64.le_of_lt lt))
  have lt := UInt64.lt_iff_toNat_lt.mp lt
  rcases h.2.1 with eq | le
  · exact .inl (by rw [eq])
  · exact .inr (by omega)

private theorem resetAge_tick_slot {anchor : Checkpoint} {s t : Store preset fork}
    {time : UInt64} {old new : Slot} (oldOk : s.getCurrentSlot config = .ok old)
    (newOk : t.getCurrentSlot config = .ok new) (le : old ≤ new)
    (h : ResetAge anchor s (computeEpochAtSlot preset old))
    (tick : s.onTickPerSlot config time = .ok t) :
    ResetAge anchor t (computeEpochAtSlot preset new) := by
  have epochLe : computeEpochAtSlot preset old ≤ computeEpochAtSlot preset new := by
    simpa only [computeEpochAtSlot, UInt64.le_iff_toNat_le, UInt64.toNat_div] using
      Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp le)
  have newClock :
      ({s with timeMs := time} : Store preset fork).getCurrentSlot config = .ok new := by
    simpa only [Store.getCurrentSlot, (Store.onTickPerSlot_frame tick).1,
      (Store.onTickPerSlot_frame tick).2.1] using newOk
  unfold Store.onTickPerSlot at tick
  simp only [bind_ok_iff, oldOk, newClock, Except.ok.injEq] at tick
  obtain ⟨_, rfl, _, rfl, offset, offsetOk, tick⟩ := tick
  split at tick <;>
    split at tick
  all_goals
    first
    | cases Except.ok.inj tick
      exact resetAge_mono h epochLe
    | have boundary : old < new ∧ offset = 0 := by assumption
      have lt : computeEpochAtSlot preset old < computeEpochAtSlot preset new := by
        obtain ⟨higher, zero⟩ := boundary
        have higher := UInt64.lt_iff_toNat_lt.mp higher
        have offsetOk := mapError_ok_iff.mp offsetOk
        unfold computeSlotsSinceEpochStart at offsetOk
        rw [bind_ok_iff] at offsetOk
        obtain ⟨start, startOk, sub⟩ := offsetOk
        have startEq := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
        have subEq : new - start = 0 := by simpa [zero] using Except.ok.inj sub
        have subEq := congrArg UInt64.toNat subEq
        simp only [UInt64.toNat_sub, UInt64.toNat_zero] at subEq
        rw [UInt64.lt_iff_toNat_lt, computeEpochAtSlot, computeEpochAtSlot, UInt64.toNat_div,
          UInt64.toNat_div]
        rw [computeEpochAtSlot, UInt64.toNat_div] at startEq
        have startBound := start.toNat_lt
        have newBound := new.toNat_lt
        have eq : new.toNat = new.toNat / preset.SLOTS_PER_EPOCH.toNat *
            preset.SLOTS_PER_EPOCH.toNat := by omega
        have pos : 0 < preset.SLOTS_PER_EPOCH.toNat := by
          by_contra notPos
          have zero : preset.SLOTS_PER_EPOCH.toNat = 0 := by omega
          simp [zero] at eq
          omega
        have bound := Nat.div_mul_le_self old.toNat preset.SLOTS_PER_EPOCH.toNat
        apply (Nat.mul_lt_mul_right pos).mp
        omega
      cases Except.ok.inj tick
      exact resetAge_realize h lt

private theorem resetAge_catchUp {anchor : Checkpoint} {s t : Store preset fork}
    {target old : Slot} (oldOk : s.getCurrentSlot config = .ok old) (le : old ≤ target)
    (h : ResetAge anchor s (computeEpochAtSlot preset old))
    (caught : Store.catchUp config s target = .ok t) :
    t.getCurrentSlot config = .ok target ∧
      ResetAge anchor t (computeEpochAtSlot preset target) := by
  induction s using Store.catchUp.induct config target generalizing old with
  | case1 s ih =>
    rw [Store.catchUp.eq_1] at caught
    rw [bind_ok_iff] at caught
    obtain ⟨current, currentOk, caught⟩ := caught
    rw [oldOk, Except.ok.injEq] at currentOk
    subst current
    split at caught
    · rename_i lt
      rw [bind_ok_iff] at caught
      obtain ⟨next, nextOk, caught⟩ := caught
      rw [bind_ok_iff] at caught
      obtain ⟨time, timeOk, caught⟩ := caught
      rw [bind_ok_iff] at caught
      obtain ⟨ticked, tick, caught⟩ := caught
      split at caught
      · have nextOk := mapError_ok_iff.mp nextOk
        have timeOk := mapError_ok_iff.mp timeOk
        have tickSlot : ticked.getCurrentSlot config = .ok next := by
          unfold Store.getCurrentSlot
          rw [(Store.onTickPerSlot_frame tick).1, (Store.onTickPerSlot_frame tick).2.1,
            computeSlotAtTimeMs_computeTimeAtSlotMs (Store.slotDuration_pos oldOk) timeOk]
          rfl
        have sum := (addChecked_ok_iff.mp nextOk).2
        have low : old ≤ next := UInt64.le_iff_toNat_le.mpr (by simp_all)
        have high : next ≤ target := UInt64.le_iff_toNat_le.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp lt
          simp only [UInt64.toNat_one] at sum
          omega)
        exact ih ticked ‹_› tickSlot high (resetAge_tick_slot oldOk tickSlot low h tick) caught
      · cases caught
    · rename_i notLt
      have eq : old = target := UInt64.le_antisymm le (UInt64.not_lt.mp notLt)
      cases Except.ok.inj caught
      subst target
      exact ⟨oldOk, h⟩

private theorem resetAge_tick {anchor : Checkpoint} {s t : Store preset fork}
    {time : UInt64} {old : Slot} (oldOk : s.getCurrentSlot config = .ok old)
    (forward : s.timeMs ≤ time) (h : ResetAge anchor s (computeEpochAtSlot preset old))
    (tick : s.onTick config time = .ok t) :
    ∃ current, t.getCurrentSlot config = .ok current ∧
      ResetAge anchor t (computeEpochAtSlot preset current) := by
  have finalSlot := Store.getCurrentSlot_onTick tick
  unfold Store.onTick at tick
  simp only [bind_ok_iff] at tick
  obtain ⟨target, targetOk, caught, caughtOk, tick⟩ := tick
  have low : old ≤ target := computeSlotAtTimeMs_mono forward
    (mapError_ok_iff.mp oldOk) (mapError_ok_iff.mp targetOk)
  have targetFinal := finalSlot.trans targetOk
  obtain ⟨caughtSlot, h⟩ := resetAge_catchUp oldOk low h caughtOk
  exact ⟨target, targetFinal,
    resetAge_tick_slot caughtSlot targetFinal (UInt64.le_refl _) h tick⟩

open Serialization.Ssz in
private theorem resetAge_block {anchor : Store preset fork} {s t : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (reached : Store.Reachable config anchorState anchorBlock s)
    {current : Slot} (clock : s.getCurrentSlot config = .ok current)
    (h : ResetAge anchor.finalizedCheckpoint s (computeEpochAtSlot preset current))
    {signed : SignedBeaconBlock preset fork}
    (added : s.onBlock config checks sources signed = .ok t) :
    ResetAge anchor.finalizedCheckpoint t (computeEpochAtSlot preset current) := by
  obtain ⟨anchorRoot, _, _, _, _, anchorFinal, _⟩ := getForkchoiceStore_anchor anchored
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, Except.mapError, bind, Except.bind] at added
  | ok blockRoot =>
    by_cases known : s.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact h
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError,
      ↓reduceIte, Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, _, voted, vote, recorded, record, boosted, boost, pulled⟩ := added
    obtain ⟨pre, preFound, _, _, transition⟩ := Store.validateOnBlock_ok valid
    have stateBound := finalized_transition_bound ((reached.ordered sound).2 preFound)
      (finalized_states_bound sound reached preFound) transition
    have stateSlot := (stateTransition_slot transition).2
    obtain ⟨⟨slot, slotOk, slotLe⟩, _⟩ := Store.validateOnBlock_checks valid
    rw [clock, Except.ok.injEq] at slotOk
    subst slot
    have epochLe : (getCurrentEpoch state).toNat ≤ (computeEpochAtSlot preset current).toNat := by
      simp only [getCurrentEpoch_toNat, stateSlot, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp slotLe)
    have stateBound' : state.finalizedCheckpoint.epoch.toNat ≤
        anchor.finalizedCheckpoint.epoch.toNat ∨ state.finalizedCheckpoint.epoch.toNat + 2 ≤
          (computeEpochAtSlot preset current).toNat := by
      rw [anchorFinal]
      dsimp only
      omega
    -- Timeliness, payload votes and proposer boost leave both checkpoint pairs unchanged.
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedAge : ResetAge anchor.finalizedCheckpoint recorded
        (computeEpochAtSlot preset current) := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact h
      · cases record
        exact h
    have boostedAge : ResetAge anchor.finalizedCheckpoint boosted
        (computeEpochAtSlot preset current) := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> cases Except.ok.inj boost <;> exact recordedAge
    have boostedClock : boosted.getCurrentSlot config = .ok current := by
      rw [(Store.updateProposerBoostRoot_frame boost).2.2.2.getCurrentSlot,
        (Store.recordBlockTimeliness_frame record).2.2.2.getCurrentSlot]
      exact clock
    have boostedState : boosted.blockStates[blockRoot]? = some state := by
      rw [(Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
      simp
    have boostedBlock : boosted.blocks[blockRoot]? = some signed.message := by
      rw [(Store.updateProposerBoostRoot_frame boost).2.1,
        (Store.recordBlockTimeliness_frame record).2.1]
      simp
    have updatedAge := resetAge_update boostedAge stateBound'
      (j := state.currentJustifiedCheckpoint)
    unfold Store.computePulledUpTip at pulled
    simp only [bind_ok_iff] at pulled
    obtain ⟨base, baseOk, endState, endOk, block, blockOk, epoch, epochOk, pulled⟩ := pulled
    have baseEq : base = state := by
      have found := Store.blockState_ok_iff.mp baseOk
      rw [Store.updateCheckpoints_blockStates, boostedState] at found
      exact (Option.some.inj found).symm
    subst base
    have blockEq : block = signed.message := by
      have found := Store.block_ok_iff.mp blockOk
      simpa only [Store.updateUnrealizedCheckpoints_blocks, Store.updateCheckpoints_blocks,
        boostedBlock, Option.some.injEq] using found.symm
    subst block
    have epochEq : epoch = computeEpochAtSlot preset current := by
      unfold Store.getCurrentSlot at boostedClock
      simp only [Store.getCurrentStoreEpoch, Store.updateCheckpoints,
        Store.updateUnrealizedCheckpoints] at epochOk
      repeat' split at epochOk
      all_goals simpa only [Store.getCurrentSlot, boostedClock,
        bind, Except.bind, pure, Except.pure, Except.ok.injEq] using epochOk.symm
    subst epoch
    have pulledBound := finalized_pull_bound stateBound (mapError_ok_iff.mp endOk)
    have unrealizedBound : endState.finalizedCheckpoint.epoch.toNat ≤
        anchor.finalizedCheckpoint.epoch.toNat ∨ endState.finalizedCheckpoint.epoch.toNat + 1 ≤
          (computeEpochAtSlot preset current).toNat := by
      rw [anchorFinal]
      dsimp only
      omega
    have unrealizedAge := resetAge_update_unrealized
      (s := { (boosted.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint)
        with unrealizedJustifications :=
          ((boosted.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
            ).unrealizedJustifications.insert blockRoot endState.currentJustifiedCheckpoint) })
      updatedAge unrealizedBound (j := endState.currentJustifiedCheckpoint)
    split at pulled
    · rename_i earlier
      -- A pull-up becomes realized only after the epoch of its block.
      cases Except.ok.inj pulled
      apply resetAge_update unrealizedAge
      have earlier := UInt64.lt_iff_toNat_lt.mp earlier
      have epochState : getCurrentEpoch state = computeEpochAtSlot preset signed.message.slot := by
        simp only [getCurrentEpoch, stateSlot]
      rw [epochState] at pulledBound
      rw [anchorFinal]
      dsimp only
      omega
    · cases Except.ok.inj pulled
      exact unrealizedAge

theorem resetAge_forward {anchor store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (positive : 0 < config.SLOT_DURATION_MS)
    (forward : Store.ForwardReachable config anchorState anchorBlock store) :
    ∃ current, store.getCurrentSlot config = .ok current ∧
      ResetAge anchor.finalizedCheckpoint store (computeEpochAtSlot preset current) := by
  induction forward with
  | anchor made =>
    have eq := Except.ok.inj (anchored.symm.trans made)
    subst eq
    obtain ⟨r, _, _, _, _, hf, _, hu⟩ := getForkchoiceStore_anchor made
    exact ⟨anchorState.slot, getCurrentSlot_getForkchoiceStore positive made,
      .inl rfl, .inl (hu.trans hf.symm), UInt64.le_refl _, by rw [hf, hu]; exact UInt64.le_refl _⟩
  | tick _ le tick ih =>
    obtain ⟨current, clock, h⟩ := ih
    exact resetAge_tick clock le h tick
  | block reached added ih =>
    obtain ⟨current, clock, h⟩ := ih
    exact ⟨current, (Store.onBlock_sameClock added).getCurrentSlot.trans clock,
      resetAge_block anchored sound reached.reachable clock h added⟩
  | attestation _ attested ih =>
    obtain ⟨current, clock, h⟩ := ih
    refine ⟨current, (Store.onAttestation_sameClock attested).getCurrentSlot.trans clock, ?_⟩
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, valid, _, attested⟩ := attested
    have kept : ResetAge anchor.finalizedCheckpoint stored (computeEpochAtSlot preset current) := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · cases Except.ok.inj storing
        exact h
      · simp only [bind_ok_iff] at storing
        obtain ⟨_, _, storing⟩ := storing
        cases Except.ok.inj storing
        exact h
    split at attested
    · cases Except.ok.inj attested
      exact kept
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
  | attesterSlashing _ slashed ih =>
    obtain ⟨current, clock, h⟩ := ih
    refine ⟨current, (Store.onAttesterSlashing_sameClock slashed).getCurrentSlot.trans clock, ?_⟩
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact h
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ accepted
    exact ih

omit [DecidablePred (· ∈ J)] in
/-- The finalized checkpoint of an honest store is that of the anchor, or is two epochs old.

No checkpoint of the state of the anchor is of a later epoch than that state.

A state finalizes a checkpoint of the epoch before its own at the latest.

The store takes that checkpoint from a block of an epoch before its own. -/
theorem Execution.finalizedCheckpoint_eq_or_add_two_le {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (start : e.start u = anchor) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint ∨
      ((e.world n).state u).finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat := by
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) := by
    clear epochOk
    induction n with
    | zero =>
      change Store.ForwardReachable config anchorState anchorBlock (e.start u)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n u with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.forwardReachable ih
  unfold Store.getCurrentStoreEpoch at epochOk
  rw [bind_ok_iff] at epochOk
  obtain ⟨slot, slotOk, epochOk⟩ := epochOk
  obtain ⟨current, clock, h⟩ := resetAge_forward anchored sound
    (Store.slotDuration_pos slotOk) forward
  rw [slotOk, Except.ok.injEq] at clock
  subst current
  cases Except.ok.inj epochOk
  exact h.1.imp id And.right

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
      (s.updateUnrealizedCheckpoints j f).unrealizedJustifications =
        s.unrealizedJustifications := by
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
          state.finalizedCheckpoint).unrealizedJustifications =
            boosted.unrealizedJustifications := by
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

/-- Both voting-source selectors return an anchor-era checkpoint or an ancestor. -/
theorem walk_source_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
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
        aligned nonzero child stored processed).2.1
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
          aligned nonzero child stored).2.1
  · unfold Store.unrealizedJustification at unrealized
    cases entry : store.unrealizedJustifications[root]? with
    | none => simp [entry] at unrealized
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at unrealized
      exact cache (unrealized ▸ entry)

/-- A selected source cannot be newer than the current epoch of its store. -/
theorem walk_source_epoch_le {store : Store preset fork}
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
    simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind,
      pure, Except.pure] using epochOk
  have bound : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      getCurrentEpoch s ≤ epoch := by
    intro r s held
    rw [← epochEq, UInt64.le_iff_toNat_le]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (states r s held))
  have cache : store.unrealizedJustifications[root]? = some checkpoint →
      checkpoint.epoch ≤ epoch := by
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

omit [DecidablePred (· ∈ J)] in
/-- Prefix agreement identifies a finalized checkpoint whose epoch is still the anchor's. -/
theorem walk_finalized_eq_anchor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (before : fork < .glamsterdam) {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ last)
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
  have read := chain w honest w honest k 0 bounded ((e.monotone_time (Nat.zero_le k)).trans bounded)
    anchor.justifiedCheckpoint justifiedAt
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
theorem walk_finalized_read_of_recent_source {anchor : Store preset fork}
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
  have anchorRead := walk_anchor_read anchorStore anchored anchorSlot anchorBoundary before
    caller known
  rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound
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

The RANDAO buffer is longer than the lower seed lookahead plus two.

This retains the target epoch's committee seed in a head of the following epoch.

Each up-to-date honest head has the past committee reads that `HeadFollowsSupport` supplies.

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
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (oneBlock : OneBlockPerRoot e time)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (committees : CommitteesFollow e time)
    (follows : HeadFollowsSupport e time)
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
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (long : 1 < preset.SLOTS_PER_EPOCH) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
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
