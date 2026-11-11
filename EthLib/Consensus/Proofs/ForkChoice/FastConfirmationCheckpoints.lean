module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints

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

/-- The selected start carries both its reset checks and its descendant search. -/
theorem getLatestConfirmed_checked_start {fcr : FastConfirmationStore} {head root : Root}
    (lower : store.ParentsBelow)
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      (start = fcr.confirmedRoot ∧
          store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
          (isStartSlotAtEpoch preset slot = .ok true →
            store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true) ∨
        start = store.finalizedCheckpoint.root ∨
        start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
          isStartSlotAtEpoch preset slot = .ok true ∧
          (∃ observedBlock epoch,
            store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
            store.getCurrentStoreEpoch config = .ok epoch ∧
            Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
          store.unrealizedJustification head = .ok fcr.currentEpochObservedJustifiedCheckpoint) ∧
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
  let kept : Prop := store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
    (isStartSlotAtEpoch preset slot = .ok true →
      store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)
  -- Keep the reset decision paired with the continuation that consumes it.
  have reset : ∃ reset, (reset = false → kept) ∧ resetBody reset = .ok root := by
    clear_value resetBody
    rw [bind_ok_iff] at latest
    obtain ⟨_, -, latest⟩ := latest
    rw [bind_ok_iff] at latest
    obtain ⟨_, -, latest⟩ := latest
    split at latest
    · exact ⟨true, by simp, latest⟩
    · rw [bind_ok_iff] at latest
      obtain ⟨onChain, ancestry, latest⟩ := latest
      split at latest
      · exact ⟨true, by simp, latest⟩
      · rename_i isOnChain
        obtain rfl : onChain = true := by simpa using isOnChain
        rw [bind_ok_iff] at latest
        obtain ⟨atStart, startChecked, latest⟩ := latest
        split at latest
        · rw [bind_ok_iff] at latest
          obtain ⟨safe, chainChecked, latest⟩ := latest
          refine ⟨!safe, fun notReset => ⟨ancestry, fun _ => ?_⟩, latest⟩
          obtain rfl : safe = true := by simpa using notReset
          exact chainChecked
        · rename_i notStart
          refine ⟨false, fun _ => ⟨ancestry, fun isStart => ?_⟩, latest⟩
          exact absurd (Except.ok.inj (startChecked.symm.trans isStart)) notStart
  clear latest
  obtain ⟨reset, keeps, latest⟩ := reset
  have base : ∃ base, (base = fcr.confirmedRoot ∧ kept ∨
      base = store.finalizedCheckpoint.root) ∧ afterReset () base = .ok root := by
    cases reset
    · exact ⟨fcr.confirmedRoot, Or.inl ⟨rfl, keeps rfl⟩, latest⟩
    · exact ⟨store.finalizedCheckpoint.root, Or.inr rfl, latest⟩
  clear latest keeps
  obtain ⟨base, baseCase, latest⟩ := base
  -- The observed checkpoint can replace this base only after all replacement checks pass.
  have start : ∃ start, (start = fcr.confirmedRoot ∧ kept ∨
      start = store.finalizedCheckpoint.root ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
        isStartSlotAtEpoch preset slot = .ok true ∧
        (∃ observedBlock epoch,
          store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
          store.getCurrentStoreEpoch config = .ok epoch ∧
          Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
        store.unrealizedJustification head =
          .ok fcr.currentEpochObservedJustifiedCheckpoint) ∧ finish () start = .ok root := by
    clear_value finish
    simp only [afterReset, bind_ok_iff] at latest
    obtain ⟨atStart, startChecked, observedBlock, observedFound, observedEpoch, epochAdded,
      justified, justification, _, -, latest⟩ := latest
    split at latest
    · rename_i replaced
      refine ⟨observedRoot, Or.inr (Or.inr ⟨rfl, ?_, ?_, ?_⟩), latest⟩
      · exact replaced.1 ▸ startChecked
      · refine ⟨observedBlock, currentEpoch, observedFound, epochFound, ?_⟩
        exact replaced.2.1 ▸ mapError_ok_iff.mp epochAdded
      · exact justification.trans (congrArg Except.ok replaced.2.2.1.symm)
    · exact ⟨base, baseCase.imp id Or.inl, latest⟩
  clear latest
  obtain ⟨start, startCase, latest⟩ := start
  refine ⟨start, slotFound, startCase, ?_⟩
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
  obtain ⟨slot, start, _, startCase, result⟩ := getLatestConfirmed_checked_start lower latest
  refine ⟨start, ?_, result.imp id And.left⟩
  rcases startCase with ⟨same, _⟩ | same | ⟨same, _⟩
  · exact Or.inl same
  · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr same)

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
        (SignsTarget e v target ∨ v ∉ participants)) ∧
      3 * support.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters

/-- Assumption 3 of the paper: a target with an honest quorum is included within an epoch.

An honest store counts honest votes for the checkpoint of an epoch on the chain of a block.

Two thirds of the active balance of the pulled-up state of a head sign that target.

The block is safe from a first time on.

Take an honest store that is up to date at that time or later.

Its epoch is two epochs after the target or later.

It holds a block above the given one, of an epoch before that, with the target included.

Included means that the unrealized justification of that block is not before the target.

In [verified-fast-confirmation][vfc], this is `EventualCheckpointInclusion.included`.

Its conclusion there is `A32IncludedAtTip`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetIncluded
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ u ∈ J, ∀ n head state total root rootEpoch target, ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
    rootEpoch ≤ target.epoch →
    ((e.world n).state u).getCheckpointBlock root target.epoch = .ok target.root →
    (∀ v ∈ voters, v ∈ J ∧ SignsTarget e v target) →
    2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k current, (e.world n).time ≤ (e.world k).time →
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

/-- Step 6, the count: honest validators hold the count of the rule for the target, with a margin.

The caller is an honest validator, and each honest store starts from the store of the anchor.

Each latest vote of an honest validator in the store of the caller is a vote that it signed.

The Byzantine validators hold at most β of the committees of the epoch so far, Assumption 2.

So the votes for the target less the weight of the adversary are honest votes.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

The stake is read in the pulled-up state of the head.

The statement reads the store of the caller alone, and takes no safety of the target.

The proof follows two lemmas of [verified-fast-confirmation][vfc].

The first is `noConflict_arithmeticBranch_oneThird`.

The second is `currentTarget_remaining_honest_le_future_weight`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honestTargetVotes_of_byzantineStakeAtMost {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (committees : CommitteesFollow e) {margin : ℕ}
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
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

/-- Step 6, the result: a block that passed the checks is not filtered out at a later time.

The caller is an honest validator whose store is up to date, and its rule passed the checks.

The block is on the chain of the head of the caller.

The head of the slot before, as the rule tracks it, was a head of the store of the caller.

Honest validators hold the count of the rule for the target of the head, with the margin.

Each has voted for that target or has still to vote in the epoch.

A start of the current epoch is the block of the anchor, or the rule checked its target before.

From the call to just before the later time, the block is safe.

The start of the rule is safe from the call to the later time.

Up to the horizon, two justified checkpoints of one epoch are the same.

An honest third, with the margin, signs each justified checkpoint of its epoch.

Each justified checkpoint after the anchor, up to the horizon, has an honest vote.

Slots last a positive time, so an honest validator signs one target in an epoch.

A target with an honest quorum is included within an epoch, Assumption 3.

Each honest store up to the later time is in an epoch at most the horizon.

Then each honest store at the later time holds the block in its filtered tree.

Otherwise its justified block is above the block.

The proof follows a theorem of [verified-fast-confirmation][vfc] and the lemmas under it.

It is `Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.coveredOrViableAt_of_checked {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam)
    (admitted : BlocksAdmitted e 0 Δ)
    (oneBlock : OneBlockPerRoot e)
    (votes : Votes e.startTime e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e) (committees : CommitteesFollow e)
    {horizon anchorEpoch : Epoch} {margin : ℕ}
    (chain : FinalizedPrefix e horizon)
    (unique : OneJustifiedPerEpoch e horizon) (pins : HonestThirdPins e anchorEpoch horizon margin)
    (voted : JustifiedByHonestVote e anchorEpoch horizon) (included : TargetIncluded e)
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
    (targetVotes : HonestTargetVotes e margin u n head.root)
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
    {time : ℕ} (later : (e.world n).time ≤ time)
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
