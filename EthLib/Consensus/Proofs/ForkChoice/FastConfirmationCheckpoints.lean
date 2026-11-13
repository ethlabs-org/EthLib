module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.HonestHeads
public import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Statements: a block that the rule confirms stays in the filtered tree of each honest store

This file states step 6 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The late case of a block of the call's own epoch is proved in `FastConfirmationLateCurrent`.

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

/-- Each root has a stored realized justification at most one epoch behind its block. -/
def RealizedRecent (store : Store preset fork) (roots : List Root) : Prop :=
  ∀ root ∈ roots, ∃ block state,
    store.blocks[root]? = some block ∧ store.blockStates[root]? = some state ∧
      (computeEpochAtSlot preset block.slot).toNat ≤
        state.currentJustifiedCheckpoint.epoch.toNat + 1

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

/-- Assumption 3 of the paper: an honest quorum for a target is included by the epoch after next.

An honest store, at an event `q`, reads its head, the pulled-up state of the head and its target.

The epoch of the store is the epoch of the target, `E`.

Two thirds of the active balance of that state belong to honest voters.

Each of them signs a vote with that target before the start of epoch `E + 1`.

A later time, the event `n`, is still in epoch `E`.

Its reader takes `n` to be the call that confirmed a block; the definition takes any such event.

Take an honest store that is up to date at that time or later, from epoch `E + 2` on.

A block that it holds has the target as its checkpoint of epoch `E`, and its epoch is at most `E`.

The block is safe from the time of `n` to the time of that store.

Nothing is asked of the block before `n`.

Then the store holds a seed above the block, of epoch `E` or `E + 1`.

The state of the seed reads the target as its block root of epoch `E`.

That state has justified epoch `E` or a later one, or it holds the target votes of the voters.

From Altair those votes are timely target flags, in the list of the current epoch for a seed of `E`.

A seed of `E + 1` holds them in the list of the previous epoch.

Before Altair they are pending attestations for the target that the voters attested.

Both stores are at events up to the last time `limit`.

This is a counted-vote adapter for Assumption 3.2 of arXiv 2405.00549v4, Section 4.2.

No theorem here proves it equivalent to that assumption, in either direction.

The paper takes a block `b` and an epoch `e` at least the epoch of `b`, after GST.

It asks that `b` be canonical throughout epoch `e + 1`.

By the start of epoch `e + 2` each honest view then holds `b' ⪰ b` that includes `C(b, e)`.

Here `e` is the epoch `E` of the confirming event, not the epoch of the block.

The quorum is the honest voter set of one count, against one pulled-up head state.

The shape follows `EventualCheckpointInclusion.included` in [verified-fast-confirmation][vfc].

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
def TargetIncluded
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (limit : ℕ) : Prop :=
  ∀ u ∈ J, ∀ q n, q ≤ n → (e.world n).time ≤ limit →
    ∀ (head : ForkChoiceNode) state total target, ∀ voters : Finset ValidatorIndex,
    ((e.world q).state u).getHead config = .ok head →
    ((e.world q).state u).getPulledUpHeadState config head.root = .ok state →
    ((e.world q).state u).getCurrentTarget config head.root = .ok target →
    getTotalActiveBalance state = .ok total →
    ((e.world q).state u).getCurrentStoreEpoch config = .ok target.epoch →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch →
    2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ next first begin, addChecked target.epoch 1 = .ok next →
    computeStartSlotAtEpoch preset next = .ok first →
    computeTimeAtSlotMs config genesisTimeMs first = .ok begin →
    (∀ v ∈ voters, v ∈ J ∧ SignsTarget e v target (begin.toNat - 1)) →
    ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit → (e.world n).time ≤ (e.world k).time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
      target.epoch.toNat + 2 ≤ current.toNat →
      ∀ root rootEpoch, ((e.world k).state w).getBlockEpoch root = .ok rootEpoch →
      rootEpoch ≤ target.epoch →
      ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
      (∀ time, (e.world n).time ≤ time → time < (e.world k).time → SafeAt e time root) →
      ∃ (seed : Root) (seedBlock : BeaconBlock preset fork) (seedState : BeaconState preset fork),
        ((e.world k).state w).blocks[seed]? = some seedBlock ∧
        ((e.world k).state w).blockStates[seed]? = some seedState ∧
        ((e.world k).state w).isAncestor ⟨seed, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
        target.epoch ≤ computeEpochAtSlot preset seedBlock.slot ∧
        (computeEpochAtSlot preset seedBlock.slot).toNat < target.epoch.toNat + 2 ∧
        getBlockRoot seedState target.epoch = .ok target.root ∧
        (target.epoch ≤ seedState.currentJustifiedCheckpoint.epoch ∨
          (∃ altair : .altair ≤ fork, ∀ v ∈ voters,
            TargetFlagAt (recentParticipation seedState altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
          ∃ before : fork < .altair, ∀ v ∈ voters,
            ∃ pending ∈ recentPending seedState before
                (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
              pending.data.target = target ∧
              ∃ indices, getPendingAttestingIndices seedState pending = .ok indices ∧
                v ∈ indices)

/-- A block extends an origin whose target the rule checked in the block's epoch.

The origin and the block have the same epoch, which can precede the current epoch.

The anchor is an origin without a target check.

For any other origin, an earlier up-to-date call checked a head above that origin.

There the rule found that the target of the epoch will be justified.

That call was at the start of its slot, and the record keeps that time.

Honest validators held the count of the rule for that target.

They held it with the margin plus the quorum reserve of the pulled-up state and the target state.

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
      (∀ state target anc,
        ((e.world k).state u).getPulledUpHeadState config head.root = .ok state →
        ((e.world k).state u).getCurrentTarget config head.root = .ok target →
        ((e.world k).state u).blockStates[target.root]? = some anc →
        HonestTargetVotes e (margin + quorumReserve config state anc) u k head.root) ∧
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
  fun u caller q n ordered nBound head state total target voters headOk stateOk targetOk totalOk
    epochOk confirmedOk quorum next first begin nextOk firstOk beginOk signed w receiver k current
    kBound =>
    included u caller q n ordered (nBound.trans le) head state total target voters headOk stateOk
      targetOk totalOk epochOk confirmedOk quorum next first begin nextOk firstOk beginOk signed w
      receiver k current (kBound.trans le)

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
private theorem walk_cache_origin_state {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (before : fork < .glamsterdam) {key : Root} {checkpoint : Checkpoint}
    (entry : store.unrealizedJustifications[key]? = some checkpoint) :
    (checkpoint.epoch = getCurrentEpoch anchorState ∧
      store.blockStates[key]? = some anchorState) ∨
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
        exact .inl ⟨rfl, by simp_all⟩
      · simp at entry
  | tick prior ticked ih =>
    rw [walk_tick_cache ticked] at entry
    rcases ih entry with old | ⟨state, pulled, held, processed, same⟩
    · exact .inl ⟨old.1, (Store.onTick_frame ticked).2.2.2.symm ▸ old.2⟩
    · exact .inr ⟨state, pulled, (Store.onTick_frame ticked).2.2.2.symm ▸ held,
        processed, same⟩
  | @block prior after checks sources signed reachable added ih =>
    rcases walk_block_cache added entry with old | fresh
    · rcases ih old with old | ⟨state, pulled, held, processed, same⟩
      · left
        refine ⟨old.1, ?_⟩
        rcases Store.onBlock_same_or_insert added with eq |
          ⟨newRoot, _, fresh, _, _, _, _, _, states⟩
        · exact eq ▸ old.2
        have other : newRoot ≠ key := by
          rintro rfl
          have absent := reachable.blockState_eq_none fresh
          rw [old.2] at absent
          cases absent
        rw [states, getElem?_insert_root]
        simpa only [other, ↓reduceIte] using old.2
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
    · exact .inl ⟨old.1, (Store.onAttestation_frame attested).2.2.symm ▸ old.2⟩
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

theorem walk_cache_origin {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (before : fork < .glamsterdam) {key : Root} {checkpoint : Checkpoint}
    (entry : store.unrealizedJustifications[key]? = some checkpoint) :
    checkpoint.epoch = getCurrentEpoch anchorState ∨
      ∃ state pulled, store.blockStates[key]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = checkpoint :=
  (walk_cache_origin_state reachable before entry).imp And.left id

/-- A cached unrealized justification is no older than the stored realized justification. -/
theorem walk_realized_le_unrealized {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    {root : Root} {state : BeaconState preset fork} {checkpoint : Checkpoint}
    (stored : store.blockStates[root]? = some state)
    (entry : store.unrealizedJustifications[root]? = some checkpoint) :
    state.currentJustifiedCheckpoint.epoch ≤ checkpoint.epoch := by
  rcases walk_cache_origin_state reachable before entry with ⟨epoch, held⟩ |
    ⟨base, pulled, held, run, same⟩
  · rw [stored, Option.some.injEq] at held
    subst state
    rw [epoch]
    exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
  · rw [stored, Option.some.injEq] at held
    subst base
    rw [← same]
    exact processJustificationAndFinalization_currentJustified_mono
      ((reachable.ordered sound).2 stored).settled run

/-- Realized justification cannot decrease along a held descendant chain. -/
theorem walk_realized_mono {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    {root tip : Root} {block : BeaconBlock preset fork}
    {base state : BeaconState preset fork}
    (known : store.blocks[root]? = some block)
    (baseStored : store.blockStates[root]? = some base)
    (tipStored : store.blockStates[tip]? = some state)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    base.currentJustifiedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch := by
  have walk := Store.getAncestor_of_isAncestor_of_lt before known descends
  have aboveAnchor := reachable.anchorSlot_le_block known
  generalize nodeEq : (⟨tip, .pending⟩ : ForkChoiceNode) = node at walk
  have stored : store.blockStates[node.root]? = some state := by
    rw [← nodeEq]
    exact tipStored
  clear nodeEq tipStored descends
  induction node using Store.getAncestor.induct (store := store) (slot := block.slot)
      generalizing state with
  | case1 node found =>
    rw [Store.getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node current found le =>
    rw [Store.getAncestor_of_le found le] at walk
    cases walk
    rw [baseStored, Option.some.injEq] at stored
    subst state
    exact UInt64.le_refl _
  | case3 node current found above parentFound =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst b
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node current found above parent parentFound lower ih =>
    have notAnchor : current ≠ anchorBlock := by
      intro eq
      exact above (eq ▸ aboveAnchor)
    obtain ⟨post, postStored, _, origin⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postStored
    subst post
    obtain ⟨parentState, _, _, signed, _, parentStored, run⟩ := origin notAnchor
    rw [Store.getAncestor_step found above parentFound lower] at walk
    exact UInt64.le_trans (ih walk parentStored)
      (stateTransition_currentJustified_mono ((reachable.ordered sound).2 parentStored) run)
  | case5 node current found above parent parentFound notLower =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst b
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p same
        rw [parentFound, Option.some.injEq] at same
        subst p
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- Every descendant source is at least as recent as the root's realized justification. -/
theorem walk_realized_le_source {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    {root tip : Root} {block : BeaconBlock preset fork} {base : BeaconState preset fork}
    {source : Checkpoint}
    (known : store.blocks[root]? = some block)
    (stored : store.blockStates[root]? = some base)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : store.getVotingSource config tip = .ok source) :
    base.currentJustifiedCheckpoint.epoch ≤ source.epoch := by
  unfold Store.getVotingSource at read
  simp only [bind_ok_iff] at read
  obtain ⟨tipBlock, tipRead, current, _, read⟩ := read
  obtain ⟨state, held, _⟩ := reachable.blockStatesFromParents
    (Store.block_ok_iff.mp tipRead)
  have mono := walk_realized_mono reachable sound before known stored held descends
  split at read
  · cases entry : store.unrealizedJustifications[tip]? with
    | none => simp [entry] at read
    | some checkpoint =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at read
      subst source
      exact UInt64.le_trans mono (walk_realized_le_unrealized reachable sound before held entry)
  · simp only [held, pure, Except.pure, Except.ok.injEq] at read
    subst source
    exact mono

/-- In the early window, every descendant source inherits the root's realized recency. -/
theorem walk_source_recent_of_realized {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (before : fork < .glamsterdam)
    {root tip : Root} {block : BeaconBlock preset fork} {base : BeaconState preset fork}
    {epoch : Epoch} {source : Checkpoint}
    (known : store.blocks[root]? = some block)
    (stored : store.blockStates[root]? = some base)
    (recent : (computeEpochAtSlot preset block.slot).toNat ≤
      base.currentJustifiedCheckpoint.epoch.toNat + 1)
    (early : epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : store.getVotingSource config tip = .ok source) :
    epoch.toNat ≤ source.epoch.toNat + 2 := by
  have lower := UInt64.le_iff_toNat_le.mp
    (walk_realized_le_source reachable sound before known stored descends read)
  omega

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

omit [DecidablePred (· ∈ J)] in
/-- An early receiver reads its finality on each descendant of a realized-recent root. -/
theorem Execution.early_source_recent_and_finalized {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (before : fork < .glamsterdam) {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last) (oneBlock : OneBlockPerRoot e last)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {epoch : Epoch}
    (receiverEpoch : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (anchorHorizon : getCurrentEpoch anchorState ≤ horizon)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {root tip : Root} {block tipBlock : BeaconBlock preset fork}
    {base : BeaconState preset fork} {source : Checkpoint}
    (callerKnown : ((e.world n).state u).blocks[root]? = some block)
    (callerStored : ((e.world n).state u).blockStates[root]? = some base)
    (known : ∃ b, ((e.world k).state w).blocks[root]? = some b)
    (tipKnown : ((e.world k).state w).blocks[tip]? = some tipBlock)
    (recent : (computeEpochAtSlot preset block.slot).toNat ≤
      base.currentJustifiedCheckpoint.epoch.toNat + 1)
    (early : epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (descends : ((e.world k).state w).isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : ((e.world k).state w).getVotingSource config tip = .ok source) :
    epoch.toNat ≤ source.epoch.toNat + 2 ∧
      ((e.world k).state w).getCheckpointBlock tip
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root := by
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  obtain ⟨other, held⟩ := known
  have blockEq := oneBlock u caller w receiver n k nBound kBound root block other callerKnown held
  subst other
  obtain ⟨state, stored, _⟩ := forward.reachable.blockStatesFromParents held
  have stateEq := e.blockStates_eq anchorStore caller receiver (anchored u caller)
    (anchored w receiver) (oneBlock u caller w receiver n k nBound kBound) callerStored stored
  subst state
  have recency := walk_source_recent_of_realized forward.reachable sound before
    held stored recent early descends read
  refine ⟨recency, ?_⟩
  by_cases child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b ∧ b ≠ anchorBlock
  · exact walk_finalized_read_of_recent_source anchorStore anchored sound slots positive window
      anchorSlot anchorBoundary before chain receiver receiver kBound kBound receiverEpoch
      receiverEpoch inHorizon anchorHorizon nonzero child tipKnown (.inl read) recency
  have allAnchor {r : Root} {b : BeaconBlock preset fork}
      (held : ((e.world k).state w).blocks[r]? = some b) : b = anchorBlock := by
    by_contra different
    exact child ⟨r, b, held, different⟩
  have upper : epoch.toNat ≤ (getCurrentEpoch anchorState).toNat + 1 := by
    rw [allAnchor held, anchorSlot] at early
    exact early
  rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound
      (anchored w receiver) receiverEpoch with same | age
  · rw [same]
    exact walk_anchor_read anchorStore anchored anchorSlot anchorBoundary before receiver tipKnown
  · have anchorFinal := (getForkchoiceStore_anchor anchorStore)
    obtain ⟨_, _, ages⟩ := resetAge_forward anchorStore sound slots forward
    have finalLower := ages.2.2.1
    have epochEq : anchor.finalizedCheckpoint.epoch = getCurrentEpoch anchorState := by
      obtain ⟨r, _, _, _, _, eq, _⟩ := anchorFinal
      simp [eq]
    rw [epochEq, UInt64.le_iff_toNat_le] at finalLower
    omega

/-- An aligned store reads each post-anchor justification on a held carrier. -/
theorem justified_read_of_anchor_aligned {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork), store.blocks[r]? = some b →
      b.stateRoot ≠ Vector.replicate 32 0)
    {checkpoint : Checkpoint}
    (selected : checkpoint = store.justifiedCheckpoint ∨
      checkpoint = store.unrealizedJustifiedCheckpoint)
    (recent : getCurrentEpoch anchorState < checkpoint.epoch) :
    ∃ root, store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root := by
  have child : ∃ (r : Root) (b : BeaconBlock preset fork),
      store.blocks[r]? = some b ∧ b ≠ anchorBlock := by
    by_contra absent
    have allAnchor {r : Root} {s : BeaconState preset fork}
        (held : store.blockStates[r]? = some s) : s = anchorState := by
      obtain ⟨b, known⟩ := reached.known_of_blockState held
      have same : b = anchorBlock := by
        by_contra other
        exact absent ⟨r, b, known, other⟩
      obtain ⟨post, found, anchored, _⟩ := reached.blockStatesFromParents known
      rw [held, Option.some.injEq] at found
      subst post
      exact anchored same
    have upper : checkpoint.epoch ≤ getCurrentEpoch anchorState := by
      rcases reached.justified_origins checkpoint selected with
        ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
      · exact eq ▸ UInt64.le_refl _
      · rw [eq, allAnchor held]
        exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
      · rw [allAnchor held] at pulled
        rw [eq]
        exact (processJustificationAndFinalization_invariant sound.ordered sound.settled
          pulled).2.2.1
    exact UInt64.not_le.mpr recent upper
  have aligned := UInt64.le_of_eq anchorSlot
  rcases reached.justified_origins checkpoint selected with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
  · rw [same] at recent
    exact (UInt64.lt_irrefl _ recent).elim
  · rcases (walk_checkpoint_ancestor reached sound preGloas positive window aligned nonzero
      child stored).2.1 with early | ⟨_, _, _, _, _, _, read⟩
    · exact (UInt64.not_le.mpr recent (same ▸ early)).elim
    · exact ⟨root, same ▸ read⟩
  · rcases (walk_pulled_checkpoint_ancestor reached sound preGloas positive window aligned nonzero
      child stored run).2.1 with early | ⟨_, _, _, _, _, _, read⟩
    · exact (UInt64.not_le.mpr recent (same ▸ early)).elim
    · exact ⟨root, same ▸ read⟩

/-- A non-anchor head reads its honest target on its own chain after the anchor epoch. -/
theorem reset_honest_target_read {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → block.stateRoot ≠ Vector.replicate 32 0)
    {head : ForkChoiceNode} {block : BeaconBlock preset fork}
    {headState state : BeaconState preset fork} {slot : Slot} {committee : CommitteeIndex}
    {data : AttestationData}
    (found : store.blocks[head.root]? = some block)
    (stored : store.blockStates[head.root]? = some headState)
    (other : block ≠ anchorBlock)
    (advanced : lookaheadState config checks headState slot = .ok state)
    (made : getAttestationData state head.root block.slot committee head.payloadStatus = .ok data)
    (later : getCurrentEpoch anchorState < data.target.epoch) :
    store.getCheckpointBlock data.beaconBlockRoot data.target.epoch = .ok data.target.root := by
  obtain ⟨_, boundary, _, dataRoot, _, epoch⟩ := getAttestationData_eq_ok_iff.mp made
  have headLe : block.slot ≤ state.slot := by
    have le := reached.blockState_slot_le aligned found stored
    unfold lookaheadState at advanced
    split at advanced
    · have bounds := processSlots_slot (mapError_ok_iff.mp advanced)
      rw [bounds.2]
      exact UInt64.le_trans le (UInt64.le_of_lt bounds.1)
    · cases Except.ok.inj advanced
      exact le
  let first := state.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH
  have firstOk : computeStartSlotAtEpoch preset data.target.epoch = .ok first := by
    rw [epoch]
    exact computeStartSlotAtEpoch_computeEpochAtSlot state.slot
  have afterAnchor : anchorState.slot ≤ first := by
    have lower := UInt64.lt_iff_toNat_lt.mp later
    rw [getCurrentEpoch_toNat] at lower
    have lt := (Nat.div_lt_iff_lt_mul positive).mp lower
    have eq := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  rw [dataRoot]
  unfold Store.getCheckpointBlock
  rw [firstOk]
  simp only [Except.mapError, bind, Except.bind]
  change (·.root) <$> store.getAncestor ⟨head.root, .pending⟩ first = _
  rcases getEpochBoundaryBlockRoot_eq_ok_iff.mp boundary with ⟨onBoundary, targetEq⟩ | ⟨_, read⟩
  · have eq : first = state.slot := div_mul_eq_self_iff.mpr onBoundary
    rw [eq, Store.getAncestor_of_le (node := ⟨head.root, .pending⟩) found headLe]
    simp [targetEq]
  · have read' : getBlockRootAtSlot state first = .ok data.target.root := by
      unfold getBlockRoot at read
      rw [← epoch, firstOk] at read
      exact read
    unfold lookaheadState at advanced
    split at advanced
    · have ran := mapError_ok_iff.mp advanced
      by_cases old : first < headState.slot
      · have run := ran
        simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
        obtain ⟨_, _, advancedOk⟩ := run
        exact reached.blockState_history_ancestor aligned nonzero stored
          (getBlockRootAtSlot_of_advanceSlots advancedOk read' old) afterAnchor .pending
      · have eq := reached.blockState_processSlots_root found stored other (nonzero _ _ found)
          ran read' (UInt64.le_trans (reached.blockState_slot_le aligned found stored)
            (UInt64.not_lt.mp old))
        rw [Store.getAncestor_of_le (node := ⟨head.root, .pending⟩) found
          (UInt64.le_trans (reached.blockState_slot_le aligned found stored)
            (UInt64.not_lt.mp old))]
        simp only [Functor.map, Except.map, eq]
    · cases Except.ok.inj advanced
      exact reached.blockState_history_ancestor aligned nonzero stored read' afterAnchor .pending

omit [DecidablePred (· ∈ J)] in
/-- A later justified checkpoint covers a root safe since the earlier epoch boundary. -/
private theorem coverage_covered_of_later_justified {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {limit : ℕ} {anchorEpoch horizon : Epoch}
    (oneBlock : OneBlockPerRoot e limit)
    (voted : JustifiedByHonestVote e anchorEpoch horizon limit)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (nonzero : ∀ v ∈ J, ∀ i, (e.world i).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world i).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ}
    (kBound : (e.world k).time ≤ limit)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {slot first : Slot} {epoch : Epoch} {begin : UInt64}
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs first = .ok begin)
    {checkpoint : Checkpoint}
    (justified : ((e.world k).state w).Justified checkpoint)
    (afterAnchor : anchorEpoch < checkpoint.epoch) (bounded : checkpoint.epoch ≤ horizon)
    (later : epoch ≤ checkpoint.epoch)
    {root : Root} {rootBlock checkpointBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (checkpointKnown : ((e.world k).state w).blocks[checkpoint.root]? = some checkpointBlock)
    (rootBefore : rootBlock.slot ≤ first)
    (safe : ∀ t, begin.toNat ≤ t → t < (e.world k).time → SafeAt e t root) :
    ((e.world k).state w).isAncestor ⟨checkpoint.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true := by
  obtain ⟨v, honest, signer, data, supportHead, duty, target, _, beforeTime,
      supportHeadOk, supports⟩ := e.exists_supporting_head_of_justified_epoch_start fits voted
    anchored receiver kBound justified slotOk ready afterAnchor bounded firstOk beginOk later safe
  have signerBound := beforeTime.le.trans kBound
  have reached := e.reachable
    (fun a ha => (anchored a ha) ▸ Store.Reachable.anchor anchorStore) signer v honest
  have received := e.reachable
    (fun a ha => (anchored a ha) ▸ Store.Reachable.anchor anchorStore) k w receiver
  obtain ⟨committee, _, _, _, _, honestData, _⟩ := duty
  obtain ⟨tip, tipBlock, headState, state, tipOk, tipKnown, stored, advanced, made⟩ := honestData
  have tipEq := Except.ok.inj (tipOk.symm.trans supportHeadOk)
  subst tip
  have rootRead := supports
  unfold Store.isAncestor at rootRead
  obtain ⟨otherRoot, otherOk, _⟩ := bind_ok_iff.mp rootRead
  have otherKnown := Store.block_ok_iff.mp otherOk
  have rootEq := oneBlock v honest w receiver signer k signerBound kBound root
    otherRoot rootBlock otherKnown known
  subst otherRoot
  obtain ⟨_, _, _, _, anchorJustified, _⟩ := getForkchoiceStore_anchor anchorStore
  have afterAnchor' : getCurrentEpoch anchorState < data.target.epoch := by
    rw [target]
    have bound := afterAnchor
    rw [← anchorOk, anchorJustified] at bound
    exact bound
  by_cases same : tipBlock = anchorBlock
  · have lower := reached.anchorSlot_le_block otherKnown
    have walk := Store.getAncestor_of_isAncestor_of_lt preGloas otherKnown supports
    rw [Store.getAncestor_of_le tipKnown (same.symm ▸ lower)] at walk
    have eq := congrArg ForkChoiceNode.root (Except.ok.inj walk)
    obtain ⟨anchorRoot, hashed, _, _, _, final, _⟩ := getForkchoiceStore_anchor anchorStore
    have hash := reached.root tipKnown
    rw [same, hashed, Except.ok.injEq] at hash
    have rootEq : root = anchor.finalizedCheckpoint.root := by
      rw [final]
      exact eq.symm.trans hash.symm
    simpa only [← rootEq] using
      e.isAncestor_anchor_of_known anchorStore anchored receiver checkpointKnown
  have targetRead := reset_honest_target_read reached positive (UInt64.le_of_eq anchorSlot)
    (nonzero v honest signer signerBound) tipKnown (Store.blockState_ok_iff.mp stored)
    same advanced made afterAnchor'
  have dataRoot := (getAttestationData_eq_ok_iff.mp made).2.2.2.1
  rw [dataRoot] at targetRead
  unfold Store.getCheckpointBlock at targetRead
  simp only [bind_ok_iff] at targetRead
  obtain ⟨targetSlot, targetSlotOk, targetNode, targetWalk, targetRoot⟩ := targetRead
  have targetSlotOk := mapError_ok_iff.mp targetSlotOk
  have nodeEq : targetNode = (⟨checkpoint.root, .pending⟩ : ForkChoiceNode) := by
    have rootEq := (Except.ok.inj targetRoot).trans (congrArg Checkpoint.root target)
    have status := Store.getAncestor_pending_of_lt preGloas rfl targetWalk
    cases targetNode
    exact congrArg₂ ForkChoiceNode.mk rootEq status
  subst targetNode
  have belowTarget : rootBlock.slot ≤ targetSlot := by
    have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
    have targetNat := (computeStartSlotAtEpoch_ok_iff.mp targetSlotOk).2
    rw [target] at targetNat
    have le := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (UInt64.le_iff_toNat_le.mp later)
    have firstBelow : first ≤ targetSlot := UInt64.le_iff_toNat_le.mpr (by omega)
    exact UInt64.le_trans rootBefore firstBelow
  have sourceWalk := Store.getAncestor_of_isAncestor_of_lt preGloas otherKnown supports
  have targetAncestor : ((e.world signer).state v).getAncestor
      ⟨checkpoint.root, .pending⟩ rootBlock.slot = .ok ⟨root, .pending⟩ := by
    have roots := Store.getAncestor_root (store := (e.world signer).state v)
      supportHead .pending rootBlock.slot
    rw [sourceWalk, Store.getAncestor_trans belowTarget targetWalk] at roots
    cases walk : ((e.world signer).state v).getAncestor
        ⟨checkpoint.root, .pending⟩ rootBlock.slot with
    | error error => simp [walk] at roots
    | ok node =>
      have rootEq : node.root = root := by simpa [walk] using roots.symm
      have status := Store.getAncestor_pending_of_lt preGloas rfl walk
      have eq : node = (⟨root, .pending⟩ : ForkChoiceNode) := by
        cases node
        exact congrArg₂ ForkChoiceNode.mk rootEq status
      exact congrArg Except.ok eq
  have copied := Store.getAncestor_of_same_blocks received
    (oneBlock v honest w receiver signer k signerBound kBound)
    (received.anchorSlot_le_block known) ⟨checkpointBlock, checkpointKnown⟩ targetAncestor
  simp [Store.isAncestor, Store.block_ok_iff.mpr known, copied,
    bind, Except.bind, pure, Except.pure]

/-- Two pending ancestors of one head are comparable before Gloas. -/
theorem coverage_ancestors_comparable {store : Store preset fork}
    (before : fork < .glamsterdam) {head : ForkChoiceNode} {a b : Root}
    {aBlock bBlock : BeaconBlock preset fork}
    (aKnown : store.blocks[a]? = some aBlock) (bKnown : store.blocks[b]? = some bBlock)
    (ha : store.isAncestor head ⟨a, .pending⟩ = .ok true)
    (hb : store.isAncestor head ⟨b, .pending⟩ = .ok true) :
    store.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true ∨
      store.isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true := by
  have aw := Store.getAncestor_of_isAncestor_of_lt before aKnown ha
  have bw := Store.getAncestor_of_isAncestor_of_lt before bKnown hb
  rcases UInt64.le_total bBlock.slot aBlock.slot with le | le
  · left
    have walk := (Store.getAncestor_trans le aw).symm.trans bw
    simp [Store.isAncestor, Store.block_ok_iff.mpr bKnown, walk,
      bind, Except.bind, pure, Except.pure]
  · right
    have walk := (Store.getAncestor_trans le bw).symm.trans aw
    simp [Store.isAncestor, Store.block_ok_iff.mpr aKnown, walk,
      bind, Except.bind, pure, Except.pure]

omit [DecidablePred (· ∈ J)] in
/-- Exclusion from the caller's past committees places an unseen duty after the call. -/
theorem Execution.unseen_signer_time
    {limit : ℕ} (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n k : ℕ}
    (bounded : (e.world n).time ≤ limit)
    (forward : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u))
    {head : ForkChoiceNode} {slot first last receiverSlot : Slot} {begin endTime : UInt64}
    {participants : Std.TreeSet ValidatorIndex} {data : AttestationData}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first)
    (lastOk : subChecked slot 1 = .ok last)
    (found : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants)
    (unseen : v ∉ participants)
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k).time ((e.world k).view v) ((e.world k).state v) data)
    (epoch : data.target.epoch = computeEpochAtSlot preset slot)
    (before : data.slot < receiverSlot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (endOk : computeTimeAtSlotMs config genesisTimeMs receiverSlot = .ok endTime) :
    begin.toNat ≤ (e.world k).time ∧ (e.world k).time < endTime.toNat := by
  obtain ⟨index, assigned, deadline, _, _, made, _⟩ := duty
  obtain ⟨_, _, _, _, _, _, _, _, dataOk⟩ := made
  have dataEpoch := target_epoch_eq_of_getAttestationData dataOk
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have slotPositive := (subChecked_ok_iff.mp lastOk).1
  have past : last < slot := UInt64.lt_iff_toNat_lt.mpr (by
    simp only [UInt64.toNat_one] at lastNat slotPositive; omega)
  have inRange := committees.assigned_current_epoch retained caller bounded forward
    headOk slotOk firstOk past found v honest
  have firstLe : first ≤ data.slot := by
    rw [UInt64.le_iff_toNat_le, firstNat, ← epoch, dataEpoch]
    exact Nat.div_mul_le_self _ _
  have after : slot ≤ data.slot := by
    by_contra earlier
    have lastLe : data.slot ≤ last := UInt64.le_iff_toNat_le.mpr (by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp earlier)
      simp only [UInt64.toNat_one] at lastNat
      omega)
    exact unseen (inRange.mpr ⟨data.slot, index, firstLe, lastLe, assigned⟩)
  constructor
  · obtain ⟨start, due, startOk, _, timeEq⟩ := deadline
    obtain ⟨begin', beginOk', _, le⟩ := exists_timeAtSlotMs_of_le after startOk
    have eq := Except.ok.inj (beginOk.symm.trans beginOk')
    subst begin'
    have := UInt64.le_iff_toNat_le.mp le
    omega
  · have := fits.deadline_lt_later_slot before endOk deadline
    omega

omit [DecidablePred (· ∈ J)] in
/-- The count of the rule for a head names its target, its committees and the honest voters. -/
theorem coverage_quorum_of_count {u : ValidatorIndex} {n margin : ℕ}
    {head : Root} (count : HonestTargetVotes e margin u n head)
    {state : BeaconState preset fork} {support : Gwei}
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (supportOk : ((e.world n).state u).computeHonestFfgSupportForCurrentTarget config head =
      .ok support) :
    ∃ target slot first last participants, ∃ voters : Finset ValidatorIndex,
      ((e.world n).state u).getCurrentTarget config head = .ok target ∧
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch ∧
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first ∧
      subChecked slot 1 = .ok last ∧
      ((e.world n).state u).getCommitteesBetweenSlots head first last = .ok participants ∧
      ((e.world n).state u).getCheckpointBlock head target.epoch = .ok target.root ∧
      (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
        (SignsTarget e v target (e.world n).time ∨ v ∉ participants)) ∧
      3 * support.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters := by
  have supportRead := supportOk
  simp only [Store.computeHonestFfgSupportForCurrentTarget, bind_ok_iff, mapError_ok_iff]
    at supportRead
  obtain ⟨slot, slotOk, readState, stateRead, total, totalOk, score, scoreOk, first, firstOk,
    last, lastOk, weight, weightOk, _⟩ := supportRead
  have stateEq := Except.ok.inj (stateRead.symm.trans stateOk)
  subst readState
  have targetScore := scoreOk
  unfold Store.getCurrentTargetScore at targetScore
  obtain ⟨target, targetOk, _⟩ := bind_ok_iff.mp targetScore
  obtain ⟨_, adversary, _, adversaryOk, _⟩ :=
    Store.computeHonestFfgSupportForCurrentTarget_eq stateOk slotOk totalOk firstOk lastOk
      weightOk supportOk
  obtain ⟨_, _, _, _, _, equivocationOk, _⟩ :=
    Store.computeAdversarialWeight_steps adversaryOk
  unfold Store.getEquivocationScore at equivocationOk
  obtain ⟨participants, participantsOk, _⟩ := bind_ok_iff.mp equivocationOk
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have targetRead := targetOk
  simp only [Store.getCurrentTarget, epochOk, Store.getCheckpointForBlock, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at targetRead
  obtain ⟨_, rfl, root, checkpointOk, rfl⟩ := targetRead
  obtain ⟨voters, members, bound⟩ := count state support
    ⟨computeEpochAtSlot preset slot, root⟩ slot first last participants
    stateOk supportOk targetOk slotOk firstOk lastOk participantsOk
  exact ⟨_, slot, first, last, participants, voters, targetOk,
    slotOk, epochOk, firstOk, lastOk, participantsOk, checkpointOk, members, by omega⟩

/-- The no-conflict check either reads an already justified target or supplies strict stake. -/
private theorem coverage_no_conflict_cases {store : Store preset fork} {head : Root}
    (checked : store.willNoConflictingCheckpointBeJustified config head = .ok true) :
    store.getCurrentTarget config head = .ok store.unrealizedJustifiedCheckpoint ∨
      ∃ state total support,
        store.getPulledUpHeadState config head = .ok state ∧
        getTotalActiveBalance state = .ok total ∧
        store.computeHonestFfgSupportForCurrentTarget config head = .ok support ∧
        total.toNat < 3 * support.toNat := by
  unfold Store.willNoConflictingCheckpointBeJustified at checked
  obtain ⟨target, targetOk, checked⟩ := bind_ok_iff.mp checked
  split at checked
  · rename_i same
    exact .inl (same ▸ targetOk)
  · right
    simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at checked
    obtain ⟨state, stateOk, total, totalOk, support, supportOk, product, productOk, lt⟩ := checked
    have productNat := (mulChecked_ok_iff.mp productOk).2
    have lt := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true lt)
    exact ⟨state, total, support, stateOk, totalOk, supportOk, by
      simp only [UInt64.toNat_ofNat] at productNat
      omega⟩

/-- Same-block agreement transports pending ancestry to a receiver holding both roots. -/
private theorem coverage_copy_ancestor {sender receiver : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock receiver)
    (before : fork < .glamsterdam)
    (same : ∀ (r : Root) (b c : BeaconBlock preset fork),
      sender.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    {a b : Root} {aBlock bBlock : BeaconBlock preset fork}
    (aKnown : receiver.blocks[a]? = some aBlock) (bKnown : receiver.blocks[b]? = some bBlock)
    (above : sender.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true) :
    receiver.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true := by
  have read := above
  unfold Store.isAncestor at read
  obtain ⟨block, blockOk, _⟩ := bind_ok_iff.mp read
  have held := Store.block_ok_iff.mp blockOk
  have eq := same _ _ _ held bKnown
  subst block
  have walk := Store.getAncestor_of_isAncestor_of_lt before held above
  have copied := Store.getAncestor_of_same_blocks reached same
    (reached.anchorSlot_le_block bKnown) ⟨aBlock, aKnown⟩ walk
  simp [Store.isAncestor, Store.block_ok_iff.mpr bKnown, copied,
    bind, Except.bind, pure, Except.pure]

/-- A block at or before an epoch boundary is below the checkpoint of each block above it. -/
private theorem coverage_below_checkpoint {store : Store preset fork}
    (before : fork < .glamsterdam) {head root checkpoint : Root} {epoch : Epoch}
    {block : BeaconBlock preset fork} {boundary : Slot}
    (known : store.blocks[root]? = some block)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (early : block.slot ≤ boundary)
    (read : store.getCheckpointBlock head epoch = .ok checkpoint) :
    store.isAncestor ⟨checkpoint, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  unfold Store.getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨readBoundary, readBoundaryOk, ancestor, walk, rootEq⟩ := read
  have same := Except.ok.inj ((mapError_ok_iff.mp readBoundaryOk).symm.trans boundaryOk)
  subst readBoundary
  have pending := Store.getAncestor_pending_of_lt before rfl walk
  have eq : ancestor = ⟨checkpoint, .pending⟩ := by
    cases ancestor
    simp_all
  subst ancestor
  have rootWalk := Store.getAncestor_of_isAncestor_of_lt before known descends
  rw [Store.getAncestor_trans early walk] at rootWalk
  exact ancestor_pending_of_walk known ⟨_, rootWalk, rfl, fun _ => rfl⟩

/-- A target read on a supporting head makes its checkpoint comparable with the root.

A checkpoint below the root is below it only when the root is after the checkpoint's boundary. -/
private theorem coverage_comparable_of_target_read {sender receiver : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock receiver)
    (before : fork < .glamsterdam)
    (same : ∀ (r : Root) (b c : BeaconBlock preset fork),
      sender.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    {head : ForkChoiceNode} {root : Root} {checkpoint : Checkpoint}
    {rootBlock checkpointBlock : BeaconBlock preset fork}
    (known : receiver.blocks[root]? = some rootBlock)
    (checkpointKnown : receiver.blocks[checkpoint.root]? = some checkpointBlock)
    (supports : sender.isAncestor head ⟨root, .pending⟩ = .ok true)
    (read : sender.getCheckpointBlock head.root checkpoint.epoch = .ok checkpoint.root) :
    receiver.isAncestor ⟨checkpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      receiver.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
        ∀ boundary, computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary →
          boundary < rootBlock.slot := by
  obtain ⟨_, block, _, held, _, targetAbove⟩ :=
    Store.isAncestor_of_getCheckpointBlock before read
  have supportRead := supports
  unfold Store.isAncestor at supportRead
  obtain ⟨rb, rbOk, _⟩ := bind_ok_iff.mp supportRead
  have rk := Store.block_ok_iff.mp rbOk
  have supportWalk := Store.getAncestor_of_isAncestor_of_lt before rk supports
  have pendingSupport : sender.isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true := by
    have roots := Store.getAncestor_root (store := sender) head .pending rb.slot
    rw [supportWalk] at roots
    cases walk : sender.getAncestor ⟨head.root, .pending⟩ rb.slot with
    | error err => simp [walk] at roots
    | ok node =>
      have eq : node = (⟨root, .pending⟩ : ForkChoiceNode) := by
        have rootEq : node.root = root := by simpa [walk] using roots.symm
        have status := Store.getAncestor_pending_of_lt before rfl walk
        cases node
        exact congrArg₂ ForkChoiceNode.mk rootEq status
      subst node
      simp [Store.isAncestor, rbOk, walk, bind, Except.bind, pure, Except.pure]
  rcases coverage_ancestors_comparable before held rk targetAbove pendingSupport with h | h
  · exact .inl (coverage_copy_ancestor reached before same checkpointKnown known h)
  by_cases early : ∃ boundary, computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary ∧
      rootBlock.slot ≤ boundary
  · obtain ⟨boundary, boundaryOk, le⟩ := early
    have eq := same _ _ _ rk known
    subst eq
    exact .inl (coverage_copy_ancestor reached before same checkpointKnown known
      (coverage_below_checkpoint before rk pendingSupport boundaryOk le read))
  · push Not at early
    exact .inr ⟨coverage_copy_ancestor reached before same known checkpointKnown h,
      fun boundary boundaryOk => UInt64.not_le.mp (early boundary boundaryOk)⟩

omit [DecidablePred (· ∈ J)] in
/-- An off-start numeric check makes a same-epoch justification comparable with the root. -/
private theorem coverage_comparable_of_numeric_check {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS)
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {limit : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    (oneBlock : OneBlockPerRoot e limit)
    (pins : HonestThirdPins e anchorEpoch horizon margin limit)
    (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (nonzero : ∀ v ∈ J, ∀ i, (e.world i).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world i).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {head : ForkChoiceNode} {root : Root} {checkpoint : Checkpoint}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (onChain : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    (count : HonestTargetVotes e margin u n head.root)
    {state : BeaconState preset fork} {total support : Gwei}
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head.root = .ok state)
    (totalOk : getTotalActiveBalance state = .ok total)
    (supportOk : ((e.world n).state u).computeHonestFfgSupportForCurrentTarget config head.root =
      .ok support)
    (enough : total.toNat < 3 * support.toNat)
    {slot receiverSlot : Slot} {epoch : Epoch} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    (receiverSlotOk : ((e.world k).state w).getCurrentSlot config = .ok receiverSlot)
    (justified : ((e.world k).state w).Justified checkpoint)
    (checkpointEpoch : checkpoint.epoch = epoch)
    (afterAnchor : anchorEpoch < epoch) (bounded : epoch ≤ horizon)
    {rootBlock checkpointBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (checkpointKnown : ((e.world k).state w).blocks[checkpoint.root]? = some checkpointBlock)
    (safe : ∀ t, (e.world n).time ≤ t → t < (e.world k).time → SafeAt e t root) :
    ((e.world k).state w).isAncestor ⟨checkpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ =
          .ok true ∧
        ∀ boundary, computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary →
          boundary < rootBlock.slot := by
  obtain ⟨target, current, first, last, participants, voters, targetOk, currentOk, targetEpochOk,
    firstOk, lastOk, participantsOk, targetRead, members, counted⟩ :=
    coverage_quorum_of_count count stateOk supportOk
  have large : total.toNat + margin < 3 * stake (fun v => balanceAt state v.toNat) voters := by
    omega
  have currentEq := Except.ok.inj (currentOk.symm.trans slotOk)
  subst current
  have targetEpoch := Except.ok.inj (targetEpochOk.symm.trans epochOk)
  have forward := e.forwardReachable
    (fun a ha => (anchored a ha) ▸ Store.ForwardReachable.anchor anchorStore)
  have reached := (forward k w receiver).reachable
  rcases e.target_eq_or_unseen_signer_of_pins slots pins caller nBound stateOk totalOk epochOk
      bounded afterAnchor targetEpoch members large receiver kBound justified receiverSlotOk
      checkpointEpoch with eq | ⟨v, _, honest, unseen, signed⟩
  · subst checkpoint
    exact coverage_comparable_of_target_read reached preGloas
      (oneBlock u caller w receiver n k nBound kBound) known checkpointKnown onChain targetRead
  obtain ⟨signer, data, duty, targetEq, before⟩ :=
    e.exists_maySign_of_signsTargetBefore honest signed
  have dutyCopy := duty
  obtain ⟨_, _, _, genesis, _, made, _⟩ := dutyCopy
  have senderGenesis := (e.clock_bounds v signer).1
  have receiverGenesis := (e.clock_bounds w k).1
  rw [anchored v honest] at senderGenesis
  rw [anchored w receiver] at receiverGenesis
  have common : ((e.world k).state w).genesisTimeMs = genesisTimeMs :=
    receiverGenesis.trans (senderGenesis.symm.trans genesis)
  have clock := mapError_ok_iff.mp receiverSlotOk
  change computeSlotAtTimeMs config ((e.world k).state w).genesisTimeMs
    ((e.world k).state w).timeMs = .ok receiverSlot at clock
  rw [common] at clock
  obtain ⟨endTime, endOk, endLe⟩ := exists_slot_start_of_current_slot clock
  have epochSlot : computeEpochAtSlot preset slot = epoch := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using epochOk
  have timeBounds := e.unseen_signer_time committees retained fits caller honest nBound
    (forward n u caller) headOk slotOk firstOk lastOk participantsOk unseen duty
    (targetEq ▸ checkpointEpoch.trans epochSlot.symm) before beginOk endOk
  have endBound : endTime.toNat ≤ (e.world k).time := by
    rw [← ready.1]
    exact UInt64.le_iff_toNat_le.mp endLe
  have signerBefore : (e.world signer).time < (e.world k).time := timeBounds.2.trans_le endBound
  have signerBound := signerBefore.le.trans kBound
  obtain ⟨supportHead, supportHeadOk, supports⟩ := e.head_supports_of_maySign honest duty
    (atSlot ▸ timeBounds.1) signerBefore safe
  obtain ⟨tip, tipBlock, headState, post, tipOk, tipKnown, stored, advanced, dataOk⟩ := made
  have eq := Except.ok.inj (tipOk.symm.trans supportHeadOk)
  subst tip
  have signedReach := (forward signer v honest).reachable
  by_cases anchorHead : tipBlock = anchorBlock
  · have supportRead := supports
    unfold Store.isAncestor at supportRead
    obtain ⟨rb, rbOk, _⟩ := bind_ok_iff.mp supportRead
    have rk := Store.block_ok_iff.mp rbOk
    have walk := Store.getAncestor_of_isAncestor_of_lt preGloas rk supports
    rw [Store.getAncestor_of_le tipKnown (anchorHead.symm ▸
      signedReach.anchorSlot_le_block rk)] at walk
    have rootEq := congrArg ForkChoiceNode.root (Except.ok.inj walk)
    obtain ⟨ar, hash, _, _, _, final, _⟩ := getForkchoiceStore_anchor anchorStore
    have tipHash := signedReach.root tipKnown
    rw [anchorHead, hash, Except.ok.injEq] at tipHash
    have rootAnchor : root = anchor.finalizedCheckpoint.root := by
      rw [final]
      exact rootEq.symm.trans tipHash.symm
    left
    simpa only [← rootAnchor] using
      e.isAncestor_anchor_of_known anchorStore anchored receiver checkpointKnown
  have later : getCurrentEpoch anchorState < data.target.epoch := by
    obtain ⟨_, _, _, _, anchorJustified, _⟩ := getForkchoiceStore_anchor anchorStore
    rw [targetEq, checkpointEpoch]
    simpa only [← anchorOk, anchorJustified] using afterAnchor
  have read := reset_honest_target_read signedReach positive (UInt64.le_of_eq anchorSlot)
    (nonzero v honest signer signerBound) tipKnown (Store.blockState_ok_iff.mp stored)
    anchorHead advanced dataOk later
  rw [(getAttestationData_eq_ok_iff.mp dataOk).2.2.2.1, targetEq] at read
  exact coverage_comparable_of_target_read reached preGloas
    (oneBlock v honest w receiver signer k signerBound kBound) known checkpointKnown supports read

omit [DecidablePred (· ∈ J)] in
/-- An honest justified vote supplies a representable time for its epoch boundary. -/
private theorem coverage_justified_boundary_time
    {limit : ℕ} {anchorEpoch horizon : Epoch}
    (voted : JustifiedByHonestVote e anchorEpoch horizon limit)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ}
    (bounded : (e.world k).time ≤ limit) {checkpoint : Checkpoint} {slot boundary : Slot}
    (justified : ((e.world k).state w).Justified checkpoint)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (later : anchorEpoch < checkpoint.epoch) (horizonOk : checkpoint.epoch ≤ horizon)
    (boundaryOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok boundary) :
    ∃ begin, computeTimeAtSlotMs config genesisTimeMs boundary = .ok begin := by
  obtain ⟨v, honest, signed⟩ := voted w receiver k bounded checkpoint slot justified slotOk
    later horizonOk
  obtain ⟨signer, data, duty, target, _⟩ := e.exists_maySign_of_signsTargetBefore honest signed
  obtain ⟨_, _, deadline, _, _, made, _⟩ := duty
  obtain ⟨_, _, _, _, _, _, _, _, dataOk⟩ := made
  have epoch := target_epoch_eq_of_getAttestationData dataOk
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  have before : boundary ≤ data.slot := by
    rw [UInt64.le_iff_toNat_le, firstNat, ← target, epoch]
    exact Nat.div_mul_le_self _ _
  obtain ⟨start, _, startOk, _⟩ := deadline
  obtain ⟨begin, beginOk, _⟩ := exists_timeAtSlotMs_of_le before startOk
  exact ⟨begin, beginOk⟩

/-- The start of a later slot is more than one delay after the start of an earlier slot. -/
private theorem coverage_delay_before_later_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot current : Slot} {begin currentBegin : UInt64} (later : slot < current)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (currentOk : computeTimeAtSlotMs config genesisTimeMs current = .ok currentBegin) :
    begin.toNat + Δ < currentBegin.toNat := by
  have lt := UInt64.lt_iff_toNat_lt.mp later
  have bound := current.toNat_lt
  have nextOk : addChecked slot 1 = .ok (slot + 1) :=
    addChecked_ok_iff.mpr ⟨by simp only [UInt64.toNat_one]; omega,
      by rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)⟩
  have nextNat : (slot + 1).toNat = slot.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨following, followingOk, _, followingLe⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_iff_toNat_le.mpr (by rw [nextNat]; omega)) currentOk
  obtain ⟨due, dueOk⟩ := fits.1
  have fit := fits.2 slot (slot + 1) begin due following nextOk beginOk dueOk followingOk
  have le := UInt64.le_iff_toNat_le.mp followingLe
  omega

/-- A viable leaf above a block of the justified subtree keeps the block in the filtered tree. -/
private theorem coverage_mem_of_viable_leaf {store : Store preset fork}
    (lower : store.ParentsBelow) (before : fork < .glamsterdam)
    {start root leaf : Root} {nodes : List ForkChoiceNode} {rootBlock : BeaconBlock preset fork}
    (rootKnown : store.blocks[root]? = some rootBlock)
    (below : store.isAncestor ⟨root, .pending⟩ ⟨start, .pending⟩ = .ok true)
    (above : store.isAncestor ⟨leaf, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (terminal : store.getNodeChildren ⟨leaf, .pending⟩ = .ok [])
    (viable : store.isViableLeaf config ⟨leaf, .pending⟩ = .ok true)
    (walk : store.filterNodeTree config ⟨start, .pending⟩ = .ok nodes) :
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes := by
  obtain ⟨startBlock, startKnown⟩ := Store.filterNodeTree_known walk
  have rootPath := (Store.isAncestor_iff (lower := lower) before startKnown rfl below).mp rfl
  have leafPath := (Store.isAncestor_iff (lower := lower) before rootKnown rfl above).mp rfl
  obtain ⟨result, resultOk, lift⟩ :=
    (Store.nodePath_of_ancestor (lower := lower) before startKnown rootPath).filterNodeTree walk
  exact lift _ ((Store.nodePath_of_ancestor (lower := lower) before rootKnown
    leafPath).self_mem_filterNodeTree resultOk terminal viable)

omit [DecidablePred (· ∈ J)] in
/-- A receiver justification of the call's epoch or later is above the root, or below it.

When it is below the root, the root comes after the boundary of the justification's epoch.

So for a root of an earlier epoch than the call, such a justification is above it. -/
private theorem coverage_current_justified {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {time : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    (oneBlock : OneBlockPerRoot e time)
    (unique : OneJustifiedPerEpoch e horizon time)
    (pins : HonestThirdPins e anchorEpoch horizon margin time)
    (voted : JustifiedByHonestVote e anchorEpoch horizon time)
    (committees : CommitteesFollow e time)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (nonzero : ∀ v ∈ J, ∀ i, (e.world i).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world i).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ v ∈ J, ∀ i epoch, (e.world i).time ≤ time →
      ((e.world i).state v).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (later : (e.world n).time ≤ time) (kBound : (e.world k).time ≤ time)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {head : ForkChoiceNode} {fcr : FastConfirmationStore} {start root : Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (rootAbove : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    (targetVotes : ∀ slot, ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false → HonestTargetVotes e margin u n head.root)
    {epoch rootEpoch startEpoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (rootEpochOk : ((e.world n).state u).getBlockEpoch root = .ok rootEpoch)
    (startEpochOk : ((e.world n).state u).getBlockEpoch start = .ok startEpoch)
    (fresh : rootEpoch = epoch →
      startEpoch < ((e.world k).state w).justifiedCheckpoint.epoch)
    {current boundary : Slot}
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (epochLe : epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch)
    (afterAnchor : anchorEpoch < ((e.world k).state w).justifiedCheckpoint.epoch)
    (cpHorizon : ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon)
    (boundaryOk : computeStartSlotAtEpoch preset
      ((e.world k).state w).justifiedCheckpoint.epoch = .ok boundary)
    {rootBlock jb : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (jk : ((e.world k).state w).blocks[((e.world k).state w).justifiedCheckpoint.root]? = some jb)
    (safe : ∀ t, (e.world n).time ≤ t → t < (e.world k).time → SafeAt e t root) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true ∧
        ∀ boundary, computeStartSlotAtEpoch preset
          ((e.world k).state w).justifiedCheckpoint.epoch = .ok boundary →
          boundary < rootBlock.slot := by
  let sender := (e.world n).state u
  let receiverStore := (e.world k).state w
  let cp := receiverStore.justifiedCheckpoint
  have forward := e.forwardReachable
    (fun a ha => (anchored a ha) ▸ Store.ForwardReachable.anchor anchorStore)
  have rr := (forward k w receiver).reachable
  have common := oneBlock u caller w receiver n k later kBound
  have rootRead := rootAbove
  unfold Store.isAncestor at rootRead
  obtain ⟨rb, rbOk, _⟩ := bind_ok_iff.mp rootRead
  have rk := Store.block_ok_iff.mp rbOk
  obtain ⟨readEpoch, slot, readRootEpoch, readStartEpoch, readEpochOk, slotOk, readRootEpochOk,
    readStartEpochOk, _, checks⟩ := checked
  cases Except.ok.inj (readEpochOk.symm.trans epochOk)
  cases Except.ok.inj (readRootEpochOk.symm.trans rootEpochOk)
  cases Except.ok.inj (readStartEpochOk.symm.trans startEpochOk)
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlot
  have eq := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst callSlot
  have slotEpoch : computeEpochAtSlot preset slot = epoch := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using epochOk
  have rbEq := common _ _ _ rk known
  subst rb
  have rootSlotLe : rootBlock.slot ≤ slot := by
    obtain ⟨s, sOk, held, _⟩ :=
      (forward n u caller).slots_le_current slots (UInt64.le_of_eq anchorSlot)
    have eq := Except.ok.inj (sOk.symm.trans slotOk)
    simpa only [eq] using held root rootBlock rk
  -- The receiver checkpoint's own boundary also handles calls exactly at that boundary.
  have coverAtBoundary (slotBefore : slot ≤ boundary) :
      receiverStore.isAncestor ⟨cp.root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
    obtain ⟨begin, beginOk⟩ := coverage_justified_boundary_time voted receiver kBound
      (.inl rfl) currentOk afterAnchor cpHorizon boundaryOk
    obtain ⟨callBegin', callBeginOk', _, le⟩ := exists_timeAtSlotMs_of_le slotBefore beginOk
    have eq := Except.ok.inj (callBeginOk.symm.trans callBeginOk')
    subst callBegin'
    exact coverage_covered_of_later_justified anchorStore anchorSlot anchored preGloas positive
      fits oneBlock voted anchorOk nonzero receiver kBound ready currentOk boundaryOk beginOk
      (.inl rfl) afterAnchor cpHorizon (UInt64.le_refl _)
      known jk (UInt64.le_trans rootSlotLe slotBefore) (fun t low high =>
        safe t (by rw [atCall]; exact (UInt64.le_iff_toNat_le.mp le).trans low)
          high)
  by_cases callBefore : slot ≤ boundary
  · exact .inl (coverAtBoundary callBefore)
  have sameEpoch : cp.epoch = epoch := by
    apply UInt64.le_antisymm _ epochLe
    rw [UInt64.le_iff_toNat_le, ← slotEpoch, computeEpochAtSlot, UInt64.toNat_div]
    apply (Nat.le_div_iff_mul_le positive).mpr
    have eq := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp callBefore)
    omega
  have offStart : isStartSlotAtEpoch preset slot = .ok false := by
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart
    rw [slotEpoch, ← sameEpoch, boundaryOk]
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    apply decide_eq_false
    intro zero
    have below := UInt64.le_of_lt (UInt64.not_le.mp callBefore)
    have eqNat := congrArg UInt64.toNat zero
    rw [UInt64.toNat_sub_of_le _ _ below] at eqNat
    exact callBefore (UInt64.le_iff_toNat_le.mpr (by simpa using Nat.le_of_sub_eq_zero eqNat))
  have numeric (state : BeaconState preset fork) (total support : Gwei)
      (stateOk : sender.getPulledUpHeadState config head.root = .ok state)
      (totalOk : getTotalActiveBalance state = .ok total)
      (supportOk : sender.computeHonestFfgSupportForCurrentTarget config head.root = .ok support)
      (enough : total.toNat < 3 * support.toNat) :=
    coverage_comparable_of_numeric_check anchorStore anchorSlot anchored preGloas positive slots
      fits oneBlock pins committees retained anchorOk nonzero caller receiver later kBound ready
      headOk rootAbove (targetVotes slot slotOk offStart) stateOk totalOk supportOk enough
      slotOk epochOk callBeginOk atCall currentOk (.inl rfl) sameEpoch
      (sameEpoch ▸ afterAnchor) (inHorizon u caller n _ later epochOk) known jk
      (fun t low high => safe t low high)
  have startNe (current : rootEpoch = epoch) : startEpoch ≠ epoch := by
    rw [← sameEpoch]
    exact UInt64.ne_of_lt (fresh current)
  by_cases rootCurrent : rootEpoch = epoch
  · have check : sender.willCurrentTargetBeJustified config head.root = .ok true := by
      rcases checks with old | current
      · exact (old.2.1 rootCurrent).elim
      · exact current.2.1 rootCurrent (startNe rootCurrent)
    simp only [Store.willCurrentTargetBeJustified, bind_ok_iff, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq] at check
    obtain ⟨state, stateOk, total, totalOk, support, supportOk, doubled, doubledOk,
      tripled, tripledOk, bound⟩ := check
    have two := (mulChecked_ok_iff.mp doubledOk).2
    have three := (mulChecked_ok_iff.mp tripledOk).2
    have le := UInt64.le_iff_toNat_le.mp (of_decide_eq_true bound)
    have enough : 2 * total.toNat ≤ 3 * support.toNat := by
      simpa only [two, three, UInt64.toNat_ofNat] using le
    have floor := UInt64.le_iff_toNat_le.mp
      (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
    exact numeric state total support stateOk totalOk supportOk (by omega)
  · have check : sender.willNoConflictingCheckpointBeJustified config head.root = .ok true := by
      rcases checks with old | current
      · exact (old.2.2.2 offStart).1
      · exact (current.2.2 rootCurrent).2 offStart
    rcases coverage_no_conflict_cases check with targetOk |
      ⟨s, total, support, hs, ht, hv, enough⟩
    · have read := targetOk
      simp only [sender, Store.getCurrentTarget, epochOk, Store.getCheckpointForBlock,
        bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
      obtain ⟨_, rfl, targetRoot, targetRead, targetEq⟩ := read
      have targetEpoch : sender.unrealizedJustifiedCheckpoint.epoch = epoch :=
        (congrArg Checkpoint.epoch targetEq).symm
      have same := unique w receiver u caller k n kBound later cp
        sender.unrealizedJustifiedCheckpoint (.inl rfl) (.inr (.inl rfl))
        (sameEpoch.trans targetEpoch.symm) cpHorizon
      have targetRead' : sender.getCheckpointBlock head.root cp.epoch = .ok cp.root := by
        rw [same, targetEpoch, ← congrArg Checkpoint.root targetEq]
        exact targetRead
      exact coverage_comparable_of_target_read rr preGloas common known jk rootAbove targetRead'
    · exact numeric s total support hs ht hv enough

omit [DecidablePred (· ∈ J)] in
/-- A checked root is comparable with receiver justification using only earlier root safety. -/
theorem Execution.justified_comparable_of_checked {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (slots : 0 < config.SLOT_DURATION_MS)
    {Δ : ℕ} (fits : DelayFits fork config genesisTimeMs Δ)
    {time : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    (oneBlock : OneBlockPerRoot e time)
    (unique : OneJustifiedPerEpoch e horizon time)
    (pins : HonestThirdPins e anchorEpoch horizon margin time)
    (voted : JustifiedByHonestVote e anchorEpoch horizon time)
    (committees : CommitteesFollow e time)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (nonzero : ∀ v ∈ J, ∀ i, (e.world i).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world i).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ v ∈ J, ∀ i epoch, (e.world i).time ≤ time →
      ((e.world i).state v).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (later : (e.world n).time ≤ time) (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {head receiverHead : ForkChoiceNode} {fcr : FastConfirmationStore} {start root : Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (onChain : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true)
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    (targetVotes : ∀ slot, ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false → HonestTargetVotes e margin u n head.root)
    (startSafe : ∀ t, (e.world n).time ≤ t → t ≤ time → SafeAt e t start)
    (safe : ∀ t, (e.world n).time ≤ t → t < time → SafeAt e t root)
    {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true := by
  let sender := (e.world n).state u
  let receiverStore := (e.world k).state w
  let cp := receiverStore.justifiedCheckpoint
  have kBound : (e.world k).time ≤ time := atTime.le
  have forward := e.forwardReachable
    (fun a ha => (anchored a ha) ▸ Store.ForwardReachable.anchor anchorStore)
  have sr := (forward n u caller).reachable
  have rr := (forward k w receiver).reachable
  have common := oneBlock u caller w receiver n k later kBound
  have pending : head = (⟨head.root, .pending⟩ : ForkChoiceNode) := by
    have p := Store.getHead_pending preGloas headOk
    cases head
    simp_all
  have rootAbove : sender.isAncestor head ⟨root, .pending⟩ = .ok true := by
    rw [pending]
    exact onChain
  have callerStart := startSafe _ le_rfl later u caller n head rfl upToDate headOk
  have receiverStart := startSafe _ later le_rfl w receiver k receiverHead atTime ready
    receiverHeadOk
  have receiverJ := Store.isAncestor_getHead receiverHeadOk
  have startRead := callerStart
  unfold Store.isAncestor at startRead
  obtain ⟨sb, sbOk, _⟩ := bind_ok_iff.mp startRead
  have sk := Store.block_ok_iff.mp sbOk
  have rootRead := rootAbove
  unfold Store.isAncestor at rootRead
  obtain ⟨rb, rbOk, _⟩ := bind_ok_iff.mp rootRead
  have rk := Store.block_ok_iff.mp rbOk
  have receiverStartRead := receiverStart
  unfold Store.isAncestor at receiverStartRead
  obtain ⟨rsb, rsbOk, _⟩ := bind_ok_iff.mp receiverStartRead
  have rsk := Store.block_ok_iff.mp rsbOk
  have seq := common _ _ _ sk rsk
  subst rsb
  have jRead := receiverJ
  unfold Store.isAncestor at jRead
  obtain ⟨jb, jbOk, _⟩ := bind_ok_iff.mp jRead
  have jk := Store.block_ok_iff.mp jbOk
  -- Compare the start with the root before comparing receiver justification with the start.
  rcases coverage_ancestors_comparable preGloas sk rk callerStart rootAbove with below | above
  · have copied := coverage_copy_ancestor rr preGloas common rsk known below
    have supported := Store.isAncestor_trans_of_lt preGloas rsk known receiverStart copied
    exact coverage_ancestors_comparable preGloas jk known receiverJ supported
  have startBelow := coverage_copy_ancestor rr preGloas common known rsk above
  rcases coverage_ancestors_comparable preGloas jk rsk receiverJ receiverStart with aboveJ | belowJ
  · by_cases reverse : receiverStore.isAncestor ⟨start, .pending⟩ ⟨cp.root, .pending⟩ = .ok true
    · exact .inr (Store.isAncestor_trans_of_lt preGloas rsk jk startBelow reverse)
    have checkedCopy := checked
    obtain ⟨epoch, slot, rootEpoch, startEpoch, epochOk, slotOk, rootEpochOk, startEpochOk,
      age, checks⟩ := checked
    obtain ⟨current, currentOk, _, blockBound⟩ :=
      (forward k w receiver).slots_le_current slots (UInt64.le_of_eq anchorSlot)
    have currentEpochOk : receiverStore.getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset current) := by
      simp [receiverStore, Store.getCurrentStoreEpoch, currentOk,
        bind, Except.bind, pure, Except.pure]
    have cpHorizon : cp.epoch ≤ horizon := UInt64.le_trans
      ((forward k w receiver).justified_epoch_le_current sound slots
        (UInt64.le_of_eq anchorSlot) currentEpochOk).1
      (inHorizon w receiver k _ kBound currentEpochOk)
    have anchorLower : anchorEpoch ≤ cp.epoch := by
      have lower := (e.epochsLe_of_le w (Nat.zero_le k)).1
      simpa [Execution.world_zero, World.initial, anchored w receiver, anchorOk] using lower
    have afterAnchor : anchorEpoch < cp.epoch := by
      by_contra old
      have eq : cp.epoch = anchor.justifiedCheckpoint.epoch :=
        (UInt64.le_antisymm (UInt64.not_lt.mp old) anchorLower).trans anchorOk.symm
      have anchorJust : ((e.world 0).state w).Justified anchor.justifiedCheckpoint := by
        change (e.start w).Justified anchor.justifiedCheckpoint
        rw [anchored w receiver]
        exact .inl rfl
      have same := unique w receiver w receiver k 0 kBound
        ((e.monotone_time (Nat.zero_le k)).trans kBound) cp anchor.justifiedCheckpoint
        (.inl rfl) anchorJust eq cpHorizon
      obtain ⟨_, _, _, _, aj, af, _⟩ := getForkchoiceStore_anchor anchorStore
      have anchorSame : anchor.justifiedCheckpoint = anchor.finalizedCheckpoint := aj.trans af.symm
      exact reverse (by simpa only [cp, same, anchorSame] using
        e.isAncestor_anchor_of_known anchorStore anchored receiver rsk)
    have anchorRecent : getCurrentEpoch anchorState < cp.epoch := by
      obtain ⟨_, _, _, _, aj, _⟩ := getForkchoiceStore_anchor anchorStore
      simpa only [← anchorOk, aj] using afterAnchor
    obtain ⟨carrier, cpRead⟩ := justified_read_of_anchor_aligned rr sound preGloas positive window
      anchorSlot (nonzero w receiver k kBound) (.inl rfl) anchorRecent
    obtain ⟨boundary, cpBlock, boundaryOk, cpKnown, cpBefore, _⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas cpRead
    change computeStartSlotAtEpoch preset cp.epoch = .ok boundary at boundaryOk
    have cpEq := Option.some.inj (jk.symm.trans cpKnown)
    subst cpBlock
    have startStrict : sb.slot < jb.slot := by
      by_contra notLt
      have walk := Store.getAncestor_of_isAncestor_of_lt preGloas rsk aboveJ
      rw [Store.getAncestor_of_le jk (UInt64.not_lt.mp notLt)] at walk
      have eq := Except.ok.inj walk
      exact reverse (eq ▸ Store.isAncestor_self jk)
    have startEpochEq : computeEpochAtSlot preset sb.slot = startEpoch := by
      simpa [Store.getBlockEpoch, sbOk, bind, Except.bind, pure, Except.pure] using startEpochOk
    -- Strict block ancestry below a checkpoint gives a strict epoch bound for the start.
    have epochStrict : startEpoch < cp.epoch := by
      have lt := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_lt_of_le startStrict cpBefore)
      have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      rw [← startEpochEq, UInt64.lt_iff_toNat_lt, computeEpochAtSlot, UInt64.toNat_div]
      exact (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
    have epochLe : epoch ≤ cp.epoch := UInt64.le_iff_toNat_le.mpr (by
      have := UInt64.lt_iff_toNat_lt.mp epochStrict
      omega)
    exact (coverage_current_justified anchorStore anchorSlot anchored preGloas positive slots
      incrementPositive fits
      oneBlock unique pins voted committees retained anchorOk nonzero inHorizon caller receiver
      later kBound ready headOk checkedCopy rootAbove atSlot targetVotes epochOk rootEpochOk
      startEpochOk (fun _ => epochStrict) currentOk epochLe afterAnchor cpHorizon boundaryOk
      known jk (fun t low high => safe t low (by simpa only [atTime] using high))).imp id
      And.left
  · exact .inr (Store.isAncestor_trans_of_lt preGloas rsk jk startBelow belowJ)

omit [DecidablePred (· ∈ J)] in
/-- A count with the quorum reserve added to the margin is a count with the margin alone. -/
private theorem coverage_targetVotes_of_reserve {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {u : ValidatorIndex} (caller : u ∈ J) {n margin : ℕ} {head : Root}
    (reserve : ∀ state target anc,
      ((e.world n).state u).getPulledUpHeadState config head = .ok state →
      ((e.world n).state u).getCurrentTarget config head = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u n head) :
    HonestTargetVotes e margin u n head := by
  intro state support target slot epochStart lastSlot participants stateOk supportOk targetOk
    slotOk startOk lastOk participantsOk
  have reachable := e.reachable
    (fun a ha => (anchored a ha) ▸ Store.Reachable.anchor anchorStore) n u caller
  obtain ⟨epoch, checkpoint, _, read, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  obtain ⟨_, block, _, held, _, _⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
  obtain ⟨anc, stored, _⟩ := reachable.blockStatesFromParents held
  obtain ⟨voters, members, bound⟩ := reserve state ⟨epoch, checkpoint⟩ anc stateOk targetOk
    stored state support ⟨epoch, checkpoint⟩ slot epochStart lastSlot participants stateOk
    supportOk targetOk slotOk startOk lastOk participantsOk
  exact ⟨voters, members, by omega⟩

omit [DecidablePred (· ∈ J)] in
/-- A later store reads a checkpoint of a head at each block above a block of that epoch.

The block is on the chain of the head and in the epoch of the checkpoint.

Another honest store holds a block above it, at a time up to the last one.

That store reads the same checkpoint root at that block for that epoch. -/
private theorem coverage_target_read {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {head : Root} {target : Checkpoint}
    (headRead : ((e.world n).state u).getCheckpointBlock head target.epoch = .ok target.root)
    {root : Root} {rootBlock : BeaconBlock preset fork}
    (rootHeld : ((e.world n).state u).blocks[root]? = some rootBlock)
    (onChain : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (rootEpoch : computeEpochAtSlot preset rootBlock.slot = target.epoch)
    {x : Root}
    (above : ((e.world k).state w).isAncestor ⟨x, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    ((e.world k).state w).getCheckpointBlock x target.epoch = .ok target.root := by
  have reachable (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.reachable (fun a ha => (anchored a ha) ▸ Store.Reachable.anchor anchorStore) i v honest
  obtain ⟨boundary, checkpointBlock, boundaryOk, checkpointHeld, checkpointLe, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas headRead
  have early : boundary ≤ rootBlock.slot := by
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    rw [UInt64.le_iff_toNat_le, boundaryNat, ← rootEpoch]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  have rootRead := Store.getCheckpointBlock_of_isAncestor_below (node := ⟨head, .pending⟩)
    (ancestor := ⟨root, .pending⟩) preGloas rootHeld onChain boundaryOk early headRead
  obtain ⟨receiverRoot, receiverRootHeld⟩ : ∃ b, ((e.world k).state w).blocks[root]? = some b := by
    have read := above
    unfold Store.isAncestor at read
    obtain ⟨b, found, _⟩ := bind_ok_iff.mp read
    exact ⟨b, Store.block_ok_iff.mp found⟩
  have same := oneBlock u caller w receiver n k nBound kBound root rootBlock receiverRoot
    rootHeld receiverRootHeld
  subst same
  have aboveAnchor : anchorBlock.slot ≤ boundary :=
    UInt64.le_trans ((reachable u caller n).anchorSlot_le_block checkpointHeld) checkpointLe
  have receiverRead := Store.getCheckpointBlock_of_same_blocks (reachable w receiver k)
    (oneBlock u caller w receiver n k nBound kBound) boundaryOk aboveAnchor
    ⟨rootBlock, receiverRootHeld⟩ rootRead
  exact Store.getCheckpointBlock_of_isAncestor (node := ⟨x, .pending⟩) preGloas receiverRootHeld
    above boundaryOk early receiverRead

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

For a block of the call's own epoch and a store two epochs later, that is `currentLate`.

`Execution.coveredOrViableAt_late_current` proves it from the same hypotheses.

The proof follows a theorem of [verified-fast-confirmation][vfc] and the lemmas under it.

It is `Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.coveredOrViableAt_of_checked {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
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
      isStartSlotAtEpoch preset slot = .ok false → ∀ state target anc,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u n head.root)
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
    (quorumDrifts : ∀ u ∈ J, ∀ n (head : Root) (pulled anc : BeaconState preset fork)
        (target : Checkpoint),
      (e.world n).time ≤ time →
      ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
      ((e.world n).state u).getCurrentTarget config head = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      ∀ w ∈ J, ∀ k (root : Root) (rootState state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).blockStates[root]? = some rootState →
      ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
      (state = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok state) →
      target.epoch ≤ getCurrentEpoch state →
      (getCurrentEpoch state).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch state ≤ horizon →
      ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
      (∀ v ∈ voters, v ∈ activeVoters pulled ∧ NotSlashed state v) →
      getTotalActiveBalance state = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
      2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
        2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
          quorumReserve config pulled anc)
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
      ∃ block, ((e.world k).state w).blocks[root]? = some block)
    (realized : ((e.world n).state u).RealizedRecent [root])
    (rootRecent : ∀ epoch block, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).blocks[root]? = some block →
      epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (realizedHead : ∀ epoch block, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).blocks[root]? = some block →
      computeEpochAtSlot preset block.slot < epoch →
      ∃ headState, ((e.world n).state u).blockStates[head.root]? = some headState ∧
        ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true ∧
        computeEpochAtSlot preset block.slot ≤ headState.currentJustifiedCheckpoint.epoch)
    (sourceLe : ∀ w ∈ J, ∀ k (tip : Root) (source : Checkpoint), (e.world k).time = time →
      getCurrentEpoch anchorState ≤ ((e.world k).state w).justifiedCheckpoint.epoch →
      ((e.world k).state w).getVotingSource config tip = .ok source →
      source.epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch)
    (genesis : ∀ w ∈ J, ∀ i, ((e.world i).state w).genesisTimeMs = genesisTimeMs)
    (currentLate : ∀ w ∈ J, ∀ k nodes (rootBlock : BeaconBlock preset fork) (slot current : Slot),
      (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
      ((e.world n).state u).blocks[root]? = some rootBlock →
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      computeEpochAtSlot preset rootBlock.slot = computeEpochAtSlot preset slot →
      ((e.world k).state w).getCurrentSlot config = .ok current →
      (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
        (computeEpochAtSlot preset current).toNat →
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true →
      ((e.world k).state w).isAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
        (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    CoveredOrViableAt e time root := by
  intro w receiver k nodes atTime ready tree
  obtain ⟨block, held⟩ := known w receiver k atTime ready
  obtain ⟨receiverHead, receiverHeadOk⟩ := e.exists_getHead anchorStore sound anchored anchorSlot
    anchorAtBoundary slots long window preGloas boost nonzero anchorParent inHorizon large supply
    receiver atTime.le
  rcases e.justified_comparable_of_checked anchorStore sound anchorSlot anchored preGloas
      positive window incrementPositive slots fits oneBlock unique pins voted committees
      (by omega) anchorOk nonzero inHorizon caller receiver later atTime upToDate ready
      headOk receiverHeadOk checked onChain atSlot
      (fun slot slotOk inside => coverage_targetVotes_of_reserve anchorStore anchored preGloas
        caller (targetVotes slot slotOk inside))
      startSafe safe held with
      covered | descends
  · exact .inl covered
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore)
  have reached := (forward k w receiver).reachable
  have lower := reached.parentsBelow (UInt64.le_of_eq anchorSlot)
    (anchorParent w receiver k atTime.le)
  obtain ⟨callerBlock, base, callerKnown, callerStored, recent⟩ := realized root (by simp)
  obtain ⟨current, currentOk, blocksBound, _⟩ :=
    (forward k w receiver).slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  by_cases early : (computeEpochAtSlot preset current).toNat ≤
      (computeEpochAtSlot preset callerBlock.slot).toNat + 1
  -- The justified subtree reads a leaf above the root even when that leaf is rejected.
  · obtain ⟨justifiedBlock, justifiedKnown⟩ := Store.filterNodeTree_known tree
    have path := (Store.isAncestor_iff (lower := lower) preGloas justifiedKnown rfl
      descends).mp rfl
    obtain ⟨leaf, leafBlock, leafKnown, above, terminal, ⟨verdict, read⟩, member⟩ :=
      Store.exists_leaf_above_of_filterNodeTree (lower := lower) preGloas held path tree
    have leafAbove : ((e.world k).state w).isAncestor ⟨leaf, .pending⟩ ⟨root, .pending⟩ =
        .ok true := by
      obtain ⟨result, resultOk⟩ := e.exists_isAncestor_of_held anchorStore anchored anchorSlot
        preGloas anchorParent receiver atTime.le leafKnown held
      have eq := (Store.isAncestor_iff (lower := lower) preGloas held rfl resultOk).mpr above
      exact eq ▸ resultOk
    have anchorHorizon : getCurrentEpoch anchorState ≤ horizon := by
      obtain ⟨r, _, anchorKnown⟩ := reached.anchor_known
      have bound := UInt64.le_iff_toNat_le.mp (blocksBound r anchorBlock anchorKnown)
      rw [anchorSlot] at bound
      exact UInt64.le_trans (UInt64.le_iff_toNat_le.mpr (Nat.div_le_div_right bound))
        (inHorizon w receiver k _ atTime.le epochOk)
    unfold Store.isViableLeaf at read
    rw [bind_ok_iff] at read
    obtain ⟨ep, epOk, read⟩ := read
    have eq := Except.ok.inj (epOk.symm.trans epochOk)
    subst ep
    rw [bind_ok_iff] at read
    obtain ⟨source, sourceOk, read⟩ := read
    obtain ⟨sourceRecent, finalized⟩ := e.early_source_recent_and_finalized anchorStore anchored
      sound slots positive window anchorSlot anchorAtBoundary preGloas chain oneBlock caller
      receiver later atTime.le epochOk (inHorizon w receiver k _ atTime.le epochOk)
      anchorHorizon (nonzero w receiver k atTime.le) callerKnown callerStored ⟨block, held⟩
      leafKnown recent early leafAbove sourceOk
    apply Or.inr
    apply member
    unfold Store.isViableLeaf
    simp only [epochOk, sourceOk, bind, Except.bind]
    by_cases shortcut : ((e.world k).state w).justifiedCheckpoint.epoch = GENESIS_EPOCH ∨
        source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch
    · simp [shortcut, finalized, pure, Except.pure]
    -- Only the numeric arm executes addition; its successful read rules out overflow.
    · cases addition : addChecked source.epoch 2 with
      | error err => simp [shortcut, addition, bind, Except.bind, Except.mapError] at read
      | ok bound =>
        have boundValue := (addChecked_ok_iff.mp addition).2
        change bound.toNat = source.epoch.toNat + 2 at boundValue
        have within : computeEpochAtSlot preset current ≤ bound :=
          UInt64.le_iff_toNat_le.mpr (by omega)
        simp [shortcut, within, finalized, Except.mapError, pure, Except.pure]
  -- Later receivers: the receiver is at least two epochs after the root.
  · have lateEpoch := Nat.lt_of_not_ge early
    have callerReached := (forward n u caller).reachable
    have common := oneBlock u caller w receiver n k later atTime.le
    have sameBlock := common _ _ _ callerKnown held
    subst sameBlock
    obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlot
    have callEpochOk : ((e.world n).state u).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset callSlot) := by
      simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
    have callRecent := rootRecent _ _ callEpochOk callerKnown
    by_cases previous : computeEpochAtSlot preset callerBlock.slot <
        computeEpochAtSlot preset callSlot
    swap
    -- A root of the call's own epoch is the late case of `currentLate`.
    · obtain ⟨readSlot, readSlotOk, blocksBelow, _⟩ :=
        (forward n u caller).slots_le_current slots (UInt64.le_of_eq anchorSlot)
      have slotEq := Except.ok.inj (readSlotOk.symm.trans callSlotOk)
      subst readSlot
      have below := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp (blocksBelow root callerBlock callerKnown))
      have notBefore := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp previous)
      have sameEpoch : computeEpochAtSlot preset callerBlock.slot =
          computeEpochAtSlot preset callSlot := by
        apply UInt64.toNat_inj.mp
        simp only [computeEpochAtSlot, UInt64.toNat_div] at below notBefore ⊢
        omega
      exact currentLate w receiver k nodes callerBlock callSlot current atTime ready tree
        callerKnown callSlotOk sameEpoch currentOk lateEpoch descends
    -- A root of the epoch before the call: the head realized its epoch.
    have previousNat := UInt64.lt_iff_toNat_lt.mp previous
    obtain ⟨headState, headStored, headAbove, headRealized⟩ :=
      realizedHead _ _ callEpochOk callerKnown previous
    have headRealizedNat := UInt64.le_iff_toNat_le.mp headRealized
    have positiveNat := positive
    have slotEpochNat (slot : Slot) :
        (computeEpochAtSlot preset slot).toNat = slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
    simp only [slotEpochNat] at lateEpoch callRecent previousNat headRealizedNat
    obtain ⟨_, _, _, _, anchorJustified, anchorFinalized, _⟩ := getForkchoiceStore_anchor anchorStore
    have anchorEpochEq : anchorEpoch = getCurrentEpoch anchorState := by
      rw [← anchorOk, anchorJustified]
    have anchorBelow : anchorEpoch.toNat ≤ callerBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      have le := UInt64.le_iff_toNat_le.mp (callerReached.anchorSlot_le_block callerKnown)
      rw [anchorEpochEq, getCurrentEpoch, slotEpochNat, ← anchorSlot]
      exact Nat.div_le_div_right le
    obtain ⟨jb, jk⟩ := Store.filterNodeTree_known tree
    have cpHorizon : ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon := UInt64.le_trans
      ((forward k w receiver).justified_epoch_le_current sound slots
        (UInt64.le_of_eq anchorSlot) epochOk).1
      (inHorizon w receiver k _ atTime.le epochOk)
    have cpCurrent := UInt64.le_iff_toNat_le.mp ((forward k w receiver).justified_epoch_le_current
      sound slots (UInt64.le_of_eq anchorSlot) epochOk).1
    simp only [slotEpochNat] at cpCurrent
    have anchorLower : anchorEpoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch := by
      have lower := (e.epochsLe_of_le w (Nat.zero_le k)).1
      simpa [Execution.world_zero, World.initial, anchored w receiver, anchorOk] using lower
    have anchorLowerNat := UInt64.le_iff_toNat_le.mp anchorLower
    by_cases atLeastCall : computeEpochAtSlot preset callSlot ≤ ((e.world k).state w).justifiedCheckpoint.epoch
    -- A justification of the call's epoch or later is above a root of the epoch before.
    · have atLeastNat := UInt64.le_iff_toNat_le.mp atLeastCall
      simp only [slotEpochNat] at atLeastNat
      have anchorRecent : getCurrentEpoch anchorState < ((e.world k).state w).justifiedCheckpoint.epoch := by
        rw [← anchorEpochEq]
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
      obtain ⟨carrier, cpRead⟩ := justified_read_of_anchor_aligned reached sound preGloas positive
        window anchorSlot (nonzero w receiver k atTime.le) (.inl rfl) anchorRecent
      obtain ⟨boundary, _, boundaryOk, _, _, _⟩ :=
        Store.isAncestor_of_getCheckpointBlock preGloas cpRead
      have checkedCopy := checked
      obtain ⟨_, _, _, startEpoch, _, _, _, startEpochOk, _, _⟩ := checkedCopy
      have pending : head = (⟨head.root, .pending⟩ : ForkChoiceNode) := by
        have p := Store.getHead_pending preGloas headOk
        cases head
        simp_all
      have rootAbove : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true := by
        rw [pending]
        exact onChain
      have rootEpochOk : ((e.world n).state u).getBlockEpoch root =
          .ok (computeEpochAtSlot preset callerBlock.slot) := by
        simp [Store.getBlockEpoch, Store.block_ok_iff.mpr callerKnown, bind, Except.bind, pure,
          Except.pure]
      rcases coverage_current_justified anchorStore anchorSlot anchored preGloas positive slots
          incrementPositive fits oneBlock unique pins voted committees (by omega) anchorOk nonzero
          inHorizon caller receiver later atTime.le ready headOk checked rootAbove
          ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩
          (fun slot slotOk inside => coverage_targetVotes_of_reserve anchorStore anchored preGloas
            caller (targetVotes slot slotOk inside))
          callEpochOk rootEpochOk startEpochOk
          (fun same => absurd same (UInt64.ne_of_lt previous)) currentOk atLeastCall
          (UInt64.lt_iff_toNat_lt.mpr (by omega)) cpHorizon boundaryOk held jk
          (fun t low high => safe t low (by simpa only [atTime] using high)) with
        covered | ⟨_, after⟩
      · exact .inl covered
      · exfalso
        have lt := UInt64.lt_iff_toNat_lt.mp (after boundary boundaryOk)
        have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
        have slotBelow := (Nat.div_lt_iff_lt_mul positive).mp previousNat
        have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat atLeastNat
        have back := Nat.div_mul_le_self callSlot.toNat preset.SLOTS_PER_EPOCH.toNat
        omega
    -- A justification of the root's epoch or before: a viable leaf lies above the head.
    have cpBelow : ((e.world k).state w).justifiedCheckpoint.epoch.toNat ≤ callerBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp atLeastCall)
      simp only [slotEpochNat] at this
      omega
    obtain ⟨headBlock, headKnown, rootBelowHead⟩ :=
      Store.slot_le_of_isAncestor callerKnown headAbove
    have headPending : head = (⟨head.root, .pending⟩ : ForkChoiceNode) := by
      have p := Store.getHead_pending preGloas headOk
      cases head
      simp_all
    have headAboveRoot : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
      rw [← headPending]
      exact headAbove
    -- The receiver's clock runs from the model's genesis time.
    have receiverGenesis : ((e.world k).state w).genesisTimeMs = genesisTimeMs :=
      genesis w receiver k
    have receiverClock : computeSlotAtTimeMs config genesisTimeMs ((e.world k).state w).timeMs =
        .ok current := by
      simpa only [Store.getCurrentSlot, receiverGenesis] using (mapError_ok_iff.mp currentOk)
    obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
      exists_slot_start_of_current_slot receiverClock
    have currentBeginBound : currentBegin.toNat ≤ (e.world k).time := by
      rw [← ready.1]
      exact UInt64.le_iff_toNat_le.mp currentBeginLe
    have callBefore : callSlot < current := by
      apply UInt64.lt_iff_toNat_lt.mpr
      by_contra notLt
      have := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) (Nat.le_of_not_lt notLt)
      omega
    have delay := coverage_delay_before_later_slot fits callBefore callBeginOk currentBeginOk
    -- The finalized checkpoint of the receiver is on the chain of the head.
    have finalLe := UInt64.le_iff_toNat_le.mp (reached.finalized_le_justified sound)
    have finalRead : ((e.world n).state u).getCheckpointBlock head.root
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root := by
      obtain ⟨_, _, ages⟩ := resetAge_forward anchorStore sound slots (forward k w receiver)
      rcases ages.1 with finalAnchor | ⟨finalLater, _⟩
      · rw [finalAnchor]
        exact walk_anchor_read anchorStore anchored anchorSlot anchorAtBoundary preGloas caller
          headKnown
      have finalLaterNat := UInt64.lt_iff_toNat_lt.mp finalLater
      simp only [anchorFinalized] at finalLaterNat
      have anchorNat : (getCurrentEpoch anchorState).toNat = anchorEpoch.toNat := by
        rw [anchorEpochEq]
      have cLater : anchorEpoch.toNat < headState.currentJustifiedCheckpoint.epoch.toNat := by
        omega
      have cGenesis : GENESIS_EPOCH < headState.currentJustifiedCheckpoint.epoch := by
        apply UInt64.lt_iff_toNat_lt.mpr
        simp only [GENESIS_EPOCH, UInt64.toNat_zero]
        omega
      have cJustified : ((e.world n).state u).Justified headState.currentJustifiedCheckpoint :=
        .inr (.inr ⟨cGenesis, .inl ⟨head.root, headState, headStored, rfl⟩⟩)
      have cHorizon : headState.currentJustifiedCheckpoint.epoch ≤ horizon := by
        obtain ⟨readSlot, readSlotOk, _, statesBound⟩ :=
          (forward n u caller).slots_le_current slots (UInt64.le_of_eq anchorSlot)
        have eq := Except.ok.inj (readSlotOk.symm.trans callSlotOk)
        subst readSlot
        have settled := UInt64.le_iff_toNat_le.mp (UInt64.le_trans
          ((callerReached.ordered sound).2 headStored).settled (getPreviousEpoch_le _))
        have slotLe := UInt64.le_iff_toNat_le.mp (statesBound head.root headState headStored)
        have horizonNat := UInt64.le_iff_toNat_le.mp (inHorizon u caller n _ later callEpochOk)
        simp only [slotEpochNat] at horizonNat
        simp only [getCurrentEpoch, slotEpochNat] at settled
        apply UInt64.le_iff_toNat_le.mpr
        have := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) slotLe
        omega
      have headNotAnchor : headBlock ≠ anchorBlock := by
        intro same
        obtain ⟨state, stored, isAnchor, _⟩ := callerReached.blockStatesFromParents headKnown
        have stateEq := isAnchor same
        rw [headStored, Option.some.injEq] at stored
        subst stored
        subst stateEq
        have settled := UInt64.le_iff_toNat_le.mp
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _))
        omega
      rcases (walk_checkpoint_ancestor callerReached sound preGloas positive window
          (UInt64.le_of_eq anchorSlot) (nonzero u caller n later)
          ⟨head.root, headBlock, headKnown, headNotAnchor⟩ headStored).2.1 with
        old | ⟨_, cBoundary, cBlock, _, cBoundaryOk, _, cRead⟩
      · have := UInt64.le_iff_toNat_le.mp old
        omega
      have priorRead := chain w receiver u caller k n atTime.le later headState.currentJustifiedCheckpoint cJustified
        (UInt64.le_iff_toNat_le.mpr (by omega)) cHorizon
      have splitRead := priorRead
      unfold Store.getCheckpointBlock at splitRead
      simp only [bind_ok_iff] at splitRead
      obtain ⟨prior, priorOk, _⟩ := splitRead
      exact walk_checkpoint_trans cBoundaryOk (mapError_ok_iff.mp priorOk)
        (UInt64.le_iff_toNat_le.mpr (by omega)) cRead priorRead preGloas
    -- The receiver holds the head, admitted more than one delay after the call.
    have finalizedKnown := e.finalized_known_of_prefix anchorStore sound anchored slots anchorSlot
      preGloas chain receiver atTime.le epochOk (inHorizon w receiver k _ atTime.le epochOk)
    obtain ⟨headHeld, agree⟩ := e.blocks_of_partiallySynchronous sync oneBlock admitted
      anchorStore anchored caller receiver (by rw [Nat.max_zero, atCall]; omega) atTime.le ready
      finalizedKnown (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) headKnown
      finalRead
    have headAboveRootReceiver := coverage_copy_ancestor reached preGloas common headHeld held
      headAboveRoot
    have headAboveJustified := Store.isAncestor_trans_of_lt preGloas held jk
      headAboveRootReceiver descends
    have path := (Store.isAncestor_iff (lower := lower) preGloas jk rfl headAboveJustified).mp rfl
    obtain ⟨leaf, leafBlock, leafKnown, leafAbove, terminal, ⟨verdict, read⟩, _⟩ :=
      Store.exists_leaf_above_of_filterNodeTree (lower := lower) preGloas headHeld path tree
    have leafAboveHead : ((e.world k).state w).isAncestor ⟨leaf, .pending⟩
        ⟨head.root, .pending⟩ = .ok true := by
      obtain ⟨result, resultOk⟩ := e.exists_isAncestor_of_held anchorStore anchored anchorSlot
        preGloas anchorParent receiver atTime.le leafKnown headHeld
      have eq := (Store.isAncestor_iff (lower := lower) (node := ⟨head.root, .pending⟩) preGloas
        headHeld rfl resultOk).mpr leafAbove
      exact eq ▸ resultOk
    have leafAboveRoot := Store.isAncestor_trans_of_lt (middle := ⟨head.root, .pending⟩) preGloas
      headHeld held leafAboveHead headAboveRootReceiver
    -- The leaf's voting source is the receiver's justified checkpoint.
    unfold Store.isViableLeaf at read
    rw [bind_ok_iff] at read
    obtain ⟨ep, epOk, read⟩ := read
    have eq := Except.ok.inj (epOk.symm.trans epochOk)
    subst ep
    rw [bind_ok_iff] at read
    obtain ⟨source, sourceOk, _⟩ := read
    obtain ⟨receiverHeadState, receiverHeadStored, _⟩ := reached.blockStatesFromParents headHeld
    have stateEq := e.blockStates_eq anchorStore caller receiver (anchored u caller)
      (anchored w receiver) common headStored receiverHeadStored
    subst stateEq
    have sourceLower := UInt64.le_iff_toNat_le.mp
      (walk_realized_le_source reached sound preGloas headHeld receiverHeadStored leafAboveHead
        sourceOk)
    have sourceUpper := UInt64.le_iff_toNat_le.mp (sourceLe w receiver k leaf source atTime
      (by rw [← anchorEpochEq]; exact anchorLower) sourceOk)
    have sourceSame : source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch :=
      UInt64.toNat_inj.mp (by omega)
    -- The leaf reads the finalized checkpoint of the receiver.
    have splitFinal := finalRead
    unfold Store.getCheckpointBlock at splitFinal
    simp only [bind_ok_iff] at splitFinal
    obtain ⟨finalBoundary, finalBoundaryOk, _⟩ := splitFinal
    have finalBoundaryOk := mapError_ok_iff.mp finalBoundaryOk
    have finalBoundaryNat := (computeStartSlotAtEpoch_ok_iff.mp finalBoundaryOk).2
    have finalBelow : finalBoundary ≤ headBlock.slot := by
      apply UInt64.le_iff_toNat_le.mpr
      have rootSlot := UInt64.le_iff_toNat_le.mp rootBelowHead
      have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
        (show ((e.world k).state w).finalizedCheckpoint.epoch.toNat ≤
          callerBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat by omega)
      have back := Nat.div_mul_le_self callerBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      omega
    have finalized := Store.getCheckpointBlock_of_isAncestor preGloas headHeld leafAboveHead
      finalBoundaryOk finalBelow (agree _ _ (UInt64.le_refl _) finalRead)
    have viable : ((e.world k).state w).isViableLeaf config ⟨leaf, .pending⟩ = .ok true := by
      unfold Store.isViableLeaf
      simp [epochOk, sourceOk, sourceSame, finalized, bind, Except.bind, pure, Except.pure]
    exact .inr (coverage_mem_of_viable_leaf lower preGloas held descends leafAboveRoot terminal
      viable tree)

end Models.Network

end EthLib.Consensus
