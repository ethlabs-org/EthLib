module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationResets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCommittees
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes

/-!
# Statements: the honest support of a confirmed block, from a historical anchor

This file states the initial transport of step 5 for the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proof of the transport is a placeholder, and its statement is proposed for review.

The caller counts an old vote of an honest validator, for a block or for its parent.

The validator may have cast a newer vote before the call.

The caller may still count the old vote, while another honest store counts the new one.

A historical anchor rules this out.

It is a block on the chain of the parent of the confirmed block.

It is of the current epoch or the one before.

It is safe at each time of the current epoch before the call.

So a counted vote has a target of the epoch before or later.

A newer vote of the same validator then has a target of the current epoch.

Its head descends from the historical anchor, so it agrees with the finality of the caller.

So the caller admits that newer vote before the call, and the old vote is not its latest one.

The induction of step 8 takes the anchor from an earlier call, or takes the block of the anchor.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Two votes that an honest validator signs for targets of one epoch are the same vote.

Two different votes for one target epoch are slashable, and an honest validator signs neither.

So when two honest stores hold votes of one validator for one target epoch, they hold one vote. -/
theorem Execution.data_eq_of_signed_of_target_epoch (slots : 0 < config.SLOT_DURATION_MS)
    {n k : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world k).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) (epoch : data.target.epoch = other.target.epoch) : data = other := by
  have nonslashable := e.isSlashableAttestationData_of_signed slots
    (e.monotone_sent (Nat.le_max_left n k) sentFirst)
    (e.monotone_sent (Nat.le_max_right n k) sentSecond) signedFirst signedSecond honest
  by_contra different
  simp [isSlashableAttestationData, different, epoch] at nonslashable

private theorem mem_insert_fold {v : ValidatorIndex}
    {items : List ValidatorIndex} {initial : Std.TreeSet ValidatorIndex} :
    v ∈ items.foldl (·.insert ·) initial ↔ v ∈ initial ∨ v ∈ items := by
  induction items generalizing initial with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons, ih, Std.TreeSet.mem_insert, List.mem_cons,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    constructor
    · rintro ((rfl | inside) | later)
      · exact .inr (.inl rfl)
      · exact .inl inside
      · exact .inr (.inr later)
    · rintro (inside | rfl | later)
      · exact .inl (.inr inside)
      · exact .inl (.inl rfl)
      · exact .inr later

/-- A slot committee contains only indices active in the head state's duty epoch. -/
private theorem active_of_mem_slotCommittee {store : Store preset fork}
    {head : Root} {slot : Slot} {members : Std.TreeSet ValidatorIndex}
    {headState : BeaconState preset fork} {v : ValidatorIndex}
    (preGloas : fork < .glamsterdam)
    (stateOk : store.blockState head = .ok headState)
    (read : store.getSlotCommittee head slot = .ok members) (member : v ∈ members) :
    isActiveAt headState (computeEpochAtSlot preset slot) v.toNat = true := by
  unfold Store.getSlotCommittee at read
  rw [stateOk] at read
  dsimp only [bind, Except.bind] at read
  -- Every insertion is justified by the committee read at that iteration.
  have kept := foldlM_ok_invariant
    (fun found : Std.TreeSet ValidatorIndex => ∀ x ∈ found,
      isActiveAt headState (computeEpochAtSlot preset slot) x.toNat = true)
    (fun found index after before step => ?_) (by
      intro x hx
      exact False.elim (Std.TreeSet.not_mem_emptyc hx)) read
  · exact kept v member
  · change (do
      let committee ← (getBeaconCommittee headState slot index.toUInt64).mapError
        ForkChoiceError.accessor
      pure (committee.foldl (·.insert ·) found)) = Except.ok after at step
    simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨committee, committeeOk, rfl⟩ := step
    intro x inside
    rw [← Array.foldl_toList, mem_insert_fold] at inside
    rcases inside with old | added
    · exact before x old
    · exact isActiveAt_eq_true_iff.mpr
        ((mem_getActiveValidatorIndices
          (BeaconState.registryWithinLimit_of_lt preGloas headState)).mp
          (mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
            (Array.mem_toList_iff.mp added)))

/-- A window member has an active duty epoch in the state used to read the window. -/
private theorem active_of_mem_committeeWindow {store : Store preset fork}
    {head : Root} {first last : Slot} {members : Std.TreeSet ValidatorIndex}
    {headState : BeaconState preset fork} {v : ValidatorIndex}
    (preGloas : fork < .glamsterdam)
    (stateOk : store.blockState head = .ok headState)
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (member : v ∈ members) :
    ∃ slot, first ≤ slot ∧ slot ≤ last ∧
      isActiveAt headState (computeEpochAtSlot preset slot) v.toNat = true := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨afterLast, afterOk, read⟩ := read
  have inside := (mem_foldlM_committees_iff read).mp member
  rcases inside with empty | ⟨offset, offsetIn, committee, committeeOk, inside⟩
  · exact False.elim (Std.TreeSet.not_mem_emptyc empty)
  · have offsetLt := List.mem_range.mp offsetIn
    have afterNat := (addChecked_ok_iff.mp afterOk).2
    have lastBound := last.toNat_lt
    have offsetBound : offset < 2 ^ 64 := by simp only [UInt64.toNat_one] at afterNat; omega
    have offsetNat : offset.toUInt64.toNat = offset := by
      simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' offsetBound]
    have slotNat : (first + offset.toUInt64).toNat = first.toNat + offset := by
      rw [UInt64.toNat_add, offsetNat, Nat.mod_eq_of_lt]
      simp only [UInt64.toNat_one] at afterNat
      omega
    refine ⟨first + offset.toUInt64, ?_, ?_,
      active_of_mem_slotCommittee preGloas stateOk committeeOk inside⟩
    · rw [UInt64.le_iff_toNat_le, slotNat]
      omega
    · rw [UInt64.le_iff_toNat_le, slotNat]
      simp only [UInt64.toNat_one] at afterNat
      omega

/-- A successful total also bounds a subset, without requiring a bound on inactive balances. -/
private theorem totalBalance_exists_of_subset {state : BeaconState preset fork}
    {indices all : List ValidatorIndex} {total : Gwei}
    (read : getTotalBalance state all = .ok total)
    (subset : ∀ v ∈ indices, v ∈ all) :
    ∃ result, getTotalBalance state indices = .ok result := by
  obtain ⟨inside, bounded, -⟩ := getTotalBalance_ok_iff_stake.mp read
  have small : stake (fun v => balanceAt state v.toNat) indices.toFinset < 2 ^ 64 :=
    lt_of_le_of_lt (stake_mono fun v member =>
      List.mem_toFinset.mpr (subset v (List.mem_toFinset.mp member))) bounded
  -- The floor is itself a UInt64, so taking the maximum cannot introduce overflow.
  let value := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat) indices.toFinset)
  have fits : value < 2 ^ 64 := max_lt preset.EFFECTIVE_BALANCE_INCREMENT.toNat_lt small
  refine ⟨value.toUInt64, getTotalBalance_ok_iff_stake.mpr
    ⟨fun v member => inside v (subset v member), small, ?_⟩⟩
  exact UInt64.toNat_ofNat_of_lt' fits

/-- Registry containment and an active total suffice for the non-full window's balance read. -/
private theorem filteredTotal_exists {state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (read : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ active result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok active ∧ getTotalBalance state active = .ok result := by
  obtain ⟨active, filtered⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  -- The filter passes only indices in the total's active set, even if they are slashed.
  obtain ⟨result, resultOk⟩ := totalBalance_exists_of_subset
    (indices := active) (getTotalActiveBalance_ok read) (fun v member => by
      have passed := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
      obtain ⟨validator, found, isActive⟩ := passed
      exact mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, isActive⟩))
  exact ⟨active, result, filtered, resultOk⟩

/-- The rule maximum succeeds once its range arithmetic, registry reads and total succeed. -/
private theorem maximum_exists_of_total {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei} {covered : Bool}
    (coverage : isFullValidatorSetCovered preset first last = .ok covered)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ maximum, store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum := by
  by_cases empty : last < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  cases covered
  · obtain ⟨active, result, filtered, resultOk⟩ := filteredTotal_exists totalOk inside
    simp only [bind, Except.bind, pure, Except.pure] at filtered
    exact ⟨result, by
      simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
        empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true, windowOk,
        filtered, resultOk, Except.mapError, pure, Except.pure]⟩
  · exact ⟨total, by
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
      rw [totalOk]; rfl⟩

/-- A nonempty caller read supplies the start arithmetic for another range with the same start. -/
private theorem coverage_exists_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last otherLast afterOther : Slot} {maximum : Gwei}
    (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (afterOk : addChecked otherLast 1 = .ok afterOther) :
    ∃ covered, isFullValidatorSetCovered preset first otherLast = .ok covered := by
  have notEmpty : ¬last < first := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at read
  obtain ⟨result, read, -⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, notEmpty, ↓reduceIte,
    bind_ok_iff] at read
  obtain ⟨covered, coverage, -⟩ := read
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at coverage
  obtain ⟨afterFirst, firstOk, lastFirst, lastFirstOk, _, _, -⟩ := coverage
  refine ⟨decide (computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterOther), ?_⟩
  simp only [isFullValidatorSetCovered, firstOk, lastFirstOk, afterOk, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- A slot step within one epoch does not change the registry. -/
private theorem validators_advanceSlot_sameEpoch {state after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (run : advanceSlot config checks state = .ok after)
    (same : getCurrentEpoch after = getCurrentEpoch state) :
    after.validators = state.validators := by
  obtain ⟨next, cached, epoched, nextNat, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok run
  have inside : next % preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro boundary
    have rem : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat boundary
    have equal : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simpa only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] using
        congrArg UInt64.toNat same
    have beforeRem := Nat.mod_lt state.slot.toNat positive
    have before := Nat.mod_add_div state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have after := Nat.mod_add_div next.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [rem, equal] at after
    omega
  simp only [epochIfLast, inside, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
  subst epoched
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  rfl

/-- No epoch transition occurs between equal endpoint epochs of a slot-only run. -/
private theorem validators_advanceSlots_sameEpoch (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {count : Nat} {state after : BeaconState preset fork}
    (run : advanceSlots config checks count state = .ok after)
    (same : getCurrentEpoch after = getCurrentEpoch state) :
    after.validators = state.validators := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at run
    subst after
    rfl
  | succ count ih =>
    obtain ⟨middle, first, rest⟩ := bind_ok_iff.mp run
    have low := (runKept_advanceSlot first).later
    have high : getCurrentEpoch middle ≤ getCurrentEpoch after := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right (by rw [advanceSlots_slot count rest]; omega)
    have middleEq : getCurrentEpoch middle = getCurrentEpoch state :=
      UInt64.le_antisymm (same ▸ high) low
    exact (ih rest (same.trans middleEq.symm)).trans
      (validators_advanceSlot_sameEpoch positive first middleEq)

/-- A same-epoch lookahead preserves both the active total read and every slashing flag. -/
private theorem lookahead_sameEpoch_frame {state after : BeaconState preset fork} {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (run : lookaheadState config checks state slot = .ok after)
    (same : getCurrentEpoch after = getCurrentEpoch state) :
    getTotalActiveBalance after = getTotalActiveBalance state ∧
      ∀ v, NotSlashed after v ↔ NotSlashed state v := by
  have validators : after.validators = state.validators := by
    unfold lookaheadState at run
    split at run
    · have slotsOk := mapError_ok_iff.mp run
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
      obtain ⟨_, _, advanced⟩ := slotsOk
      exact validators_advanceSlots_sameEpoch positive advanced same
    · cases run
      rfl
  constructor
  · simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getTotalBalance,
      validators, same]
  · intro v
    simp only [NotSlashed, validators]

/-- After the first two epochs, a successful justification step has checked the active total. -/
private theorem activeTotal_of_justification {state after : BeaconState preset fork}
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (run : processJustificationAndFinalization state = .ok after) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  unfold processJustificationAndFinalization at run
  split at run
  · simp only [processJustificationAndFinalizationAltair, late, ↓reduceIte,
      bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := run
    exact ⟨total, totalOk⟩
  · simp only [bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := run
    exact ⟨total, totalOk⟩

variable [DecidablePred (· ∈ J)]

/-- Step 5, the initial transport: the bound of step 4 holds in each honest store at a later time.

The caller is an honest validator whose store is up to date and holds the bound of step 4.

Its ranges of committees end at the slot before its own, and at the slot before the block.

The call is at the start of its slot.

So every honest vote of an earlier slot of the current epoch falls in the window below.

The block is on the chain of the head of the caller.

The historical block is on the chain of the parent of the block.

It is of the current epoch of the caller or of the epoch before.

It is safe at each time from the start of the current epoch to just before the call.

The receiver is an honest validator whose store is up to date at the later time.

Its head descends from the parent of the block.

Its current epoch is at most two epochs after the epoch of the parent.

Its finalized checkpoints up to that time agree with the block, as `rootFinal` says.

No honest validator is slashed in a state that an honest store counts, as `unslashed` says.

The tally state of the receiver is a lookahead of a held state, and need not be a counting state.

The window of the receiver is the committees of its head between the parent and its own slot.

The conclusion bounds the active members of that window, as `HeadFollowsSupport` reads it.

The preset bounds are sufficient for this argument; they are not claimed to be necessary.

The proof follows three lemmas of [verified-fast-confirmation][vfc].

Two are `honest_supporters_sum_le_Sval_window` and `weak_base_discharged_window`.

The third is `bval_endpoint_strip_window_uniform`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honest_support_of_historical_anchor {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
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
    {begin : UInt64} (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
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
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    (rootOnHead : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (below : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (recent : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historicalSafe : ∀ earlier, epochStartTime.toNat ≤ earlier → earlier < (e.world n).time →
      SafeAt e earlier historical)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (receiverUpToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (rootFinal : ∀ k' ≤ k,
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ block.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current last : Slot} {receiverEpoch : Epoch} {score : Gwei}
    {receiverWindow receiverParticipants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverAbove : ((e.world k).state w).isAncestor receiverHead ⟨block.parentRoot, .pending⟩ =
      .ok true)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (age : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok last)
    (receiverWindowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root
      firstSlot last = .ok receiverWindow)
    (scoreOk : computeProposerScore config state = .ok score)
    (receiverParticipantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root
      firstSlot beforeBlock = .ok receiverParticipants) :
    stake (fun v => balanceAt state v.toNat) (Store.activeMembers state receiverWindow) +
        score.toNat <
      stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block
            parentBlock | v ∈ J} +
        2 * stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
  sorry


end EthLib.Consensus.Models.Network
