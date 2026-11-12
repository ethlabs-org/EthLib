module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.FinalizedSources
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedRegistry
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Statements: the blocks that the fast confirmation rule falls back to are safe

This file states step 7 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

A call of the rule starts from one of three blocks.

They are the block stored before, the finalized block and the observed justified block.

The block stored before needs no statement here.

The induction of step 8 keeps it safe from one call to the next.

The finalized block of an honest store is safe one delay after the store holds it.

By then each honest store holds a justified checkpoint of that epoch or a later one.

The finalized block is on the chain of that checkpoint, and the head is above it.

So the finalized block is not safe at the call itself.

The rule confirms a later block only after a recent start.

A finalized checkpoint after that of the anchor is two epochs old, so its block is not recent.

Then the start is the block of the anchor, which is safe at each time.

The observed justified block is safe from the call that falls back to it.

The call is at the start of an epoch.

The checkpoint was the unrealized justification of the caller one delay before.

By the call, each honest store holds a justified checkpoint of that epoch or a later one.

At the same epoch the two checkpoints are the same.

A later one has the vote of an honest validator, of a time after the call.

That validator had the observed block on the chain of its head, by induction on the time.

Its target is then above the observed block, since that block is of the epoch before.

The statements take the facts of Casper FFG as hypotheses, with a horizon.

They also take three facts on the blocks of honest stores, which `BlocksArrive` holds.

Six lemmas of [verified-fast-confirmation][vfc] give these results.

The first is `finalized_epoch_le_voter_justified_of_receiver_slot_le`.

The second is `finalizedReset_safeFrom_of_nextSlotSynchrony`.

The third is `finalizedResetCandidateInput_safeFrom_anchor_of_recent`.

The fourth is `deadline_justified_epoch_le_of_carrier`.

The fifth is `ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`.

The sixth is `trustedAnchor_safeFrom_of_acceptedGlobalTrajectory`.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- Without an anchor at or before its epoch start, no new block can be admitted. -/
private theorem frozen_or_anchor_aligned {store anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    (∃ start, computeStartSlotAtEpoch preset (getCurrentEpoch anchorState) = .ok start ∧
      anchorBlock.slot ≤ start) ∨
    (store.blocks = anchor.blocks ∧
      store.finalizedCheckpoint = anchor.finalizedCheckpoint ∧
      store.unrealizedFinalizedCheckpoint = anchor.finalizedCheckpoint) := by
  obtain ⟨anchorRoot, hashed, _, _, _, final, _, unrealized⟩ :=
    getForkchoiceStore_anchor anchored
  obtain ⟨r, hash, blocks, _⟩ := getForkchoiceStore_maps anchored
  rw [hashed, Except.ok.injEq] at hash
  subst r
  induction reachable with
  | anchor made =>
    have eq := Except.ok.inj (made.symm.trans anchored)
    subst eq
    exact .inr ⟨rfl, rfl, unrealized.trans final.symm⟩
  | tick _ ticked ih =>
    rcases ih with aligned | ⟨same, f, u⟩
    · exact .inl aligned
    obtain ⟨f, u⟩ := Store.finalized_properties_of_onTick
      (fun c => c = anchor.finalizedCheckpoint) f u ticked
    exact .inr ⟨(Store.onTick_frame ticked).2.2.1.trans same, f, u⟩
  | @block before after checks sources signed reached added ih =>
    rcases ih with aligned | ⟨same, f, u⟩
    · exact .inl aligned
    rcases Store.onBlock_same_or_insert added with eq | ⟨root, rootOk, fresh, _⟩
    · exact .inr (eq ▸ ⟨same, f, u⟩)
    obtain ⟨_, _, checkpoint⟩ := Store.onBlock_checks rootOk
      (by simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]) added
    rw [f, final] at checkpoint
    unfold Store.getCheckpointBlock at checkpoint
    simp only [bind_ok_iff] at checkpoint
    obtain ⟨start, startOk, node, walk, _⟩ := checkpoint
    obtain ⟨block, known, lower⟩ := Store.getAncestor_le walk
    rw [same, blocks, getElem?_insert_root] at known
    split at known
    · cases Option.some.inj known
      exact .inl ⟨start, mapError_ok_iff.mp startOk, lower⟩
    · simp at known
  | attestation _ attested ih =>
    rcases ih with aligned | ⟨same, f, u⟩
    · exact .inl aligned
    have maps := (Store.onAttestation_frame attested).2.1
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
    have fields : stored.finalizedCheckpoint = anchor.finalizedCheckpoint ∧
        stored.unrealizedFinalizedCheckpoint = anchor.finalizedCheckpoint := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · cases Except.ok.inj storing
        exact ⟨f, u⟩
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
        obtain ⟨_, _, rfl⟩ := storing
        exact ⟨f, u⟩
    split at attested
    · cases Except.ok.inj attested
      exact .inr ⟨maps.trans same, fields⟩
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
  | attesterSlashing _ slashed ih =>
    rcases ih with aligned | ⟨same, f, u⟩
    · exact .inl aligned
    have maps := (Store.onAttesterSlashing_frame slashed).2.1
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact .inr ⟨maps.trans same, f, u⟩
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
    exact ih

/-- The block of the anchor is safe at each time.

Each honest store starts as the store of the anchor.

Each block of such a store is the block of the anchor or is above it. -/
theorem Execution.safeAt_anchor {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (time : ℕ) :
    SafeAt e time anchor.finalizedCheckpoint.root := by
  intro w honest k head _ _ headOk
  have reached := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨known, walks⟩ := anchor_walk_of_reachable anchored reached
  have descends := Store.isAncestor_getHead headOk
  have justifiedKnown : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).justifiedCheckpoint.root]? = some b := by
    unfold Store.isAncestor at descends
    rw [bind_ok_iff] at descends
    obtain ⟨b, found, -⟩ := descends
    exact ⟨b, Store.block_ok_iff.mp found⟩
  obtain ⟨b, found⟩ := justifiedKnown
  obtain ⟨block, headFound, -⟩ := Store.slot_le_of_isAncestor found descends
  exact ancestor_pending_of_walk known
    (walks head block headFound (fun before => Store.getHead_pending before headOk)).2

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
private def ResetAge (anchor : Checkpoint) (store : Store preset fork) (epoch : Epoch) : Prop :=
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

private theorem resetAge_forward {anchor store : Store preset fork}
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

/-- The finalized checkpoint of an honest store is that of the anchor, or is two epochs old.

No checkpoint of the state of the anchor is of a later epoch than that state.

A state finalizes a checkpoint of the epoch before its own at the latest.

The store takes that checkpoint from a block of an epoch before its own. -/
theorem Execution.finalizedCheckpoint_eq_or_add_two_le {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (honest : u ∈ J) (start : e.start u = anchor) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint ∨
      ((e.world n).state u).finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat := by
  have _ := honest
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

/-- Step 7, the recent start: the rule confirms a block after the finalized one of the anchor only.

The rule has passed its checks from the finalized block of an honest store to a later block.

The checks ask for a start of the current epoch or the one before.

A finalized checkpoint after that of the anchor is two epochs old, and its block is older.

So the finalized checkpoint of the store is that of the anchor. -/
theorem Execution.finalizedCheckpoint_eq_of_checked {anchor : Store preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (honest : u ∈ J) (start : e.start u = anchor) {n : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state u).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {fcr : FastConfirmationStore} {head root : Root}
    (checked : ((e.world n).state u).Checked config fcr head
      ((e.world n).state u).finalizedCheckpoint.root root) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint := by
  have _ := honest
  obtain ⟨epoch, slot, rootEpoch, startEpoch, epochOk, slotOk, rootOk, startOk, recent,
    rest⟩ := checked
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) := by
    clear epochOk slotOk startOk recent rootOk rest nonzero
    induction n with
    | zero =>
      change Store.ForwardReachable config anchorState anchorBlock (e.start u)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n u with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.forwardReachable ih
  have reached := forward.reachable
  obtain ⟨current, clock, age⟩ := resetAge_forward anchored sound
    (Store.slotDuration_pos slotOk) forward
  rw [slotOk, Except.ok.injEq] at clock
  subst current
  have epochEq : epoch = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using
      epochOk.symm
  subst epoch
  rcases age.1 with same | ⟨later, old⟩
  · exact same
  exfalso
  obtain ⟨anchorRoot, hash, _, _, _, final, _⟩ := getForkchoiceStore_anchor anchored
  have later' : getCurrentEpoch anchorState < ((e.world n).state u).finalizedCheckpoint.epoch := by
    simpa only [final] using later
  have origin := reached.finalized_origins _ (.inl rfl)
  have child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock := by
    by_contra absent
    have allAnchor {r : Root} {s : BeaconState preset fork}
        (held : ((e.world n).state u).blockStates[r]? = some s) : s = anchorState := by
      obtain ⟨b, known⟩ := reached.known_of_blockState held
      have same : b = anchorBlock := by
        by_contra other
        exact absent ⟨r, b, known, other⟩
      obtain ⟨post, found, anchoredState, _⟩ := reached.blockStatesFromParents known
      rw [held, Option.some.injEq] at found
      subst post
      exact anchoredState same
    have upper : ((e.world n).state u).finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState := by
      rcases origin with ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
      · exact eq ▸ UInt64.le_refl _
      · rw [eq, allAnchor held]
        exact UInt64.le_trans (Store.finalized_le_currentJustified sound.ordered)
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _))
      · rw [allAnchor held] at pulled
        have inv := processJustificationAndFinalization_invariant sound.ordered sound.settled pulled
        rw [eq]
        exact UInt64.le_trans (Store.finalized_le_currentJustified inv.1) inv.2.2.1
    exact UInt64.not_le.mpr later' upper
  have aligned : anchorBlock.slot ≤ anchorState.slot := by
    rcases frozen_or_anchor_aligned anchored reached with ⟨first, firstOk, le⟩ | ⟨_, eq, _⟩
    · have firstEq := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
      rw [getCurrentEpoch_toNat] at firstEq
      have lower := Nat.div_mul_le_self anchorState.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      exact UInt64.le_trans le (UInt64.le_iff_toNat_le.mpr (by omega))
    · rw [eq] at later
      exact (UInt64.lt_irrefl _ later).elim
  have rootBound : ∃ first b,
      computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch = .ok first ∧
      ((e.world n).state u).blocks[((e.world n).state u).finalizedCheckpoint.root]? = some b ∧
      b.slot ≤ first := by
    rcases origin with ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
    · rw [eq] at later'
      exact (UInt64.lt_irrefl _ later').elim
    · have bound := (reached.blockState_checkpoint_roots sound positive window aligned
        nonzero child held).2.2
      rw [← eq] at bound
      exact bound.resolve_left (UInt64.not_le.mpr later')
    · have bound := reached.pulled_finalized_root sound positive window aligned nonzero
        child held pulled
      rw [← eq] at bound
      exact bound.resolve_left (UInt64.not_le.mpr later')
  obtain ⟨first, b, firstOk, known, lower⟩ := rootBound
  unfold Store.getBlockEpoch at startOk
  simp only [bind_ok_iff] at startOk
  obtain ⟨b', found, eq⟩ := startOk
  rw [Store.block_ok_iff.mpr known, Except.ok.injEq] at found
  subst b'
  cases Except.ok.inj eq
  have bound : (computeEpochAtSlot preset b.slot).toNat ≤
      ((e.world n).state u).finalizedCheckpoint.epoch.toNat := by
    have le := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp lower)
    have atStart := computeEpochAtSlot_computeStartSlotAtEpoch
      (UInt64.lt_iff_toNat_lt.mpr positive) firstOk
    simpa only [← atStart, computeEpochAtSlot, UInt64.toNat_div] using le
  omega

/-- A receiver holding a carrier includes that carrier state's finalized epoch. -/
theorem Execution.finalized_epoch_le_justified_of_carrier
    {last : ℕ} (oneBlock : OneBlockPerRoot e last) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
    (origin : ((e.world n).state u).blockStates[root]? = some state)
    (held : ((e.world k).state w).blocks[root]? = some block) :
    state.finalizedCheckpoint.epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch := by
  have reached := e.reachable
    (fun v hv => (start v hv).symm ▸ Store.Reachable.anchor anchored) k w receiver
  obtain ⟨post, stored, _, _⟩ := reached.blockStatesFromParents held
  have same := e.blockStates_eq anchored sender receiver (start u sender) (start w receiver)
    (oneBlock u sender w receiver n k nBound kBound) origin stored
  subst post
  exact UInt64.le_trans (reached.blockState_finalized_le sound stored)
    (reached.finalized_le_justified sound)

/-- Importing a block includes its state's justified epoch in the store's maximum. -/
private theorem reset_state_justified_le {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    state.currentJustifiedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch := by
  have all : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      s.currentJustifiedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch := by
    clear stored state root
    induction reachable with
    | anchor made =>
      obtain ⟨anchorRoot, _, _, states⟩ := getForkchoiceStore_maps made
      obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor made
      intro r s found
      rw [states, getElem?_insert_root] at found
      split at found
      · cases Option.some.inj found
        rw [justified]
        exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
      · simp at found
    | @block before after checks sources signed _ added ih =>
      have forward := Store.onBlock_epochsLe added
      unfold Store.onBlock at added
      simp only [bind_ok_iff] at added
      obtain ⟨_, _, added⟩ := added
      split at added
      · cases added
        exact ih
      · unfold Store.addBlock at added
        simp only [bind_ok_iff] at added
        obtain ⟨state, _, head, _, voted, vote, recorded, record, boosted, boost, added⟩ := added
        obtain ⟨_, _, bs0⟩ := (Store.recordBlockPtcVotes_onlyPtcVotes vote).frame
        obtain ⟨_, _, bs1, _⟩ := Store.recordBlockTimeliness_frame record
        obtain ⟨_, _, bs2, _⟩ := Store.updateProposerBoostRoot_frame boost
        obtain ⟨later, _, bs3, _⟩ := Store.computePulledUpTip_frame added
        intro r s found
        rw [bs3, Store.updateCheckpoints_blockStates, bs2, bs1, bs0,
          Std.TreeMap.getElem?_insert] at found
        split at found
        · cases found
          apply UInt64.le_trans (b := (boosted.updateCheckpoints
            state.currentJustifiedCheckpoint state.finalizedCheckpoint).justifiedCheckpoint.epoch)
            ?_ later.1
          unfold Store.updateCheckpoints
          split <;> dsimp only <;> split
          all_goals first | exact UInt64.le_refl _ | exact UInt64.not_lt.mp ‹_›
        · exact UInt64.le_trans (ih _ _ found) forward.1
    | tick _ handled ih =>
      obtain ⟨_, le, _, states⟩ := Store.onTick_frame handled
      exact fun r s found => UInt64.le_trans (ih r s (states ▸ found)) le.1
    | attestation _ handled ih =>
      obtain ⟨le, _, states⟩ := Store.onAttestation_frame handled
      exact fun r s found => UInt64.le_trans (ih r s (states ▸ found)) le.1
    | attesterSlashing _ handled ih =>
      obtain ⟨le, _, states⟩ := Store.onAttesterSlashing_frame handled
      exact fun r s found => UInt64.le_trans (ih r s (states ▸ found)) le.1
    | payloadAttestation _ handled ih =>
      obtain ⟨le, _, states⟩ := (Store.onPayloadAttestationMessage_onlyPtcVotes handled).frame
      exact fun r s found => UInt64.le_trans (ih r s (states ▸ found)) le.1
    | envelope _ handled ih =>
      obtain ⟨le, _, states⟩ := Store.onExecutionPayloadEnvelope_frame handled
      exact fun r s found => UInt64.le_trans (ih r s (states ▸ found)) le.1
    | inclusionList _ handled ih =>
      obtain ⟨le, _, states⟩ := Store.onInclusionList_frame handled
      exact fun r s found => UInt64.le_trans (ih r s (states ▸ found)) le.1
  exact all root state stored

/-- Finality after the anchor requires a held block other than the anchor. -/
private theorem reset_child_of_finalized_gt {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (later : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch) :
    ∃ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block ∧ block ≠ anchorBlock := by
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
  have upper : store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState := by
    rcases reached.finalized_origins _ (.inl rfl) with
      ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
    · exact eq ▸ UInt64.le_refl _
    · rw [eq, allAnchor held]
      exact UInt64.le_trans (Store.finalized_le_currentJustified sound.ordered)
        (UInt64.le_trans sound.settled (getPreviousEpoch_le _))
    · rw [allAnchor held] at pulled
      have inv := processJustificationAndFinalization_invariant sound.ordered sound.settled pulled
      rw [eq]
      exact UInt64.le_trans (Store.finalized_le_currentJustified inv.1) inv.2.2.1
  exact UInt64.not_le.mpr later upper

/-- Realized finality names a held block, including the anchor case. -/
private theorem reset_finalized_known {anchor store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork), store.blocks[r]? = some b →
      b.stateRoot ≠ Vector.replicate 32 0)
    (forward : Store.ForwardReachable config anchorState anchorBlock store) :
    ∃ block, store.blocks[store.finalizedCheckpoint.root]? = some block := by
  obtain ⟨_, _, age⟩ := resetAge_forward anchored sound slots forward
  obtain ⟨r, hashed, _, _, _, final, _⟩ := getForkchoiceStore_anchor anchored
  have reached := forward.reachable
  rcases age.1 with same | ⟨later, _⟩
  · obtain ⟨r', hashed', found⟩ := reached.anchor_known
    rw [hashed, Except.ok.injEq] at hashed'
    subst r'
    simpa only [same, final] using Exists.intro anchorBlock found
  have later' : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch := by
    simpa only [final] using later
  have child := reset_child_of_finalized_gt reached sound later'
  have roots : ∃ start block,
      computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok start ∧
        store.blocks[store.finalizedCheckpoint.root]? = some block ∧ block.slot ≤ start := by
    rcases reached.finalized_origins _ (.inl rfl) with
      ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
    · rw [eq] at later'
      exact (UInt64.lt_irrefl _ later').elim
    · have bound := (reached.blockState_checkpoint_roots sound positive window aligned
        nonzero child held).2.2
      rw [← eq] at bound
      exact bound.resolve_left (UInt64.not_le.mpr later')
    · have bound := reached.pulled_finalized_root sound positive window aligned nonzero
        child held pulled
      rw [← eq] at bound
      exact bound.resolve_left (UInt64.not_le.mpr later')
  obtain ⟨_, block, _, held, _⟩ := roots
  exact ⟨block, held⟩

/-- A carrier's checkpoint read composes with an earlier finalized-prefix read. -/
private theorem reset_finalized_read {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last) (before : fork < .glamsterdam)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {root : Root} {checkpoint : Checkpoint}
    (justified : ((e.world n).state u).Justified checkpoint)
    (inHorizon : checkpoint.epoch ≤ horizon)
    (ordered : ((e.world k).state w).finalizedCheckpoint.epoch ≤ checkpoint.epoch)
    (read : ((e.world n).state u).getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) :
    ((e.world n).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
  have priorRead := chain w receiver u sender k n kBound nBound checkpoint justified ordered
    inHorizon
  have splitRead := read
  have splitPrefix := priorRead
  unfold Store.getCheckpointBlock at splitRead splitPrefix
  simp only [bind_ok_iff] at splitRead splitPrefix
  obtain ⟨boundary, boundaryOk, node, walked, result⟩ := splitRead
  obtain ⟨prior, priorOk, _⟩ := splitPrefix
  have below : prior ≤ boundary := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [(computeStartSlotAtEpoch_ok_iff.mp (mapError_ok_iff.mp priorOk)).2,
      (computeStartSlotAtEpoch_ok_iff.mp (mapError_ok_iff.mp boundaryOk)).2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp ordered)
  have pending := Store.getAncestor_pending_of_lt before rfl walked
  have rootEq : node.root = checkpoint.root := Except.ok.inj result
  have nodeEq : node = ⟨checkpoint.root, .pending⟩ := by
    cases node
    simp_all
  subst node
  have through := Store.getAncestor_trans below walked
  unfold Store.getCheckpointBlock at priorRead ⊢
  simp only [priorOk, bind, Except.bind, through]
  simpa only [priorOk, bind, Except.bind] using priorRead

/-- A delay later, each honest store has justified the epoch that an honest store finalized.

The first store is that of an honest validator at an event, in an epoch at most the horizon.

The receiver is an honest validator whose store is up to date one delay later or more.

The first store took its finalized checkpoint from a block that it holds.

The receiver holds that block, when its own finalized checkpoint is on the chain of the block.

Otherwise its finalized checkpoint is of a later epoch, and so is its justified one.

The proof uses the finalized chain to place the finalized checkpoint of the receiver. -/
theorem Execution.finalized_epoch_le_justified_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam)
    {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    (admitted : BlocksAdmitted e 0 Δ last) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon last)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (bounded : (e.world k).time ≤ last)
    (nonzero : ∀ v ∈ J, ∀ k', (e.world k').time ≤ (e.world k).time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k').state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) :
    ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) := e.forwardReachable
    (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored) i v honest
  have reached := (forward u first n).reachable
  have received := (forward w receiver k).reachable
  have anchorLe : getCurrentEpoch anchorState ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    have lower := (e.epochsLe_of_le w (Nat.zero_le k)).1
    obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor anchored
    simpa only [Execution.world_zero, World.initial, start w receiver, justified] using lower
  by_cases old : ((e.world n).state u).finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · exact UInt64.le_trans old anchorLe
  by_cases covered : ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (received.finalized_le_justified sound)
  have ordered := UInt64.le_of_lt (UInt64.not_le.mp covered)
  have later := UInt64.not_le.mp old
  have child := reset_child_of_finalized_gt reached sound later
  have aligned : anchorBlock.slot ≤ anchorState.slot := by
    rcases frozen_or_anchor_aligned anchored reached with ⟨boundary, boundaryOk, le⟩ |
      ⟨_, same, _⟩
    · have eq := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      rw [getCurrentEpoch_toNat] at eq
      have bound := Nat.div_mul_le_self anchorState.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      exact UInt64.le_trans le (UInt64.le_iff_toNat_le.mpr (by omega))
    · obtain ⟨_, _, _, _, _, final, _⟩ := getForkchoiceStore_anchor anchored
      rw [same, final] at old
      exact (old (UInt64.le_refl _)).elim
  obtain ⟨current, currentOk, _⟩ := bind_ok_iff.mp epochOk
  have slots := Store.slotDuration_pos currentOk
  have nBound : (e.world n).time ≤ last := by omega
  have carrier : ∀ (root : Root) (state : BeaconState preset fork),
      ((e.world n).state u).blockStates[root]? = some state →
      ((e.world n).state u).finalizedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch →
      ∃ block, ((e.world k).state w).blocks[root]? = some block := by
    intro root state stored bound
    have recent : getCurrentEpoch anchorState < state.currentJustifiedCheckpoint.epoch :=
      UInt64.lt_of_lt_of_le later bound
    have justified : ((e.world n).state u).Justified state.currentJustifiedCheckpoint :=
      .inr (.inr ⟨UInt64.lt_iff_toNat_lt.mpr (by
        have lt := UInt64.lt_iff_toNat_lt.mp recent
        simp only [GENESIS_EPOCH, UInt64.toNat_zero]
        omega), .inl ⟨root, state, stored, rfl⟩⟩)
    have upper := UInt64.le_trans (reset_state_justified_le reached sound stored)
      (forward u first n |>.justified_epoch_le_current sound slots aligned epochOk).1
    rcases (walk_checkpoint_ancestor reached sound preGloas positive window aligned
      (nonzero u first n (by omega)) child stored).2.1 with early |
      ⟨_, _, block, known, _, _, read⟩
    · exact (UInt64.not_le.mpr recent early).elim
    have finalRead := reset_finalized_read chain preGloas first receiver nBound bounded justified
      (UInt64.le_trans upper inHorizon) (UInt64.le_trans ordered bound) read
    exact ⟨block, (e.blocks_of_partiallySynchronous sync oneBlock admitted anchored start first
      receiver (by simpa using late) bounded upToDate
      (reset_finalized_known anchored sound slots positive window aligned
        (nonzero w receiver k le_rfl) (forward w receiver k))
      (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) known finalRead).1⟩
  rcases reached.finalized_origins _ (.inl rfl) with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
  · rw [same] at later
    exact (UInt64.lt_irrefl _ later).elim
  · have bound : ((e.world n).state u).finalizedCheckpoint.epoch ≤
        state.currentJustifiedCheckpoint.epoch :=
      same ▸ Store.finalized_le_currentJustified ((reached.ordered sound).2 stored).ordered
    obtain ⟨block, held⟩ := carrier root state stored bound
    rw [same]
    exact e.finalized_epoch_le_justified_of_carrier oneBlock anchored sound start first receiver
      nBound bounded stored held
  · have inv := (reached.ordered sound).2 stored
    have bound : pulled.finalizedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch := by
      rcases processJustificationAndFinalization_ok run with same | ⟨_, _, _, weighed⟩
      · rw [same]
        exact Store.finalized_le_currentJustified inv.ordered
      · rcases (weighJustificationAndFinalization_checkpoints weighed).2.2.1 with eq | eq | eq
        · exact eq ▸ Store.finalized_le_currentJustified inv.ordered
        · exact eq ▸ inv.ordered.2
        · exact eq ▸ UInt64.le_refl _
    obtain ⟨block, held⟩ := carrier root state stored (same ▸ bound)
    obtain ⟨post, postOk, _, _⟩ := received.blockStatesFromParents held
    have eq := e.blockStates_eq anchored first receiver (start u first) (start w receiver)
      (oneBlock u first w receiver n k nBound bounded) stored postOk
    subst post
    rw [same]
    exact UInt64.le_trans bound (reset_state_justified_le received sound postOk)

/-- A finalized checkpoint is safe when every current justification covers its epoch. -/
theorem Execution.safeAt_finalized_of_epoch_bounds
    (preGloas : fork < .glamsterdam) {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last)
    {u : ValidatorIndex} (caller : u ∈ J) {n time : ℕ} (nBound : (e.world n).time ≤ last)
    (bounded : time ≤ last)
    (bounds : ∀ w ∈ J, ∀ k, (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world n).state u).finalizedCheckpoint.epoch ≤
        ((e.world k).state w).justifiedCheckpoint.epoch ∧
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon) :
    SafeAt e time ((e.world n).state u).finalizedCheckpoint.root := by
  intro w honest k head atTime current headOk
  obtain ⟨lower, upper⟩ := bounds w honest k atTime current
  have read := chain u caller w honest n k nBound (atTime ▸ bounded) _ (Or.inl rfl) lower upper
  obtain ⟨boundary, finalized, _, finalizedKnown, _, below⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas read
  have headAbove := Store.isAncestor_getHead headOk
  have justifiedKnown : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).justifiedCheckpoint.root]? = some b := by
    unfold Store.isAncestor at headAbove
    rw [bind_ok_iff] at headAbove
    obtain ⟨b, found, _⟩ := headAbove
    exact ⟨b, Store.block_ok_iff.mp found⟩
  obtain ⟨justified, justifiedKnown⟩ := justifiedKnown
  exact Store.isAncestor_trans_of_lt preGloas justifiedKnown finalizedKnown headAbove below

/-- Step 7, the finalized block: it is safe from one delay after an honest store holds it.

The store is that of an honest validator at an event.

Each honest store up to the last time is in an epoch at most the horizon.

A delay later, each honest store has justified the finalized epoch or a later one.

The finalized block is on the chain of that justified block, by the finalized chain.

The head of a store is above its justified block. -/
theorem Execution.safeAt_finalized {Δ : ℕ} (sync : e.Synchronous Δ)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    (admitted : BlocksAdmitted e 0 Δ limit) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch}
    (chain : FinalizedPrefix e horizon limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (nonzero : ∀ v ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time + Δ ≤ time → time ≤ limit →
      SafeAt e time ((e.world n).state u).finalizedCheckpoint.root := by
  intro time late bounded
  by_cases same : ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint
  · rw [same]
    exact e.safeAt_anchor anchored start time
  have reached := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) n u caller
  have aligned : anchorBlock.slot ≤ anchorState.slot := by
    rcases frozen_or_anchor_aligned anchored reached with ⟨first, firstOk, le⟩ | ⟨_, eq, _⟩
    · have firstEq := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
      rw [getCurrentEpoch_toNat] at firstEq
      have lower := Nat.div_mul_le_self anchorState.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      exact UInt64.le_trans le (UInt64.le_iff_toNat_le.mpr (by omega))
    · exact (same eq).elim
  have nBound : (e.world n).time ≤ limit := by omega
  apply e.safeAt_finalized_of_epoch_bounds preGloas chain caller nBound bounded
  intro w honest k atTime current
  have kBound : (e.world k).time ≤ limit := by omega
  have lower := e.finalized_epoch_le_justified_epoch sync positive window preGloas
    oneBlock admitted anchored sound start chain caller honest epochOk
    (inHorizon u caller n _ nBound epochOk) (by omega) kBound
    (fun v hv k' earlier => nonzero v hv k' (earlier.trans kBound)) current
  have forward := e.forwardReachable
    (fun v hv => (start v hv).symm ▸ Store.ForwardReachable.anchor anchored) k w honest
  have duration : 0 < config.SLOT_DURATION_MS := by
    obtain ⟨slot, read, _⟩ := bind_ok_iff.mp epochOk
    exact Store.slotDuration_pos read
  obtain ⟨slot, slotOk, _⟩ := forward.slots_le_current duration aligned
  have currentEpoch : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  exact ⟨lower, UInt64.le_trans
    (forward.justified_epoch_le_current sound (Store.slotDuration_pos slotOk) aligned
      currentEpoch).1 (inHorizon w honest k _ kBound currentEpoch)⟩

/-- A one-slot tick realizes the pending checkpoint when it crosses an epoch boundary. -/
private theorem reset_tick_slot {s t : Store preset fork} {time : UInt64} {old new : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (oldOk : s.getCurrentSlot config = .ok old) (newOk : t.getCurrentSlot config = .ok new)
    (step : new.toNat ≤ old.toNat + 1) (tick : s.onTickPerSlot config time = .ok t) :
    t.unrealizedJustifiedCheckpoint = s.unrealizedJustifiedCheckpoint ∧
      (computeEpochAtSlot preset old < computeEpochAtSlot preset new →
        s.unrealizedJustifiedCheckpoint.epoch ≤ t.justifiedCheckpoint.epoch) := by
  have clock : ({s with timeMs := time} : Store preset fork).getCurrentSlot config = .ok new := by
    simpa only [Store.getCurrentSlot, (Store.onTickPerSlot_frame tick).1,
      (Store.onTickPerSlot_frame tick).2.1] using newOk
  have boundary (cross : computeEpochAtSlot preset old < computeEpochAtSlot preset new) :
      old < new ∧ computeSlotsSinceEpochStart preset new = .ok 0 := by
    have lt := UInt64.lt_iff_toNat_lt.mp cross
    simp only [computeEpochAtSlot, UInt64.toNat_div] at lt
    have low := (Nat.div_lt_iff_lt_mul positive).mp lt
    have high := Nat.div_mul_le_self new.toNat preset.SLOTS_PER_EPOCH.toNat
    have rounded := (computeStartSlotAtEpoch_ok_iff.mp
      (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) new)).2
    have same : new / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH = new := by
      apply UInt64.toNat_inj.mp
      rw [rounded, computeEpochAtSlot, UInt64.toNat_div]
      omega
    refine ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), ?_⟩
    simp [computeSlotsSinceEpochStart, computeStartSlotAtEpoch_computeEpochAtSlot, same,
      bind, Except.bind, pure, Except.pure]
  unfold Store.onTickPerSlot at tick
  simp only [bind_ok_iff, oldOk, clock, Except.ok.injEq] at tick
  obtain ⟨_, rfl, _, rfl, offset, offsetOk, tick⟩ := tick
  split at tick <;> split at tick
  all_goals
    first
    | cases Except.ok.inj tick
      constructor
      · simp only [Store.updateCheckpoints]
        split <;> dsimp only <;> split <;> rfl
      · intro _
        simp only [Store.updateCheckpoints]
        split <;> dsimp only <;> split
        all_goals first | exact UInt64.le_refl _ | exact UInt64.not_lt.mp ‹_›
    | cases Except.ok.inj tick
      refine ⟨rfl, fun cross => ?_⟩
      obtain ⟨lt, zero⟩ := boundary cross
      rw [zero] at offsetOk
      have eq : offset = 0 := by simpa [Except.mapError] using offsetOk.symm
      exact (‹¬ (old < new ∧ offset = 0)› ⟨lt, eq⟩).elim

/-- Catch-up realizes the original pending checkpoint if its target is in a later epoch. -/
private theorem reset_catchUp_realizes {s t : Store preset fork} {old target : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (oldOk : s.getCurrentSlot config = .ok old) (le : old ≤ target)
    (caught : Store.catchUp config s target = .ok t) :
    t.getCurrentSlot config = .ok target ∧
      t.unrealizedJustifiedCheckpoint = s.unrealizedJustifiedCheckpoint ∧
      (computeEpochAtSlot preset old < computeEpochAtSlot preset target →
        s.unrealizedJustifiedCheckpoint.epoch ≤ t.justifiedCheckpoint.epoch) := by
  induction s using Store.catchUp.induct config target generalizing old with
  | case1 s ih =>
    rw [Store.catchUp.eq_1] at caught
    rw [bind_ok_iff] at caught
    obtain ⟨current, currentOk, caught⟩ := caught
    rw [oldOk, Except.ok.injEq] at currentOk
    subst current
    split at caught
    · rename_i lt
      simp only [bind_ok_iff] at caught
      obtain ⟨next, nextOk, time, timeOk, ticked, tick, caught⟩ := caught
      split at caught
      · have nextOk := mapError_ok_iff.mp nextOk
        have timeOk := mapError_ok_iff.mp timeOk
        have tickSlot : ticked.getCurrentSlot config = .ok next := by
          unfold Store.getCurrentSlot
          rw [(Store.onTickPerSlot_frame tick).1, (Store.onTickPerSlot_frame tick).2.1,
            computeSlotAtTimeMs_computeTimeAtSlotMs (Store.slotDuration_pos oldOk) timeOk]
          rfl
        have sum := (addChecked_ok_iff.mp nextOk).2
        have high : next ≤ target := UInt64.le_iff_toNat_le.mpr (by
          have lt := UInt64.lt_iff_toNat_lt.mp lt
          simp only [UInt64.toNat_one] at sum
          omega)
        obtain ⟨clock, pending, realized⟩ := ih ticked ‹_› tickSlot high caught
        obtain ⟨same, step⟩ := reset_tick_slot positive oldOk tickSlot
          (by simpa only [UInt64.toNat_one] using Nat.le_of_eq sum) tick
        refine ⟨clock, pending.trans same, ?_⟩
        intro cross
        by_cases first : computeEpochAtSlot preset old < computeEpochAtSlot preset next
        · exact UInt64.le_trans (step first) (Store.catchUp_frame caught).2.1.1
        · rw [← same]
          apply realized
          exact UInt64.lt_of_le_of_lt (UInt64.not_lt.mp first) cross
      · cases caught
    · have same : old = target := UInt64.le_antisymm le (UInt64.not_lt.mp ‹_›)
      cases Except.ok.inj caught
      subst target
      exact ⟨oldOk, rfl, fun cross => (UInt64.lt_irrefl _ cross).elim⟩

/-- A full tick realizes earlier pending justification at each crossed epoch. -/
private theorem reset_tick_realizes {s t : Store preset fork} {time : UInt64} {old : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (oldOk : s.getCurrentSlot config = .ok old) (forward : s.timeMs ≤ time)
    (tick : s.onTick config time = .ok t) :
    ∃ current, t.getCurrentSlot config = .ok current ∧
      t.unrealizedJustifiedCheckpoint = s.unrealizedJustifiedCheckpoint ∧
      (computeEpochAtSlot preset old < computeEpochAtSlot preset current →
        s.unrealizedJustifiedCheckpoint.epoch ≤ t.justifiedCheckpoint.epoch) := by
  have finalSlot := Store.getCurrentSlot_onTick tick
  unfold Store.onTick at tick
  simp only [bind_ok_iff] at tick
  obtain ⟨target, targetOk, caught, caughtOk, tick⟩ := tick
  have low : old ≤ target := computeSlotAtTimeMs_mono forward
    (mapError_ok_iff.mp oldOk) (mapError_ok_iff.mp targetOk)
  have targetFinal := finalSlot.trans targetOk
  obtain ⟨caughtSlot, pending, realized⟩ := reset_catchUp_realizes positive oldOk low caughtOk
  obtain ⟨same, _⟩ := reset_tick_slot positive caughtSlot targetFinal (by omega) tick
  exact ⟨target, targetFinal, same.trans pending, fun cross =>
    UInt64.le_trans (realized cross) (Store.onTickPerSlot_frame tick).2.2.1.1⟩

/-- A held state's pulled-up justification is pending, and realized after its epoch. -/
private def ResetAdoption (store : Store preset fork) (epoch : Epoch) : Prop :=
  ∀ (root : Root) (state pulled : BeaconState preset fork),
    store.blockStates[root]? = some state →
    processJustificationAndFinalization state = .ok pulled →
    pulled.currentJustifiedCheckpoint.epoch ≤ store.unrealizedJustifiedCheckpoint.epoch ∧
      (getCurrentEpoch state < epoch →
        pulled.currentJustifiedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch)

private theorem reset_update_bounds (s : Store preset fork) (j f : Checkpoint) :
    j.epoch ≤ (s.updateCheckpoints j f).justifiedCheckpoint.epoch ∧
      (s.updateCheckpoints j f).unrealizedJustifiedCheckpoint =
        s.unrealizedJustifiedCheckpoint := by
  unfold Store.updateCheckpoints
  split <;> dsimp only <;> split
  all_goals exact ⟨by first | exact UInt64.le_refl _ | exact UInt64.not_lt.mp ‹_›, rfl⟩

private theorem reset_unrealized_bounds (s : Store preset fork) (j f : Checkpoint) :
    s.unrealizedJustifiedCheckpoint.epoch ≤
        (s.updateUnrealizedCheckpoints j f).unrealizedJustifiedCheckpoint.epoch ∧
      j.epoch ≤ (s.updateUnrealizedCheckpoints j f).unrealizedJustifiedCheckpoint.epoch := by
  unfold Store.updateUnrealizedCheckpoints
  split <;> dsimp only <;> split
  all_goals constructor <;> first
    | exact UInt64.le_refl _
    | exact UInt64.le_of_lt ‹_›
    | exact UInt64.not_lt.mp ‹_›

/-- Importing a block adopts its pulled-up count without losing earlier counts. -/
private theorem reset_adoption_block {before after : Store preset fork} {epoch : Epoch}
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    (clock : before.getCurrentStoreEpoch config = .ok epoch)
    (old : ResetAdoption before epoch)
    (added : before.onBlock config checks sources signed = .ok after) :
    ResetAdoption after epoch := by
  have monotone := Store.onBlock_epochsLe added
  unfold Store.onBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨blockRoot, _, added⟩ := added
  split at added
  · cases added
    exact old
  · unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, transitioned, head, _, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, _, _, transition⟩ := Store.validateOnBlock_ok transitioned
    have stateSlot := (stateTransition_slot transition).2
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have pendingRecord : recorded.unrealizedJustifiedCheckpoint =
        before.unrealizedJustifiedCheckpoint := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        rfl
      · cases record
        rfl
    have pendingBoost : boosted.unrealizedJustifiedCheckpoint =
        before.unrealizedJustifiedCheckpoint := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact pendingRecord
    have maps := (Store.computePulledUpTip_frame added).2.2.1
    have fields : after.blockStates = before.blockStates.insert blockRoot state := by
      rw [maps, Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
    have blockMap := (Store.updateProposerBoostRoot_frame boost).2.1
    rw [(Store.recordBlockTimeliness_frame record).2.1] at blockMap
    have boostedClock := (Store.recordBlockTimeliness_frame record).2.2.2.trans
      (Store.updateProposerBoostRoot_frame boost).2.2.2
    have epochClock : boosted.getCurrentStoreEpoch config = .ok epoch := by
      unfold Store.getCurrentStoreEpoch
      rw [boostedClock.getCurrentSlot]
      exact clock
    unfold Store.computePulledUpTip at added
    simp only [bind_ok_iff] at added
    obtain ⟨s, found, pulled, processed, block, blockOk, current, currentOk, added⟩ := added
    have same : s = state := by
      have found := Store.blockState_ok_iff.mp found
      rw [Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1] at found
      simpa using found.symm
    subst s
    have sameBlock : block = signed.message := by
      have found := Store.block_ok_iff.mp blockOk
      rw [Store.updateUnrealizedCheckpoints_blocks, Store.updateCheckpoints_blocks,
        blockMap] at found
      simpa using found.symm
    subst block
    have epochEq : current = epoch := by
      simp only [Store.getCurrentStoreEpoch, Store.getCurrentSlot] at epochClock
      simpa only [Store.getCurrentStoreEpoch, Store.getCurrentSlot,
        Store.updateUnrealizedCheckpoints_timeMs,
        Store.updateUnrealizedCheckpoints_genesisTimeMs,
        Store.updateCheckpoints_timeMs, Store.updateCheckpoints_genesisTimeMs,
        epochClock, Except.ok.injEq] using currentOk.symm
    subst current
    have pending := reset_unrealized_bounds
      { (boosted.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint)
        with unrealizedJustifications :=
          (boosted.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
            ).unrealizedJustifications.insert blockRoot pulled.currentJustifiedCheckpoint }
      pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
    have pendingOld : before.unrealizedJustifiedCheckpoint =
        (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).unrealizedJustifiedCheckpoint :=
      pendingBoost.symm.trans (reset_update_bounds _ _ _).2.symm
    have finish (pendingOld : before.unrealizedJustifiedCheckpoint.epoch ≤
        after.unrealizedJustifiedCheckpoint.epoch)
        (pendingNew : pulled.currentJustifiedCheckpoint.epoch ≤
          after.unrealizedJustifiedCheckpoint.epoch)
        (realized : getCurrentEpoch state < epoch →
          pulled.currentJustifiedCheckpoint.epoch ≤ after.justifiedCheckpoint.epoch) :
        ResetAdoption after epoch := by
      intro r s p held run
      rw [fields, Std.TreeMap.getElem?_insert] at held
      split at held
      · cases held
        have eq := Except.ok.inj (processed.symm.trans (congrArg
          (Except.mapError ForkChoiceError.transition) run))
        subst p
        exact ⟨pendingNew, realized⟩
      · obtain ⟨a, b⟩ := old r s p held run
        exact ⟨UInt64.le_trans a pendingOld,
          fun earlier => UInt64.le_trans (b earlier) monotone.1⟩
    split at added
    · cases Except.ok.inj added
      apply finish
      · rw [(reset_update_bounds _ _ _).2, pendingOld]
        exact pending.1
      · rw [(reset_update_bounds _ _ _).2]
        exact pending.2
      · intro _
        exact (reset_update_bounds _ _ _).1
    · rename_i notEarlier
      cases Except.ok.inj added
      apply finish
      · rw [pendingOld]
        exact pending.1
      · exact pending.2
      · intro earlier
        exact (notEarlier (by simpa only [getCurrentEpoch, stateSlot] using earlier)).elim

/-- Forward clocks realize each held state's count by the following epoch. -/
private theorem reset_adoption_forward {store : Store preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (slots : 0 < config.SLOT_DURATION_MS)
    (sound : Invariant anchorState)
    (forward : Store.ForwardReachable config anchorState anchorBlock store) :
    ∃ current, store.getCurrentSlot config = .ok current ∧
      ResetAdoption store (computeEpochAtSlot preset current) := by
  induction forward with
  | anchor made =>
    refine ⟨anchorState.slot, getCurrentSlot_getForkchoiceStore slots made, ?_⟩
    obtain ⟨_, _, _, states⟩ := getForkchoiceStore_maps made
    obtain ⟨_, _, _, _, justified, _, pending, _⟩ := getForkchoiceStore_anchor made
    intro root state pulled held run
    rw [states, getElem?_insert_root] at held
    split at held
    · cases Option.some.inj held
      have bound := (processJustificationAndFinalization_invariant sound.ordered sound.settled
        run).2.2.1
      exact ⟨pending ▸ bound, fun _ => justified ▸ bound⟩
    · simp at held
  | tick _ le tick ih =>
    obtain ⟨old, clock, oldAdoption⟩ := ih
    obtain ⟨current, currentOk, same, realized⟩ := reset_tick_realizes positive clock le tick
    refine ⟨current, currentOk, ?_⟩
    intro root state pulled held run
    obtain ⟨a, b⟩ := oldAdoption root state pulled
      ((Store.onTick_frame tick).2.2.2 ▸ held) run
    refine ⟨same ▸ a, fun earlier => ?_⟩
    by_cases cross : computeEpochAtSlot preset old < computeEpochAtSlot preset current
    · exact UInt64.le_trans a (realized cross)
    · exact UInt64.le_trans (b (UInt64.lt_of_lt_of_le earlier (UInt64.not_lt.mp cross)))
        (Store.onTick_frame tick).2.1.1
  | block _ added ih =>
    obtain ⟨current, clock, h⟩ := ih
    exact ⟨current, (Store.onBlock_sameClock added).getCurrentSlot.trans clock,
      reset_adoption_block (by simp [Store.getCurrentStoreEpoch, clock, bind, Except.bind,
        pure, Except.pure]) h added⟩
  | attestation _ attested ih =>
    obtain ⟨current, clock, h⟩ := ih
    refine ⟨current, (Store.onAttestation_sameClock attested).getCurrentSlot.trans clock, ?_⟩
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, valid, _, attested⟩ := attested
    have kept : ResetAdoption stored (computeEpochAtSlot preset current) := by
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

/-- In the next epoch, each honest store has justified what an honest store saw as justified.

The first store is that of an honest validator at an event, in an epoch at most the horizon.

Its unrealized justified checkpoint is the one that the rule records at the end of an epoch.

The receiver is an honest validator whose store is up to date one delay later or more.

The receiver is in a later epoch than the first store.

The first store took the checkpoint from a block that it holds, of its epoch or before.

The receiver holds that block, when its own finalized checkpoint is on the chain of the block.

In a later epoch the receiver takes the unrealized justification of the block as justified.

Otherwise its finalized checkpoint is of a later epoch than the checkpoint. -/
theorem Execution.unrealized_epoch_le_justified_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam)
    {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    (admitted : BlocksAdmitted e 0 Δ last) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon last)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch later : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (bounded : (e.world k).time ≤ last)
    (nonzero : ∀ v ∈ J, ∀ k', (e.world k').time ≤ (e.world k).time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k').state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (laterOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok later)
    (next : epoch < later) :
    ((e.world n).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) := e.forwardReachable
    (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored) i v honest
  have reached := (forward u first n).reachable
  have received := (forward w receiver k).reachable
  have anchorLe : getCurrentEpoch anchorState ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    have lower := (e.epochsLe_of_le w (Nat.zero_le k)).1
    obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor anchored
    simpa only [Execution.world_zero, World.initial, start w receiver, justified] using lower
  by_cases old : ((e.world n).state u).unrealizedJustifiedCheckpoint.epoch ≤
      getCurrentEpoch anchorState
  · exact UInt64.le_trans old anchorLe
  by_cases covered : ((e.world n).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (received.finalized_le_justified sound)
  have recent := UInt64.not_le.mp old
  have child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock := by
    by_contra absent
    have allAnchor {r : Root} {s : BeaconState preset fork}
        (held : ((e.world n).state u).blockStates[r]? = some s) : s = anchorState := by
      obtain ⟨b, known⟩ := reached.known_of_blockState held
      have same : b = anchorBlock := by
        by_contra other
        exact absent ⟨r, b, known, other⟩
      obtain ⟨post, found, anchored, _⟩ := reached.blockStatesFromParents known
      rw [held, Option.some.injEq] at found
      subst post
      exact anchored same
    apply old
    rcases reached.justified_origins _ (.inr rfl) with
      ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
    · exact eq ▸ UInt64.le_refl _
    · rw [eq, allAnchor held]
      exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
    · rw [allAnchor held] at pulled
      rw [eq]
      exact (processJustificationAndFinalization_invariant sound.ordered sound.settled
        pulled).2.2.1
  have aligned : anchorBlock.slot ≤ anchorState.slot := by
    rcases frozen_or_anchor_aligned anchored reached with ⟨boundary, boundaryOk, le⟩ |
      ⟨same, _, _⟩
    · have eq := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      rw [getCurrentEpoch_toNat] at eq
      have bound := Nat.div_mul_le_self anchorState.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      exact UInt64.le_trans le (UInt64.le_iff_toNat_le.mpr (by omega))
    · obtain ⟨_, _, blocks, _⟩ := getForkchoiceStore_maps anchored
      obtain ⟨r, b, known, different⟩ := child
      rw [same, blocks, getElem?_insert_root] at known
      split at known
      · exact (different (Option.some.inj known).symm).elim
      · simp at known
  obtain ⟨current, currentOk, _⟩ := bind_ok_iff.mp epochOk
  have slots := Store.slotDuration_pos currentOk
  have nBound : (e.world n).time ≤ last := by omega
  have epochBound := (forward u first n).justified_epoch_le_current sound slots aligned epochOk
  have senderSlots := (forward u first n).slots_le_current slots aligned
  have carrier : ∀ (root : Root) (state : BeaconState preset fork),
      ((e.world n).state u).blockStates[root]? = some state →
      ((e.world n).state u).getCheckpointBlock root
        ((e.world n).state u).unrealizedJustifiedCheckpoint.epoch =
          .ok ((e.world n).state u).unrealizedJustifiedCheckpoint.root →
      ∃ block, ((e.world k).state w).blocks[root]? = some block := by
    intro root state stored read
    have justified : ((e.world n).state u).Justified
        ((e.world n).state u).unrealizedJustifiedCheckpoint := .inr (.inl rfl)
    have finalRead := reset_finalized_read chain preGloas first receiver nBound bounded justified
      (UInt64.le_trans epochBound.2 inHorizon)
      (UInt64.le_of_lt (UInt64.not_le.mp covered)) read
    obtain ⟨block, known⟩ := reached.known_of_blockState stored
    exact ⟨block, (e.blocks_of_partiallySynchronous sync oneBlock admitted anchored start first
      receiver (by simpa using late) bounded upToDate
      (reset_finalized_known anchored sound slots positive window aligned
        (nonzero w receiver k le_rfl) (forward w receiver k))
      (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) known finalRead).1⟩
  rcases reached.justified_origins _ (.inr rfl) with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
  · rw [same] at recent
    exact (UInt64.lt_irrefl _ recent).elim
  · rcases (walk_checkpoint_ancestor reached sound preGloas positive window aligned
      (nonzero u first n (by omega)) child stored).2.1 with early |
      ⟨_, _, _, _, _, _, read⟩
    · exact (old (same ▸ early)).elim
    obtain ⟨block, held⟩ := carrier root state stored (same ▸ read)
    obtain ⟨post, postOk, _, _⟩ := received.blockStatesFromParents held
    have eq := e.blockStates_eq anchored first receiver (start u first) (start w receiver)
      (oneBlock u first w receiver n k nBound bounded) stored postOk
    subst post
    rw [same]
    exact reset_state_justified_le received sound postOk
  · rcases (walk_pulled_checkpoint_ancestor reached sound preGloas positive window aligned
      (nonzero u first n (by omega)) child stored run).2.1 with early |
      ⟨_, _, _, _, _, _, read⟩
    · exact (old (same ▸ early)).elim
    obtain ⟨block, held⟩ := carrier root state stored (same ▸ read)
    obtain ⟨post, postOk, _, _⟩ := received.blockStatesFromParents held
    have eq := e.blockStates_eq anchored first receiver (start u first) (start w receiver)
      (oneBlock u first w receiver n k nBound bounded) stored postOk
    subst post
    obtain ⟨slot, clock, adoption⟩ := reset_adoption_forward positive slots sound (forward w receiver k)
    have epochEq : computeEpochAtSlot preset slot = later := by
      simpa [Store.getCurrentStoreEpoch, clock, bind, Except.bind, pure, Except.pure] using laterOk
    obtain ⟨senderSlot, senderClock, _, stateBound⟩ := senderSlots
    have senderEpoch : computeEpochAtSlot preset senderSlot = epoch := by
      simpa [Store.getCurrentStoreEpoch, senderClock, bind, Except.bind, pure, Except.pure]
        using epochOk
    have stateEpoch : getCurrentEpoch state ≤ epoch := by
      rw [← senderEpoch, UInt64.le_iff_toNat_le, getCurrentEpoch_toNat,
        computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (stateBound root state stored))
    rw [same]
    exact (adoption root state pulled postOk run).2
      (epochEq ▸ UInt64.lt_of_le_of_lt stateEpoch next)

/-- A store replaces an anchor justification only with a strictly later checkpoint. -/
private theorem reset_fields_after_anchor {anchor store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (reached : Store.Reachable config anchorState anchorBlock store) :
    (store.justifiedCheckpoint = anchor.justifiedCheckpoint ∨
      anchor.justifiedCheckpoint.epoch < store.justifiedCheckpoint.epoch) ∧
    (store.unrealizedJustifiedCheckpoint = anchor.justifiedCheckpoint ∨
      anchor.justifiedCheckpoint.epoch < store.unrealizedJustifiedCheckpoint.epoch) := by
  let P := fun (c : Checkpoint) => c = anchor.justifiedCheckpoint ∨
    anchor.justifiedCheckpoint.epoch < c.epoch
  have newer {c j : Checkpoint} (old : P c) (gt : c.epoch < j.epoch) : P j := by
    rcases old with rfl | lt
    · exact .inr gt
    · exact .inr (UInt64.lt_trans lt gt)
  have update (s : Store preset fork) (j f : Checkpoint)
      (old : P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint) :
      P (s.updateCheckpoints j f).justifiedCheckpoint ∧
        P (s.updateCheckpoints j f).unrealizedJustifiedCheckpoint := by
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split
    all_goals exact ⟨by first | exact newer old.1 ‹_› | exact old.1, old.2⟩
  have updateUn (s : Store preset fork) (j f : Checkpoint)
      (old : P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint) :
      P (s.updateUnrealizedCheckpoints j f).justifiedCheckpoint ∧
        P (s.updateUnrealizedCheckpoints j f).unrealizedJustifiedCheckpoint := by
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split
    all_goals exact ⟨old.1, by first | exact newer old.2 ‹_› | exact old.2⟩
  have pull {s t : Store preset fork} {root : Root}
      (old : P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint)
      (computed : s.computePulledUpTip config root = .ok t) :
      P t.justifiedCheckpoint ∧ P t.unrealizedJustifiedCheckpoint := by
    unfold Store.computePulledUpTip at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, p, _, _, _, _, _, computed⟩ := computed
    have pending := updateUn {s with unrealizedJustifications :=
      s.unrealizedJustifications.insert root p.currentJustifiedCheckpoint}
      p.currentJustifiedCheckpoint p.finalizedCheckpoint old
    split at computed <;> cases Except.ok.inj computed
    · exact update _ _ _ pending
    · exact pending
  change P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint
  induction reached with
  | anchor made =>
    have eq := Except.ok.inj (anchored.symm.trans made)
    subst eq
    obtain ⟨_, _, _, _, justified, _, pending, _⟩ := getForkchoiceStore_anchor made
    exact ⟨.inl rfl, .inl (pending.trans justified.symm)⟩
  | block _ added ih =>
    unfold Store.onBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨_, _, added⟩ := added
    split at added
    · cases added
      exact ih
    · unfold Store.addBlock at added
      simp only [bind_ok_iff] at added
      obtain ⟨state, _, _, _, _, vote, recorded, record, boosted, boost, added⟩ := added
      obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
      have kept : P recorded.justifiedCheckpoint ∧ P recorded.unrealizedJustifiedCheckpoint := by
        unfold Store.recordBlockTimeliness at record
        simp only [bind_ok_iff, pure, Except.pure] at record
        obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
        split at record
        · simp only [bind_ok_iff, Except.ok.injEq] at record
          obtain ⟨_, _, rfl⟩ := record
          exact ih
        · cases record
          exact ih
      have boostedKept : P boosted.justifiedCheckpoint ∧
          P boosted.unrealizedJustifiedCheckpoint := by
        unfold Store.updateProposerBoostRoot at boost
        split at boost
        rotate_left
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
        simp only [bind_ok_iff, pure_bind] at boost
        obtain ⟨_, _, _, _, _, _, boost⟩ := boost
        split at boost <;> cases Except.ok.inj boost <;> exact kept
      exact pull (update _ state.currentJustifiedCheckpoint state.finalizedCheckpoint boostedKept)
        added
  | tick _ ticked ih =>
    exact Store.justified_properties_of_onTick P ih.1 ih.2 ticked
  | attestation _ attested ih =>
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
    have kept : P stored.justifiedCheckpoint ∧ P stored.unrealizedJustifiedCheckpoint := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · cases Except.ok.inj storing
        exact ih
      · simp only [bind_ok_iff] at storing
        obtain ⟨_, _, storing⟩ := storing
        cases Except.ok.inj storing
        exact ih
    split at attested
    · cases Except.ok.inj attested
      exact kept
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
  | attesterSlashing _ slashed ih =>
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact ih
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

/-- A post-anchor store justification has a checkpoint read on a held carrier. -/
private theorem reset_justified_read {anchor store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork), store.blocks[r]? = some b →
      b.stateRoot ≠ Vector.replicate 32 0)
    {checkpoint : Checkpoint}
    (selected : checkpoint = store.justifiedCheckpoint ∨
      checkpoint = store.unrealizedJustifiedCheckpoint)
    (recent : getCurrentEpoch anchorState < checkpoint.epoch) :
    anchorBlock.slot ≤ anchorState.slot ∧
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
  have aligned : anchorBlock.slot ≤ anchorState.slot := by
    rcases frozen_or_anchor_aligned anchored reached with ⟨boundary, boundaryOk, le⟩ |
      ⟨same, _, _⟩
    · have eq := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      rw [getCurrentEpoch_toNat] at eq
      have bound := Nat.div_mul_le_self anchorState.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      exact UInt64.le_trans le (UInt64.le_iff_toNat_le.mpr (by omega))
    · obtain ⟨_, _, blocks, _⟩ := getForkchoiceStore_maps anchored
      obtain ⟨r, b, known, different⟩ := child
      rw [same, blocks, getElem?_insert_root] at known
      split at known
      · exact (different (Option.some.inj known).symm).elim
      · simp at known
  refine ⟨aligned, ?_⟩
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
private theorem reset_honest_target_read {store : Store preset fork}
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

/-- Step 7, the observed justified block: it is safe from the start of the epoch after it.

The caller is an honest validator, at an event of the start of the first slot of an epoch.

At an earlier event, in the epoch before, its store held an unrealized justified checkpoint.

That event is one delay before the call or more.

The rule records that checkpoint at the last slot of an epoch, and reads it at the next call.

The block of the checkpoint is of the epoch before that of the call.

Up to the horizon, the facts of Casper FFG hold.

The finalized block of an honest store is on the chain of each later justified checkpoint.

Two justified checkpoints of one epoch are the same.

Each justified checkpoint after the anchor has an honest vote.

Each honest store up to the last time is in an epoch at most the horizon.

Then the block of the checkpoint is safe from the call to the last time.

The rule also asks that the checkpoint is the unrealized justification of its head.

The statement does not take that fact. -/
theorem Execution.safeAt_observed {Δ : ℕ} (sync : e.Synchronous Δ)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (slots : 0 < config.SLOT_DURATION_MS) {limit : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e limit)
    (admitted : BlocksAdmitted e 0 Δ limit) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch}
    (chain : FinalizedPrefix e horizon limit)
    (unique : OneJustifiedPerEpoch e horizon limit)
    (voted : JustifiedByHonestVote e anchor.justifiedCheckpoint.epoch horizon limit)
    {u : ValidatorIndex} (caller : u ∈ J) {m n : ℕ}
    (recorded : (e.world m).time + Δ ≤ (e.world n).time)
    {previous epoch : Epoch} {slot : Slot} {begin : UInt64}
    {observedBlock : BeaconBlock preset fork}
    (previousOk : ((e.world m).state u).getCurrentStoreEpoch config = .ok previous)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (next : addChecked previous 1 = .ok epoch)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (isStart : isStartSlotAtEpoch preset slot = .ok true)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atStart : (e.world n).time = begin.toNat)
    (found : ((e.world n).state u).block
      ((e.world m).state u).unrealizedJustifiedCheckpoint.root = .ok observedBlock)
    (blockEpoch : addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch)
    (nonzero : ∀ v ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time ((e.world m).state u).unrealizedJustifiedCheckpoint.root := by
  intro time
  -- A later justification has an earlier honest supporting vote, where safety is already known.
  induction time using Nat.strong_induction_on with
  | h time ih =>
    intro late bounded
    have nBound : (e.world n).time ≤ limit := late.trans bounded
    have mBound : (e.world m).time ≤ limit := by omega
    have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) := e.forwardReachable
      (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored) i v honest
    have reached := (forward u caller m).reachable
    rcases (reset_fields_after_anchor anchored reached).2 with same | recent
    · obtain ⟨_, _, _, _, justified, final, _⟩ := getForkchoiceStore_anchor anchored
      have eq : anchor.justifiedCheckpoint = anchor.finalizedCheckpoint :=
        justified.trans final.symm
      rw [same, eq]
      exact e.safeAt_anchor anchored start time
    obtain ⟨_, _, _, _, anchorJustified, _⟩ := getForkchoiceStore_anchor anchored
    have recent' : getCurrentEpoch anchorState <
        ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch := by
      simpa only [anchorJustified] using recent
    obtain ⟨aligned, carrier, checkpointRead⟩ := reset_justified_read anchored reached sound
      preGloas positive window (nonzero u caller m mBound) (.inr rfl) recent'
    obtain ⟨boundary, block, boundaryOk, blockKnown, blockLe, _⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas checkpointRead
    have blockEq := oneBlock u caller u caller m n mBound nBound _ block observedBlock blockKnown
      (Store.block_ok_iff.mp found)
    subst block
    have checkpointLe :=
      (forward u caller m).justified_epoch_le_current sound slots aligned previousOk
    have previousHorizon := inHorizon u caller m previous mBound previousOk
    have checkpointHorizon := UInt64.le_trans checkpointLe.2 previousHorizon
    have observedEpoch : computeEpochAtSlot preset observedBlock.slot = previous := by
      have a := (addChecked_ok_iff.mp blockEpoch).2
      have b := (addChecked_ok_iff.mp next).2
      apply UInt64.toNat_inj.mp
      omega
    have previousLe : previous ≤ ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch := by
      rw [← observedEpoch, UInt64.le_iff_toNat_le, computeEpochAtSlot, UInt64.toNat_div]
      have low := UInt64.le_iff_toNat_le.mp blockLe
      rw [(computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2] at low
      exact (Nat.div_le_div_right low).trans_eq (Nat.mul_div_cancel _ positive)
    have checkpointEpoch : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch = previous :=
      UInt64.le_antisymm checkpointLe.2 previousLe
    have afterAnchor : getCurrentEpoch anchorState < previous := checkpointEpoch ▸ recent'
    have slotEpoch : computeEpochAtSlot preset slot = epoch := by
      simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using epochOk
    have firstOk : computeStartSlotAtEpoch preset epoch = .ok slot := by
      rw [← slotEpoch]
      have first := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
      have test := isStart
      unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at test
      rw [first] at test
      simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        decide_eq_true_eq] at test
      have rounded := (computeStartSlotAtEpoch_ok_iff.mp first).2
      have below : (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat ≤ slot.toNat := by
        rw [rounded, computeEpochAtSlot, UInt64.toNat_div]
        exact Nat.div_mul_le_self _ _
      have zero := congrArg UInt64.toNat test
      simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
      have upper := slot.toNat_lt
      have lower := (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
      have eq : slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH = slot :=
        UInt64.toNat_inj.mp (by omega)
      simpa only [eq] using first
    obtain ⟨senderSlot, senderSlotOk, _⟩ := bind_ok_iff.mp previousOk
    obtain ⟨v, honest, signed⟩ := voted u caller m mBound _ senderSlot
      (.inr (.inl rfl)) senderSlotOk recent checkpointHorizon
    obtain ⟨signer, data, duty, _, _⟩ := e.exists_maySign_of_signsTargetBefore honest signed
    obtain ⟨_, _, _, genesis, _⟩ := duty
    -- The honest vote identifies the genesis time shared by all anchored stores.
    have common (w : ValidatorIndex) (honestW : w ∈ J) (i : ℕ) :
        ((e.world i).state w).genesisTimeMs = genesisTimeMs := by
      have a := (e.clock_bounds w i).1
      have b := (e.clock_bounds v signer).1
      rw [start w honestW] at a
      rw [start v honest] at b
      exact a.trans (b.symm.trans genesis)
    intro w receiver k head atTime current headOk
    have kBound : (e.world k).time ≤ limit := atTime ▸ bounded
    obtain ⟨currentSlot, currentSlotOk, _, _⟩ :=
      (forward w receiver k).slots_le_current slots aligned
    have currentEpoch : ((e.world k).state w).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset currentSlot) := by
      simp [Store.getCurrentStoreEpoch, currentSlotOk, bind, Except.bind, pure, Except.pure]
    have slotLe : slot ≤ currentSlot := by
      have currentSlotOk := mapError_ok_iff.mp currentSlotOk
      change computeSlotAtTimeMs config _ _ = _ at currentSlotOk
      rw [common w receiver k] at currentSlotOk
      exact computeSlotAtTimeMs_mono
        (UInt64.le_iff_toNat_le.mpr (by rw [current.1]; omega))
        (computeSlotAtTimeMs_computeTimeAtSlotMs slots beginOk) currentSlotOk
    have epochLe : epoch ≤ computeEpochAtSlot preset currentSlot := by
      rw [← slotEpoch, UInt64.le_iff_toNat_le]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp slotLe)
    have nextLt : previous < computeEpochAtSlot preset currentSlot := by
      have sum := (addChecked_ok_iff.mp next).2
      have le := UInt64.le_iff_toNat_le.mp epochLe
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [UInt64.toNat_one] at sum
      omega
    have lower := e.unrealized_epoch_le_justified_epoch sync positive window preGloas oneBlock
      admitted anchored sound start chain caller receiver previousOk previousHorizon
      (by omega) kBound (fun v hv j before => nonzero v hv j (before.trans kBound))
      current currentEpoch nextLt
    have headAbove := Store.isAncestor_getHead headOk
    have justifiedKnown : ∃ b, ((e.world k).state w).blocks[
        ((e.world k).state w).justifiedCheckpoint.root]? = some b := by
      unfold Store.isAncestor at headAbove
      obtain ⟨b, found, _⟩ := bind_ok_iff.mp headAbove
      exact ⟨b, Store.block_ok_iff.mp found⟩
    obtain ⟨justifiedBlock, justifiedKnown⟩ := justifiedKnown
    by_cases sameEpoch : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch =
        ((e.world k).state w).justifiedCheckpoint.epoch
    · have same := unique u caller w receiver m k mBound kBound _ _ (.inr (.inl rfl))
        (.inl rfl) sameEpoch checkpointHorizon
      simpa only [same] using headAbove
    have later : epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch := by
      have gt := UInt64.lt_of_le_of_ne lower sameEpoch
      rw [checkpointEpoch] at gt
      have gt := UInt64.lt_iff_toNat_lt.mp gt
      have sum := (addChecked_ok_iff.mp next).2
      apply UInt64.le_iff_toNat_le.mpr
      simp only [UInt64.toNat_one] at sum
      omega
    have justifiedHorizon := UInt64.le_trans
      ((forward w receiver k).justified_epoch_le_current sound slots aligned currentEpoch).1
      (inHorizon w receiver k _ kBound currentEpoch)
    obtain ⟨v, honest, signer, data, supportHead, duty, target, afterBegin, beforeTime,
        supportHeadOk, supports⟩ := e.exists_supporting_head_of_justified_epoch_start fits voted
      start receiver kBound (.inl rfl) currentSlotOk current
      (UInt64.lt_of_lt_of_le recent lower) justifiedHorizon firstOk beginOk later
      (fun earlier low high => ih earlier (by omega) (by omega) (by omega))
    obtain ⟨committee, _, _, _, _, honestData, _⟩ := duty
    obtain ⟨tip, tipBlock, base, advanced, tipOk, tipKnown, stored, advancedOk, made⟩ := honestData
    have tipEq := Except.ok.inj (tipOk.symm.trans supportHeadOk)
    subst tip
    have sourceKnown : ∃ b, ((e.world signer).state v).blocks[
        ((e.world m).state u).unrealizedJustifiedCheckpoint.root]? = some b := by
        unfold Store.isAncestor at supports
        obtain ⟨b, found, _⟩ := bind_ok_iff.mp supports
        exact ⟨b, Store.block_ok_iff.mp found⟩
    obtain ⟨sourceBlock, sourceKnown⟩ := sourceKnown
    have sourceEq := oneBlock v honest u caller signer n (by omega) nBound _ _ observedBlock
      sourceKnown (Store.block_ok_iff.mp found)
    subst sourceBlock
    obtain ⟨tipBlock', tipKnown', below⟩ := Store.slot_le_of_isAncestor sourceKnown supports
    rw [tipKnown, Option.some.injEq] at tipKnown'
    subst tipBlock'
    have other : tipBlock ≠ anchorBlock := by
      intro same
      have bound := UInt64.le_trans below (same ▸ aligned)
      have epochBound : computeEpochAtSlot preset observedBlock.slot ≤
          getCurrentEpoch anchorState := by
        rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, computeEpochAtSlot, UInt64.toNat_div]
        exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp bound)
      exact UInt64.not_le.mpr afterAnchor (observedEpoch ▸ epochBound)
    have targetRead := reset_honest_target_read (forward v honest signer).reachable positive aligned
      (nonzero v honest signer (by omega)) tipKnown (Store.blockState_ok_iff.mp stored)
      other advancedOk made (by rw [target]; exact UInt64.lt_of_lt_of_le recent' lower)
    have dataRoot := (getAttestationData_eq_ok_iff.mp made).2.2.2.1
    rw [dataRoot] at targetRead
    unfold Store.getCheckpointBlock at targetRead
    simp only [bind_ok_iff] at targetRead
    obtain ⟨targetSlot, targetSlotOk, targetNode, targetWalk, targetRoot⟩ := targetRead
    have targetSlotOk := mapError_ok_iff.mp targetSlotOk
    have rootEq : targetNode.root = ((e.world k).state w).justifiedCheckpoint.root :=
      (Except.ok.inj targetRoot).trans (congrArg Checkpoint.root target)
    have pending := Store.getAncestor_pending_of_lt preGloas rfl targetWalk
    have nodeEq : targetNode = ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ := by
      cases targetNode
      exact congrArg₂ ForkChoiceNode.mk rootEq pending
    subst targetNode
    have belowTarget : observedBlock.slot ≤ targetSlot := by
      have startNat := (computeStartSlotAtEpoch_ok_iff.mp targetSlotOk).2
      rw [target] at startNat
      have lt := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt previousLe
        (UInt64.lt_of_le_of_ne lower sameEpoch))
      rw [← observedEpoch] at lt
      simp only [computeEpochAtSlot, UInt64.toNat_div] at lt
      have lt := (Nat.div_lt_iff_lt_mul positive).mp lt
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have sourceWalk := Store.getAncestor_of_isAncestor_of_lt preGloas sourceKnown supports
    have targetAncestor : ((e.world signer).state v).getAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ observedBlock.slot =
        .ok ⟨((e.world m).state u).unrealizedJustifiedCheckpoint.root, .pending⟩ := by
      have roots := Store.getAncestor_root (store := (e.world signer).state v)
        supportHead .pending observedBlock.slot
      rw [sourceWalk, Store.getAncestor_trans belowTarget targetWalk] at roots
      cases walk : ((e.world signer).state v).getAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ observedBlock.slot with
      | error error => simp [walk] at roots
      | ok node =>
        have root : node.root = ((e.world m).state u).unrealizedJustifiedCheckpoint.root := by
          simpa [walk] using roots.symm
        have status := Store.getAncestor_pending_of_lt preGloas rfl walk
        have eq : node = ⟨((e.world m).state u).unrealizedJustifiedCheckpoint.root, .pending⟩ := by
          cases node
          exact congrArg₂ ForkChoiceNode.mk root status
        exact congrArg Except.ok eq
    -- Equal block data carries the supporting vote's ancestry into the receiver's store.
    have receiverWalk := Store.getAncestor_of_same_blocks (forward w receiver k).reachable
      (oneBlock v honest w receiver signer k (by omega) kBound)
      ((forward u caller n).reachable.anchorSlot_le_block (Store.block_ok_iff.mp found))
      ⟨justifiedBlock, justifiedKnown⟩ targetAncestor
    obtain ⟨observed, observedKnown, _⟩ := Store.getAncestor_le receiverWalk
    have observedEq := oneBlock w receiver u caller k n kBound nBound _ observed observedBlock
      observedKnown (Store.block_ok_iff.mp found)
    subst observed
    have ancestry : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨((e.world m).state u).unrealizedJustifiedCheckpoint.root, .pending⟩ = .ok true := by
      simp [Store.isAncestor, Store.block_ok_iff.mpr observedKnown, receiverWalk,
        bind, Except.bind, pure, Except.pure]
    exact Store.isAncestor_trans_of_lt preGloas justifiedKnown observedKnown headAbove ancestry

/-- The block of the finalized checkpoint is that of the anchor, or is two epochs old.

A call that falls back to the finalized block and confirms nothing stores that block.

The induction needs its age, and `Execution.finalizedCheckpoint_eq_of_checked` needs a check.

So this is the same bound, read off the block of the checkpoint without a check. -/
theorem Execution.finalizedCheckpoint_eq_or_blockEpoch_add_two_le {anchor : Store preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (honest : u ∈ J) (start : e.start u = anchor) {n : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state u).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {epoch : Epoch} (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint ∨
      ∃ rootEpoch,
        ((e.world n).state u).getBlockEpoch ((e.world n).state u).finalizedCheckpoint.root =
          .ok rootEpoch ∧ rootEpoch.toNat + 2 ≤ epoch.toNat := by
  have _ := honest
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) := by
    clear epochOk nonzero
    induction n with
    | zero =>
      change Store.ForwardReachable config anchorState anchorBlock (e.start u)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n u with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.forwardReachable ih
  have reached := forward.reachable
  unfold Store.getCurrentStoreEpoch at epochOk
  rw [bind_ok_iff] at epochOk
  obtain ⟨slot, slotOk, epochOk⟩ := epochOk
  obtain ⟨current, clock, age⟩ := resetAge_forward anchored sound
    (Store.slotDuration_pos slotOk) forward
  rw [slotOk, Except.ok.injEq] at clock
  subst current
  cases Except.ok.inj epochOk
  rcases age.1 with same | ⟨later, old⟩
  · exact .inl same
  right
  obtain ⟨anchorRoot, hash, _, _, _, final, _⟩ := getForkchoiceStore_anchor anchored
  have later' : getCurrentEpoch anchorState < ((e.world n).state u).finalizedCheckpoint.epoch := by
    simpa only [final] using later
  have origin := reached.finalized_origins _ (.inl rfl)
  -- Some held block is not the anchor block, or every held state is the anchor state.
  have child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state u).blocks[r]? = some b ∧ b ≠ anchorBlock := by
    by_contra absent
    have allAnchor {r : Root} {s : BeaconState preset fork}
        (held : ((e.world n).state u).blockStates[r]? = some s) : s = anchorState := by
      obtain ⟨b, known⟩ := reached.known_of_blockState held
      have same : b = anchorBlock := by
        by_contra other
        exact absent ⟨r, b, known, other⟩
      obtain ⟨post, found, anchoredState, _⟩ := reached.blockStatesFromParents known
      rw [held, Option.some.injEq] at found
      subst post
      exact anchoredState same
    have upper : ((e.world n).state u).finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState := by
      rcases origin with ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
      · exact eq ▸ UInt64.le_refl _
      · rw [eq, allAnchor held]
        exact UInt64.le_trans (Store.finalized_le_currentJustified sound.ordered)
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _))
      · rw [allAnchor held] at pulled
        have inv := processJustificationAndFinalization_invariant sound.ordered sound.settled pulled
        rw [eq]
        exact UInt64.le_trans (Store.finalized_le_currentJustified inv.1) inv.2.2.1
    exact UInt64.not_le.mpr later' upper
  have aligned : anchorBlock.slot ≤ anchorState.slot := by
    rcases frozen_or_anchor_aligned anchored reached with ⟨first, firstOk, le⟩ | ⟨_, eq, _⟩
    · have firstEq := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
      rw [getCurrentEpoch_toNat] at firstEq
      have lower := Nat.div_mul_le_self anchorState.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      exact UInt64.le_trans le (UInt64.le_iff_toNat_le.mpr (by omega))
    · rw [eq] at later
      exact (UInt64.lt_irrefl _ later).elim
  -- The finalized block is at or before the start of the finalized epoch.
  have rootBound : ∃ first b,
      computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch = .ok first ∧
      ((e.world n).state u).blocks[((e.world n).state u).finalizedCheckpoint.root]? = some b ∧
      b.slot ≤ first := by
    rcases origin with ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
    · rw [eq] at later'
      exact (UInt64.lt_irrefl _ later').elim
    · have bound := (reached.blockState_checkpoint_roots sound positive window aligned
        nonzero child held).2.2
      rw [← eq] at bound
      exact bound.resolve_left (UInt64.not_le.mpr later')
    · have bound := reached.pulled_finalized_root sound positive window aligned nonzero
        child held pulled
      rw [← eq] at bound
      exact bound.resolve_left (UInt64.not_le.mpr later')
  obtain ⟨first, b, firstOk, known, lower⟩ := rootBound
  have bound : (computeEpochAtSlot preset b.slot).toNat ≤
      ((e.world n).state u).finalizedCheckpoint.epoch.toNat := by
    have le := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp lower)
    have atStart := computeEpochAtSlot_computeStartSlotAtEpoch
      (UInt64.lt_iff_toNat_lt.mpr positive) firstOk
    simpa only [← atStart, computeEpochAtSlot, UInt64.toNat_div] using le
  refine ⟨computeEpochAtSlot preset b.slot, ?_, by omega⟩
  simp [Store.getBlockEpoch, Store.block_ok_iff.mpr known, bind, Except.bind, pure, Except.pure]

end EthLib.Consensus.Models.Network
