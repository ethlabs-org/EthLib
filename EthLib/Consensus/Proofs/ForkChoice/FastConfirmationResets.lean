module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCheckpoints

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

private theorem ancestor_pending_of_walk {store : Store preset fork}
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
private theorem anchor_walk_of_reachable {store anchor : Store preset fork}
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
    store.finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat) ∧
  (store.unrealizedFinalizedCheckpoint = anchor ∨
    store.unrealizedFinalizedCheckpoint.epoch.toNat + 1 ≤ epoch.toNat) ∧
  anchor.epoch ≤ store.finalizedCheckpoint.epoch ∧
  anchor.epoch ≤ store.unrealizedFinalizedCheckpoint.epoch

private theorem resetAge_mono {anchor : Checkpoint} {s : Store preset fork} {a b : Epoch}
    (h : ResetAge anchor s a) (le : a ≤ b) : ResetAge anchor s b := by
  have le := UInt64.le_iff_toNat_le.mp le
  rcases h with ⟨hf, hu, lowF, lowU⟩
  exact ⟨hf.imp id (by omega), hu.imp id (by omega), lowF, lowU⟩

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
      exact ⟨.inr (by dsimp only; omega), hu,
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
      exact ⟨hf, .inr (by dsimp only; omega), lowF,
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
  exact h.1

/-- Step 7, the recent start: the rule confirms a block after the finalized one of the anchor only.

The rule has passed its checks from the finalized block of an honest store to a later block.

The checks ask for a start of the current epoch or the one before.

A finalized checkpoint after that of the anchor is two epochs old, and its block is older.

So the finalized checkpoint of the store is that of the anchor. -/
theorem Execution.finalizedCheckpoint_eq_of_checked {anchor : Store preset fork}
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
  sorry

/-- A delay later, each honest store has justified the epoch that an honest store finalized.

The first store is that of an honest validator at an event, in an epoch at most the horizon.

The receiver is an honest validator whose store is up to date one delay later or more.

The first store took its finalized checkpoint from a block that it holds.

The receiver holds that block, when its own finalized checkpoint is on the chain of the block.

Otherwise its finalized checkpoint is of a later epoch, and so is its justified one.

The proof uses the finalized chain to place the finalized checkpoint of the receiver. -/
theorem Execution.finalized_epoch_le_justified_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (nonzero : ∀ v ∈ J, ∀ k', (e.world k').time ≤ (e.world k).time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k').state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) :
    ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  sorry

/-- Step 7, the finalized block: it is safe from one delay after an honest store holds it.

The store is that of an honest validator at an event.

Each honest store up to the last time is in an epoch at most the horizon.

A delay later, each honest store has justified the finalized epoch or a later one.

The finalized block is on the chain of that justified block, by the finalized chain.

The head of a store is above its justified block. -/
theorem Execution.safeAt_finalized {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {epoch : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) {limit : ℕ}
    (nonzero : ∀ v ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time + Δ ≤ time → time ≤ limit →
      SafeAt e time ((e.world n).state u).finalizedCheckpoint.root := by
  sorry

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
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    {u w : ValidatorIndex} (first : u ∈ J) (receiver : w ∈ J) {n k : ℕ} {epoch later : Epoch}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon) (late : (e.world n).time + Δ ≤ (e.world k).time)
    (nonzero : ∀ v ∈ J, ∀ k', (e.world k').time ≤ (e.world k).time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k').state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (laterOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok later)
    (next : epoch < later) :
    ((e.world n).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  sorry

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
    (slots : 0 < config.SLOT_DURATION_MS) (votes : Votes e.startTime e)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e)
    (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e 0 Δ) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} (chain : FinalizedPrefix e horizon)
    (unique : OneJustifiedPerEpoch e horizon)
    (voted : JustifiedByHonestVote e anchor.justifiedCheckpoint.epoch horizon)
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
    {limit : ℕ}
    (nonzero : ∀ v ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current → current ≤ horizon) :
    ∀ time, (e.world n).time ≤ time → time ≤ limit →
      SafeAt e time ((e.world m).state u).unrealizedJustifiedCheckpoint.root := by
  sorry

end EthLib.Consensus.Models.Network
