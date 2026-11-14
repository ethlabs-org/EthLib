module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.ForwardClock

/-!
# Proofs: the epochs of realized finalized checkpoint origins

A pulled-up checkpoint becomes realized only after the epoch of its counting state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

private theorem epoch_mono {a b : Slot} (le : a ≤ b) :
    computeEpochAtSlot preset a ≤ computeEpochAtSlot preset b := by
  simp only [computeEpochAtSlot, UInt64.le_iff_toNat_le, UInt64.toNat_div] at *
  exact Nat.div_le_div_right le

private theorem epoch_lt_at_boundary {a b : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (lt : a < b)
    (boundary : computeSlotsSinceEpochStart preset b = .ok 0) :
    computeEpochAtSlot preset a < computeEpochAtSlot preset b := by
  simp only [computeSlotsSinceEpochStart, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at boundary
  obtain ⟨first, firstOk, sub⟩ := boundary
  have bound := (computeStartSlotAtEpoch_le_lt
    (UInt64.lt_iff_toNat_lt.mpr positive) firstOk).1
  have value := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have same : b.toNat = first.toNat := by
    have := congrArg UInt64.toNat sub
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr bound)] at this
    simp only [UInt64.toNat_zero] at this
    omega
  simp only [computeEpochAtSlot, UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at *
  apply (Nat.div_lt_iff_lt_mul positive).mpr
  rw [← value, ← same]
  exact lt

private def FinalOrigin (anchor : Checkpoint) (store : Store preset fork)
    (epoch : Epoch) (checkpoint : Checkpoint) : Prop :=
  checkpoint = anchor ∨
    (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
      checkpoint = state.finalizedCheckpoint ∧ getCurrentEpoch state ≤ epoch) ∨
    ∃ (root : Root) (state pulled : BeaconState preset fork),
      store.blockStates[root]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧
      checkpoint = pulled.finalizedCheckpoint ∧ getCurrentEpoch state < epoch

private theorem FinalOrigin.mono {anchor checkpoint : Checkpoint}
    {s t : Store preset fork} {a b : Epoch}
    (kept : ∀ (root : Root) (state : BeaconState preset fork), s.blockStates[root]? = some state →
      t.blockStates[root]? = some state) (le : a ≤ b)
    (origin : FinalOrigin anchor s a checkpoint) : FinalOrigin anchor t b checkpoint := by
  rcases origin with same | ⟨r, s, found, same, bound⟩ |
    ⟨r, s, p, found, run, same, bound⟩
  · exact .inl same
  · exact .inr (.inl ⟨r, s, kept r s found, same, UInt64.le_trans bound le⟩)
  · exact .inr (.inr ⟨r, s, p, kept r s found, run, same, UInt64.lt_of_lt_of_le bound le⟩)

private theorem realized_tick {config : Config} {s t : Store preset fork}
    {anchor : Checkpoint} {time : UInt64} {a b : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (tick : s.onTickPerSlot config time = .ok t)
    (old : s.getCurrentSlot config = .ok a) (next : t.getCurrentSlot config = .ok b)
    (le : a ≤ b)
    (realized : FinalOrigin anchor s (computeEpochAtSlot preset a) s.finalizedCheckpoint)
    (pending : ∀ epoch, computeEpochAtSlot preset a < epoch →
      FinalOrigin anchor s epoch s.unrealizedFinalizedCheckpoint) :
    FinalOrigin anchor t (computeEpochAtSlot preset b) t.finalizedCheckpoint ∧
      (∀ epoch, computeEpochAtSlot preset b < epoch →
        FinalOrigin anchor t epoch t.unrealizedFinalizedCheckpoint) := by
  have maps := (Store.onTickPerSlot_frame tick).2.2.2.2.1
  have carry {epoch checkpoint} (h : FinalOrigin anchor s epoch checkpoint) :
      FinalOrigin anchor t epoch checkpoint :=
    h.mono (fun _ _ found => maps.symm ▸ found) (UInt64.le_refl _)
  constructor
  · rcases Store.finalized_of_onTickPerSlot tick with same |
      ⟨previous, current, previousOk, currentOk, later, boundary, same⟩
    · rw [same]
      exact realized.mono (fun _ _ found => maps.symm ▸ found) (epoch_mono le)
    · rw [old, Except.ok.injEq] at previousOk
      rw [next, Except.ok.injEq] at currentOk
      subst previous current
      rw [same]
      exact carry (pending _ (epoch_lt_at_boundary positive later boundary))
  · intro epoch later
    have oldLater := UInt64.lt_of_le_of_lt (epoch_mono le) later
    exact (Store.finalized_properties_of_onTickPerSlot (FinalOrigin anchor t epoch)
      (realized.mono (fun _ _ found => maps.symm ▸ found)
        (UInt64.le_of_lt oldLater)) (carry (pending epoch oldLater)) tick).2

private theorem catchUp_slot {config : Config} {s t : Store preset fork} {target a : Slot}
    (caught : Store.catchUp config s target = .ok t)
    (old : s.getCurrentSlot config = .ok a) (le : a ≤ target) :
    t.getCurrentSlot config = .ok target := by
  induction s using Store.catchUp.induct config target generalizing a with
  | _ s ih =>
    rw [Store.catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, currentOk, caught⟩ := caught
    rw [old, Except.ok.injEq] at currentOk
    subst current
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, nextOk, time, timeOk, ticked, tick, caught⟩ := caught
      have nextValue := (addChecked_ok_iff.mp (mapError_ok_iff.mp nextOk)).2
      simp only [UInt64.toNat_one] at nextValue
      have slot : ticked.getCurrentSlot config = .ok next := by
        unfold Store.getCurrentSlot
        rw [(Store.onTickPerSlot_frame tick).1, (Store.onTickPerSlot_frame tick).2.1,
          computeSlotAtTimeMs_computeTimeAtSlotMs (Store.slotDuration_pos old)
            (mapError_ok_iff.mp timeOk)]
        rfl
      split at caught
      · exact ih ticked ‹_› caught slot (UInt64.le_iff_toNat_le.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp ‹a < target›
          omega))
      · cases caught
    · have eq : a = target := UInt64.le_antisymm le (UInt64.not_lt.mp ‹¬ a < target›)
      cases caught
      simpa only [eq] using old

private theorem realized_catchUp {config : Config} {s t : Store preset fork}
    {anchor : Checkpoint} {target a : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (caught : Store.catchUp config s target = .ok t)
    (old : s.getCurrentSlot config = .ok a) (le : a ≤ target)
    (realized : FinalOrigin anchor s (computeEpochAtSlot preset a) s.finalizedCheckpoint)
    (pending : ∀ epoch, computeEpochAtSlot preset a < epoch →
      FinalOrigin anchor s epoch s.unrealizedFinalizedCheckpoint) :
    FinalOrigin anchor t (computeEpochAtSlot preset target) t.finalizedCheckpoint ∧
      (∀ epoch, computeEpochAtSlot preset target < epoch →
        FinalOrigin anchor t epoch t.unrealizedFinalizedCheckpoint) := by
  induction s using Store.catchUp.induct config target generalizing a with
  | _ s ih =>
    rw [Store.catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, currentOk, caught⟩ := caught
    rw [old, Except.ok.injEq] at currentOk
    subst current
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, nextOk, time, timeOk, ticked, tick, caught⟩ := caught
      have nextValue := (addChecked_ok_iff.mp (mapError_ok_iff.mp nextOk)).2
      simp only [UInt64.toNat_one] at nextValue
      have slot : ticked.getCurrentSlot config = .ok next := by
        unfold Store.getCurrentSlot
        rw [(Store.onTickPerSlot_frame tick).1, (Store.onTickPerSlot_frame tick).2.1,
          computeSlotAtTimeMs_computeTimeAtSlotMs (Store.slotDuration_pos old)
            (mapError_ok_iff.mp timeOk)]
        rfl
      have bounds : a ≤ next ∧ next ≤ target := by
        simp only [UInt64.le_iff_toNat_le]
        have := UInt64.lt_iff_toNat_lt.mp ‹a < target›
        omega
      obtain ⟨realized, pending⟩ := realized_tick positive tick old slot bounds.1 realized pending
      split at caught
      · exact ih ticked ‹_› caught slot bounds.2 realized pending
      · cases caught
    · have eq : a = target := UInt64.le_antisymm le (UInt64.not_lt.mp ‹¬ a < target›)
      cases caught
      simpa only [eq] using And.intro realized pending

private theorem realized_block {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {s t : Store preset fork} {anchor : Checkpoint} {slot : Slot}
    (old : s.getCurrentSlot config = .ok slot)
    (kept : ∀ (root : Root) (state : BeaconState preset fork),
      s.blockStates[root]? = some state → t.blockStates[root]? = some state)
    (realized : FinalOrigin anchor s (computeEpochAtSlot preset slot) s.finalizedCheckpoint)
    (pending : ∀ epoch, computeEpochAtSlot preset slot < epoch →
      FinalOrigin anchor s epoch s.unrealizedFinalizedCheckpoint)
    (added : s.onBlock config checks sources signed = .ok t) :
    FinalOrigin anchor t (computeEpochAtSlot preset slot) t.finalizedCheckpoint ∧
      (∀ epoch, computeEpochAtSlot preset slot < epoch →
        FinalOrigin anchor t epoch t.unrealizedFinalizedCheckpoint) := by
  cases root : Serialization.Ssz.SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : s.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact ⟨realized, pending⟩
    obtain ⟨⟨checked, checkedOk, bound⟩, -⟩ := Store.onBlock_checks root known added
    rw [old, Except.ok.injEq] at checkedOk
    subst checked
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨pre, -, -, -, transition⟩ := Store.validateOnBlock_ok valid
    have stateSlot := (stateTransition_slot transition).2
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedFields : recorded.finalizedCheckpoint = s.finalizedCheckpoint ∧
        recorded.unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ⟨rfl, rfl⟩
      · cases record
        exact ⟨rfl, rfl⟩
    have boostedFields : boosted.finalizedCheckpoint = s.finalizedCheckpoint ∧
        boosted.unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedFields
    have maps := (Store.computePulledUpTip_frame added).2.2.1
    have newFound : t.blockStates[blockRoot]? = some state := by
      rw [maps, Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
      simp
    have newBlock : t.blocks[blockRoot]? = some signed.message := by
      rw [(Store.computePulledUpTip_frame added).2.1, Store.updateCheckpoints_blocks,
        (Store.updateProposerBoostRoot_frame boost).2.1,
        (Store.recordBlockTimeliness_frame record).2.1]
      simp
    have sameClock : Store.SameClock s boosted :=
      (Store.recordBlockTimeliness_frame record).2.2.2.1.trans
        (Store.updateProposerBoostRoot_frame boost).2.2.2.1
    have clock : (boosted.updateCheckpoints state.currentJustifiedCheckpoint
        state.finalizedCheckpoint).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset slot) := by
      have same : Store.SameClock s
          (boosted.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint) :=
        ⟨(Store.updateCheckpoints_timeMs _ _).trans sameClock.1,
          (Store.updateCheckpoints_genesisTimeMs _ _).trans sameClock.2⟩
      simp only [Store.getCurrentStoreEpoch, same.getCurrentSlot, old,
        bind, Except.bind, pure, Except.pure]
    have stateBound : getCurrentEpoch state ≤ computeEpochAtSlot preset slot := by
      exact epoch_mono (stateSlot ▸ bound)
    have origin : FinalOrigin anchor t (computeEpochAtSlot preset slot) state.finalizedCheckpoint :=
      .inr (.inl ⟨blockRoot, state, newFound, rfl, stateBound⟩)
    have updated : FinalOrigin anchor t (computeEpochAtSlot preset slot)
        (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).finalizedCheckpoint :=
      Store.updateCheckpoints_finalized_property (boostedFields.1 ▸
        realized.mono kept (UInt64.le_refl _)) origin
    constructor
    · rcases Store.finalized_of_computePulledUpTip added with same |
        ⟨st, pulled, block, epoch, found, run, blockFound, epochOk, earlier, same⟩
      · exact same ▸ updated
      · have found' : t.blockStates[blockRoot]? = some st := maps.symm ▸ found
        rw [newFound, Option.some.injEq] at found'
        subst st
        have blockFound' : t.blocks[blockRoot]? = some block :=
          (Store.computePulledUpTip_frame added).2.1.symm ▸ blockFound
        rw [newBlock, Option.some.injEq] at blockFound'
        subst block
        have epochEq : epoch = computeEpochAtSlot preset slot := by
          rw [clock, Except.ok.injEq] at epochOk
          exact epochOk.symm
        subst epoch
        exact .inr (.inr ⟨blockRoot, state, pulled, newFound, run, same,
          by simpa only [getCurrentEpoch, stateSlot] using earlier⟩)
    · intro epoch later
      apply (Store.finalized_properties_of_computePulledUpTip (FinalOrigin anchor t epoch)
        (updated.mono (fun _ _ h => h) (UInt64.le_of_lt later)) ?_ ?_ added).2
      · have eq : (boosted.updateCheckpoints state.currentJustifiedCheckpoint
            state.finalizedCheckpoint).unrealizedFinalizedCheckpoint =
            s.unrealizedFinalizedCheckpoint := by
          unfold Store.updateCheckpoints
          split <;> dsimp only <;> split <;> exact boostedFields.2
        rw [eq]
        exact (pending epoch later).mono kept (UInt64.le_refl _)
      · intro st pulled found run
        have found' : t.blockStates[blockRoot]? = some st := maps.symm ▸ found
        rw [newFound, Option.some.injEq] at found'
        subst st
        exact .inr (.inr ⟨blockRoot, state, pulled, newFound, run, rfl,
          UInt64.lt_of_le_of_lt stateBound later⟩)

private def TimedOrigins (config : Config) (anchor : Checkpoint)
    (s : Store preset fork) : Prop :=
  ∃ slot, s.getCurrentSlot config = .ok slot ∧
    FinalOrigin anchor s (computeEpochAtSlot preset slot) s.finalizedCheckpoint ∧
    ∀ epoch, computeEpochAtSlot preset slot < epoch →
      FinalOrigin anchor s epoch s.unrealizedFinalizedCheckpoint

private theorem TimedOrigins.frame {config : Config} {anchor : Checkpoint}
    {s t : Store preset fork} (h : TimedOrigins config anchor s)
    (clock : Store.SameClock s t) (maps : t.blockStates = s.blockStates)
    (real : t.finalizedCheckpoint = s.finalizedCheckpoint)
    (pending : t.unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint) :
    TimedOrigins config anchor t := by
  obtain ⟨slot, old, r, p⟩ := h
  refine ⟨slot, clock.getCurrentSlot.trans old, ?_, ?_⟩
  · rw [real]
    exact r.mono (fun _ _ found => maps.symm ▸ found) (UInt64.le_refl _)
  · intro epoch later
    rw [pending]
    exact (p epoch later).mono (fun _ _ found => maps.symm ▸ found) (UInt64.le_refl _)

private theorem TimedOrigins.tick {config : Config} {anchor : Checkpoint}
    {s t : Store preset fork} {time : UInt64}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (h : TimedOrigins config anchor s) (forward : s.timeMs ≤ time)
    (ticked : s.onTick config time = .ok t) : TimedOrigins config anchor t := by
  obtain ⟨slot, old, real, pending⟩ := h
  obtain ⟨later, next, le⟩ := Store.exists_getCurrentSlot_onTick_ge forward ticked old
  have ticked' := ticked
  unfold Store.onTick at ticked'
  simp only [bind_ok_iff] at ticked'
  obtain ⟨target, targetOk, caught, catchup, tick⟩ := ticked'
  have eq : target = later := by
    rw [Store.getCurrentSlot_onTick ticked, targetOk, Except.ok.injEq] at next
    exact next
  subst target
  have caughtSlot := catchUp_slot catchup old le
  obtain ⟨real, pending⟩ := realized_catchUp positive catchup old le real pending
  exact ⟨later, next, realized_tick positive tick caughtSlot next
    (UInt64.le_refl _) real pending⟩

private theorem TimedOrigins.block {config : Config} {anchor : Checkpoint}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {s t : Store preset fork} {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock s)
    (h : TimedOrigins config anchor s)
    (added : s.onBlock config checks sources signed = .ok t) : TimedOrigins config anchor t := by
  obtain ⟨slot, old, real, pending⟩ := h
  have kept : ∀ (root : Root) (state : BeaconState preset fork),
      s.blockStates[root]? = some state → t.blockStates[root]? = some state := by
    intro root state found
    rcases Store.onBlock_same_or_insert added with same |
      ⟨newRoot, -, fresh, -, -, post, -, -, states⟩
    · exact same ▸ found
    have other : newRoot ≠ root := by
      rintro rfl
      rw [reachable.blockState_eq_none fresh] at found
      cases found
    rw [states, getElem?_insert_root]
    simpa only [other, ↓reduceIte] using found
  exact ⟨slot, (Store.onBlock_sameClock added).getCurrentSlot.trans old,
    realized_block old kept real pending added⟩

private theorem TimedOrigins.attestation {config : Config} {anchor : Checkpoint}
    {s t : Store preset fork} {checks : SignatureChecks}
    {attestation : Attestation preset fork} {fromBlock : Bool}
    (h : TimedOrigins config anchor s)
    (attested : s.onAttestation config checks attestation fromBlock = .ok t) :
    TimedOrigins config anchor t := by
  have clock := Store.onAttestation_sameClock attested
  have maps := (Store.onAttestation_frame attested).2.2.1
  apply h.frame clock maps
  all_goals
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
    have fields : stored.finalizedCheckpoint = s.finalizedCheckpoint ∧
        stored.unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · cases storing
        exact ⟨rfl, rfl⟩
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
        obtain ⟨_, _, rfl⟩ := storing
        exact ⟨rfl, rfl⟩
    split at attested
    · cases attested
      first | exact fields.1 | exact fields.2
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

private theorem TimedOrigins.slashing {config : Config} {anchor : Checkpoint}
    {s t : Store preset fork} {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} (h : TimedOrigins config anchor s)
    (slashed : s.onAttesterSlashing config checks slashing = .ok t) :
    TimedOrigins config anchor t := by
  unfold Store.onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, rfl⟩ := slashed
  exact h.frame ⟨rfl, rfl⟩ rfl rfl rfl

private theorem forward_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchor s : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (duration : 0 < config.SLOT_DURATION_MS)
    (forward : Store.ForwardReachable config anchorState anchorBlock s) :
    TimedOrigins config anchor.finalizedCheckpoint s := by
  induction forward with
  | anchor made =>
    rw [anchored, Except.ok.injEq] at made
    rw [← made]
    obtain ⟨root, -, -, -, -, final, -, unrealized⟩ := getForkchoiceStore_anchor anchored
    exact ⟨anchorState.slot, getCurrentSlot_getForkchoiceStore duration anchored,
      .inl rfl, fun _ _ => .inl (unrealized.trans final.symm)⟩
  | tick _ later ticked ih => exact ih.tick positive later ticked
  | block reached added ih => exact ih.block reached.reachable added
  | attestation _ attested ih => exact ih.attestation attested
  | attesterSlashing _ slashed ih => exact ih.slashing slashed
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih.frame ⟨rfl, rfl⟩ rfl rfl rfl
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih.frame ⟨rfl, rfl⟩ rfl rfl rfl
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
    exact ih.frame ⟨rfl, rfl⟩ rfl rfl rfl

namespace Models.Network

/-- A realized finalized checkpoint comes from the anchor or a sufficiently early held state.

Pulling up a state requires its epoch to be strictly before the store epoch. -/
theorem Execution.exists_origin_of_finalized
    {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {k : ℕ} {epoch : Epoch}
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch) :
    ((e.world k).state w).finalizedCheckpoint = anchor.finalizedCheckpoint ∨
      (∃ (root : Root) (state : BeaconState preset fork),
        ((e.world k).state w).blockStates[root]? = some state ∧
        ((e.world k).state w).finalizedCheckpoint = state.finalizedCheckpoint ∧
        getCurrentEpoch state ≤ epoch) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        ((e.world k).state w).blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        ((e.world k).state w).finalizedCheckpoint = pulled.finalizedCheckpoint ∧
        getCurrentEpoch state < epoch := by
  have _honest := honest
  have forward : ∀ n, Store.ForwardReachable config anchorState anchorBlock
      ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.ForwardReachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.forwardReachable ih
  have read := epochOk
  simp only [Store.getCurrentStoreEpoch, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at read
  obtain ⟨slot, slotOk, rfl⟩ := read
  obtain ⟨current, currentOk, real, -⟩ :=
    forward_origins anchored positive (Store.slotDuration_pos slotOk) (forward k)
  rw [slotOk, Except.ok.injEq] at currentOk
  subst current
  exact real

end Models.Network

end EthLib.Consensus
