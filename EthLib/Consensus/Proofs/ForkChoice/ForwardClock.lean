module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: stores whose clock never goes back

A tick of the fork choice sets the time of the store, even to an earlier time.

The clock of an honest node only moves forward, so its ticks never go back.

A store is reachable with a forward clock when the handlers build it and no tick sets it back.

Such a store is reachable, so every result on reachable stores applies to it.

A tick to a time no earlier than that of the store does not lower its current slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

namespace Store

/-- A store that the handlers build from an anchor, where no tick sets the time back.

It has one case for each case of a reachable store, and only its tick asks more. -/
inductive ForwardReachable (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) : Store preset fork → Prop where
  /-- The store built from the anchor. -/
  | anchor {store : Store preset fork} :
    getForkchoiceStore config anchorState anchorBlock = .ok store →
      ForwardReachable config anchorState anchorBlock store
  /-- The store after a tick to a time no earlier than its own. -/
  | tick {store after : Store preset fork} {timeMs : UInt64} :
    ForwardReachable config anchorState anchorBlock store → store.timeMs ≤ timeMs →
      store.onTick config timeMs = .ok after → ForwardReachable config anchorState anchorBlock after
  /-- The store after a signed block. -/
  | block {store after : Store preset fork} {checks : SignatureChecks}
      {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork} :
    ForwardReachable config anchorState anchorBlock store →
      store.onBlock config checks sources signed = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- The store after an attestation, from the wire or from a block. -/
  | attestation {store after : Store preset fork} {checks : SignatureChecks}
      {attestation : Attestation preset fork} {isFromBlock : Bool} :
    ForwardReachable config anchorState anchorBlock store →
      store.onAttestation config checks attestation isFromBlock = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- The store after an attester slashing. -/
  | attesterSlashing {store after : Store preset fork} {checks : SignatureChecks}
      {slashing : AttesterSlashing preset fork} :
    ForwardReachable config anchorState anchorBlock store →
      store.onAttesterSlashing config checks slashing = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- From Gloas, the store after a vote of a member of the payload committee. -/
  | payloadAttestation {store after : Store preset fork} {checks : SignatureChecks}
      {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool} :
    ForwardReachable config anchorState anchorBlock store →
      store.onPayloadAttestationMessage config checks gloas message isFromBlock = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- From Gloas, the store after a signed envelope. -/
  | envelope {store after : Store preset fork} {checks : SignatureChecks}
      {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
      {signed : SignedExecutionPayloadEnvelope preset fork} :
    ForwardReachable config anchorState anchorBlock store →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- From Heze, the store after an inclusion list. -/
  | inclusionList {store after : Store preset fork} {checks : SignatureChecks}
      {heze : .hegota ≤ fork} {signed : SignedInclusionList} :
    ForwardReachable config anchorState anchorBlock store →
      store.onInclusionList config checks heze signed = .ok after →
      ForwardReachable config anchorState anchorBlock after

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store after : Store preset fork}

/-- A store with a forward clock is reachable. -/
theorem ForwardReachable.reachable
    (forward : ForwardReachable config anchorState anchorBlock store) :
    Reachable config anchorState anchorBlock store := by
  induction forward with
  | anchor made => exact .anchor made
  | tick _ _ ticked holds => exact holds.tick ticked
  | block _ added holds => exact holds.block added
  | attestation _ attested holds => exact holds.attestation attested
  | attesterSlashing _ slashed holds => exact holds.attesterSlashing slashed
  | payloadAttestation _ voted holds => exact holds.payloadAttestation voted
  | envelope _ accepted holds => exact holds.envelope accepted
  | inclusionList _ accepted holds => exact holds.inclusionList accepted

/-- A block with the votes that it carries keeps a store reachable with a forward clock. -/
theorem ForwardReachable.onBlockWithVotes {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (added : store.onBlockWithVotes config checks sources signed = .ok after) :
    ForwardReachable config anchorState anchorBlock after :=
  onBlockWithVotes_preserves (fun reached step => reached.block step)
    (fun _ reached step => reached.attestation step)
    (fun _ reached step => reached.attesterSlashing step) forward added

/-- A tick to a time no earlier than that of the store does not lower its current slot. -/
theorem getCurrentSlot_le_of_onTick {timeMs : UInt64} {slot later : Slot}
    (forward : store.timeMs ≤ timeMs) (ticked : store.onTick config timeMs = .ok after)
    (current : store.getCurrentSlot config = .ok slot)
    (next : after.getCurrentSlot config = .ok later) : slot ≤ later := by
  rw [getCurrentSlot_onTick ticked] at next
  unfold Store.getCurrentSlot at current
  exact computeSlotAtTimeMs_mono forward (mapError_ok_iff.mp current) (mapError_ok_iff.mp next)

/-- A tick to a time no earlier than that of the store keeps the current slot defined.

It does not lower that slot. -/
theorem exists_getCurrentSlot_onTick_ge {timeMs : UInt64} {current : Slot}
    (forward : store.timeMs ≤ timeMs) (ticked : store.onTick config timeMs = .ok after)
    (slotOk : store.getCurrentSlot config = .ok current) :
    ∃ later, after.getCurrentSlot config = .ok later ∧ current ≤ later := by
  have slotAt := ticked
  unfold onTick at slotAt
  simp only [bind_ok_iff] at slotAt
  obtain ⟨tickSlot, tickOk, -⟩ := slotAt
  refine ⟨tickSlot, ?_, ?_⟩
  · rw [getCurrentSlot_onTick ticked, tickOk]
  · exact getCurrentSlot_le_of_onTick forward ticked slotOk
      (by rw [getCurrentSlot_onTick ticked, tickOk])

/-- The clock of a forward-reachable store bounds every block and block-state slot. -/
theorem ForwardReachable.slots_le_current
    (forward : ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot) :
    ∃ current, store.getCurrentSlot config = .ok current ∧
      (∀ (root : Root) (block : BeaconBlock preset fork),
        store.blocks[root]? = some block → block.slot ≤ current) ∧
      (∀ (root : Root) (state : BeaconState preset fork),
        store.blockStates[root]? = some state → state.slot ≤ current) := by
  have transport {before after : Store preset fork}
      (clock : SameClock before after) (blocks : after.blocks = before.blocks)
      (states : after.blockStates = before.blockStates)
      (holds : ∃ current, before.getCurrentSlot config = .ok current ∧
        (∀ (root : Root) (block : BeaconBlock preset fork),
          before.blocks[root]? = some block → block.slot ≤ current) ∧
        (∀ (root : Root) (state : BeaconState preset fork),
          before.blockStates[root]? = some state → state.slot ≤ current)) :
      ∃ current, after.getCurrentSlot config = .ok current ∧
        (∀ (root : Root) (block : BeaconBlock preset fork),
          after.blocks[root]? = some block → block.slot ≤ current) ∧
        (∀ (root : Root) (state : BeaconState preset fork),
          after.blockStates[root]? = some state → state.slot ≤ current) := by
    simpa only [clock.getCurrentSlot, blocks, states] using holds
  induction forward with
  | anchor made =>
    obtain ⟨root, -, blocks, states⟩ := getForkchoiceStore_maps made
    refine ⟨anchorState.slot, getCurrentSlot_getForkchoiceStore positive made, ?_, ?_⟩
    · intro r b found
      rw [blocks, getElem?_insert_root] at found
      split at found
      · cases Option.some.inj found
        exact anchorSlot
      · simp at found
    · intro r s found
      rw [states, getElem?_insert_root] at found
      split at found
      · cases Option.some.inj found
        exact UInt64.le_refl _
      · simp at found
  | tick _ forward ticked holds =>
    obtain ⟨current, currentOk, blocks, states⟩ := holds
    obtain ⟨later, laterOk, le⟩ := exists_getCurrentSlot_onTick_ge forward ticked currentOk
    obtain ⟨-, -, keptBlocks, keptStates⟩ := onTick_frame ticked
    refine ⟨later, laterOk, ?_, ?_⟩
    · intro r b found
      exact UInt64.le_trans (blocks r b (keptBlocks ▸ found)) le
    · intro r s found
      exact UInt64.le_trans (states r s (keptStates ▸ found)) le
  | @block before after checks sources signed _ added holds =>
    rcases onBlock_same_or_insert added with
      same | ⟨root, hashed, absent, blocks, pre, state, -, transitioned, states⟩
    · exact same ▸ holds
    obtain ⟨current, currentOk, blockBound, stateBound⟩ := holds
    have new : ¬ before.blocks.contains root := by
      simp [Std.TreeMap.contains_eq_isSome_getElem?, absent]
    obtain ⟨⟨checked, checkedOk, bound⟩, -⟩ := onBlock_checks hashed new added
    rw [currentOk, Except.ok.injEq] at checkedOk
    subst checked
    refine ⟨current, (onBlock_sameClock added).getCurrentSlot.trans currentOk, ?_, ?_⟩
    · intro r b found
      rw [blocks, getElem?_insert_root] at found
      split at found
      · cases Option.some.inj found
        exact bound
      · exact blockBound r b found
    · intro r s found
      rw [states, getElem?_insert_root] at found
      split at found
      · cases Option.some.inj found
        rw [(stateTransition_slot transitioned).2]
        exact bound
      · exact stateBound r s found
  | attestation _ step holds =>
    exact transport (onAttestation_sameClock step) (onAttestation_frame step).2.1
      (onAttestation_frame step).2.2 holds
  | attesterSlashing _ step holds =>
    exact transport (onAttesterSlashing_sameClock step) (onAttesterSlashing_frame step).2.1
      (onAttesterSlashing_frame step).2.2 holds
  | payloadAttestation _ step holds =>
    exact transport (onPayloadAttestationMessage_sameClock step)
      (onPayloadAttestationMessage_onlyPtcVotes step).frame.2.1
      (onPayloadAttestationMessage_onlyPtcVotes step).frame.2.2 holds
  | envelope _ step holds =>
    exact transport (onExecutionPayloadEnvelope_sameClock step)
      (onExecutionPayloadEnvelope_frame step).2.1
      (onExecutionPayloadEnvelope_frame step).2.2 holds
  | inclusionList _ step holds =>
    exact transport (onInclusionList_sameClock step) (onInclusionList_frame step).2.1
      (onInclusionList_frame step).2.2 holds

/-- Raw block states do not run ahead of a forward store's clock.

This bound does not require the anchor block's slot to match its state. -/
theorem ForwardReachable.blockState_slots_le_current
    {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < config.SLOT_DURATION_MS) :
    ∃ current, store.getCurrentSlot config = .ok current ∧
      ∀ (root : Root) (state : BeaconState preset fork),
        store.blockStates[root]? = some state → state.slot ≤ current := by
  have transport {before after : Store preset fork}
      (clock : Store.SameClock before after) (states : after.blockStates = before.blockStates)
      (holds : ∃ current, before.getCurrentSlot config = .ok current ∧
        ∀ (root : Root) (state : BeaconState preset fork),
          before.blockStates[root]? = some state → state.slot ≤ current) :
      ∃ current, after.getCurrentSlot config = .ok current ∧
        ∀ (root : Root) (state : BeaconState preset fork),
          after.blockStates[root]? = some state → state.slot ≤ current := by
    simpa only [clock.getCurrentSlot, states] using holds
  induction forward with
  | anchor made =>
    obtain ⟨root, _, _, states⟩ := getForkchoiceStore_maps made
    refine ⟨anchorState.slot, getCurrentSlot_getForkchoiceStore positive made, ?_⟩
    intro r s found
    rw [states, getElem?_insert_root] at found
    split at found
    · cases Option.some.inj found
      exact UInt64.le_refl _
    · simp at found
  | tick _ forward ticked holds =>
    obtain ⟨current, currentOk, states⟩ := holds
    obtain ⟨later, laterOk, le⟩ :=
      Store.exists_getCurrentSlot_onTick_ge forward ticked currentOk
    obtain ⟨_, _, _, keptStates⟩ := Store.onTick_frame ticked
    exact ⟨later, laterOk, fun r s found =>
      UInt64.le_trans (states r s (keptStates ▸ found)) le⟩
  | @block before after checks sources signed _ added holds =>
    rcases Store.onBlock_same_or_insert added with
      same | ⟨root, hashed, absent, _, pre, state, _, transitioned, states⟩
    · exact same ▸ holds
    obtain ⟨current, currentOk, stateBound⟩ := holds
    have fresh : ¬ before.blocks.contains root := by
      simp [Std.TreeMap.contains_eq_isSome_getElem?, absent]
    obtain ⟨⟨checked, checkedOk, bound⟩, _⟩ := Store.onBlock_checks hashed fresh added
    rw [currentOk, Except.ok.injEq] at checkedOk
    subst checked
    refine ⟨current, (Store.onBlock_sameClock added).getCurrentSlot.trans currentOk, ?_⟩
    intro r s found
    rw [states, getElem?_insert_root] at found
    split at found
    · cases Option.some.inj found
      rw [(stateTransition_slot transitioned).2]
      exact bound
    · exact stateBound r s found
  | attestation _ step holds =>
    exact transport (Store.onAttestation_sameClock step) (Store.onAttestation_frame step).2.2 holds
  | attesterSlashing _ step holds =>
    exact transport (Store.onAttesterSlashing_sameClock step)
      (Store.onAttesterSlashing_frame step).2.2 holds
  | payloadAttestation _ step holds =>
    exact transport (Store.onPayloadAttestationMessage_sameClock step)
      (Store.onPayloadAttestationMessage_onlyPtcVotes step).frame.2.2 holds
  | envelope _ step holds =>
    exact transport (Store.onExecutionPayloadEnvelope_sameClock step)
      (Store.onExecutionPayloadEnvelope_frame step).2.2 holds
  | inclusionList _ step holds =>
    exact transport (Store.onInclusionList_sameClock step)
      (Store.onInclusionList_frame step).2.2 holds

/-- The current epoch's committee prefix retains its seed in every held raw block state. -/
theorem ForwardReachable.retained_current_epoch
    {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {current first : Slot} (slotOk : store.getCurrentSlot config = .ok current)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset current) = .ok first)
    {root : Root} {state : BeaconState preset fork}
    (found : store.blockState root = .ok state) :
    (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      (computeEpochAtSlot preset first).toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
  obtain ⟨now, nowOk, states⟩ :=
    forward.blockState_slots_le_current (Store.slotDuration_pos slotOk)
  have same := Except.ok.inj (nowOk.symm.trans slotOk)
  subst now
  have bound := UInt64.le_iff_toNat_le.mp (states root state (Store.blockState_ok_iff.mp found))
  have epochBound := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) bound
  by_cases positive : 0 < preset.SLOTS_PER_EPOCH
  · have firstEpoch := computeEpochAtSlot_computeStartSlotAtEpoch positive firstOk
    rw [firstEpoch]
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at epochBound ⊢
    omega
  · have zero : preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp positive)
      simp only [UInt64.toNat_zero] at this
      omega
    simpa [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div, zero] using retained

end Store

end EthLib.Consensus
