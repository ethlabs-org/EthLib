module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints

/-!
# Registry positions at justified checkpoints

Activity at any epoch requires an activation epoch below `FAR_FUTURE_EPOCH`.

This includes committee lookahead beyond the epoch of the head state.

Positions present at the anchor stay in every cached checkpoint registry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}

/-- Phase0 beacon-chain `is_active_validator` excludes the far-future activation sentinel.

The strict exit bound applies even when the queried epoch is beyond the state's epoch. -/
theorem activationEpoch_ne_farFuture_of_isActiveAt
    {state : BeaconState preset fork} {epoch : Epoch} {position : Nat}
    (active : isActiveAt state epoch position = true) :
    ∃ validator, state.validators.data[position]? = some validator ∧
      validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨validator, found, active⟩ := isActiveAt_eq_true_iff.mp active
  refine ⟨validator, found, ?_⟩
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  intro far
  have low := UInt64.le_iff_toNat_le.mp active.1
  have high := UInt64.lt_iff_toNat_lt.mp active.2
  have bounded := validator.exitEpoch.toNat_lt
  have sentinel : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  rw [far, sentinel] at low
  omega

/-- Registry growth along imported parent transitions retains every anchor position.

The store is fixed-fork, so these transitions do not include fork upgrades. -/
theorem Store.Reachable.anchor_registry_le_blockState
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    anchorState.validators.data.size ≤ state.validators.data.size := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · rw [anchored same]
  · obtain ⟨parent, checks, engine, signed, -, parentFound, transitioned⟩ := produced same
    exact Nat.le_trans (reachable.anchor_registry_le_blockState parentFound)
      (runKept_stateTransition transitioned).grows
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

namespace Store

/-- Fork-choice `update_checkpoints` includes the supplied finalized epoch in its maximum. -/
private theorem finalized_le_updateCheckpoints (store : Store preset fork)
    (justified finalized : Checkpoint) :
    finalized.epoch ≤ (store.updateCheckpoints justified finalized).finalizedCheckpoint.epoch := by
  unfold updateCheckpoints
  split <;> dsimp only <;> split
  all_goals first | exact UInt64.le_refl _ | exact UInt64.not_lt.mp ‹_›

/-- The realized finality of an imported state is bounded by the resulting store's finality.

Fork-choice `on_block` updates realized checkpoints before pulling up the tip. -/
private theorem addBlock_finalized_states
    {store after : Store preset fork} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {root : Root}
    (holds : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      s.finalizedCheckpoint.epoch ≤ store.finalizedCheckpoint.epoch)
    (added : store.addBlock config checks sources signed root = .ok after) :
    ∀ (r : Root) (s : BeaconState preset fork), after.blockStates[r]? = some s →
      s.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  have forward := (addBlock_ok added).1.2
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨-, -, bs0⟩ := (recordBlockPtcVotes_onlyPtcVotes vote).frame
  obtain ⟨-, -, bs1, -⟩ := recordBlockTimeliness_frame record
  obtain ⟨-, -, bs2, -⟩ := updateProposerBoostRoot_frame boost
  obtain ⟨later, -, bs3, -⟩ := computePulledUpTip_frame added
  intro r s found
  rw [bs3, updateCheckpoints_blockStates, bs2, bs1, bs0,
    Std.TreeMap.getElem?_insert] at found
  split at found
  · cases found
    exact UInt64.le_trans (finalized_le_updateCheckpoints boosted _ _) later.2
  · exact UInt64.le_trans (holds _ _ found) forward

/-- Every held block state has finality at most the store's realized finality.

At the anchor the store starts finalized at the anchor epoch.

Each block import includes its post-state finality, and every handler preserves the bound. -/
theorem Reachable.blockState_finalized_le {store : Store preset fork}
    (reachable : Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    state.finalizedCheckpoint.epoch ≤ store.finalizedCheckpoint.epoch := by
  have all : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      s.finalizedCheckpoint.epoch ≤ store.finalizedCheckpoint.epoch := by
    clear stored state root
    induction reachable with
    | anchor made =>
      obtain ⟨anchorRoot, -, -, states⟩ := getForkchoiceStore_maps made
      obtain ⟨checkpointRoot, _, _, _, _, finalized, _, _⟩ := getForkchoiceStore_anchor made
      intro r s found
      rw [states, getElem?_insert_root] at found
      split at found
      · simp only [Option.some.injEq] at found
        subst s
        rw [finalized]
        exact UInt64.le_trans (finalized_le_currentJustified sound.ordered)
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _))
      · simp at found
    | @block before after checks sources signed _ added ih =>
      unfold onBlock at added
      simp only [bind_ok_iff] at added
      obtain ⟨_, -, added⟩ := added
      split at added
      · cases added
        exact ih
      · exact addBlock_finalized_states ih added
    | tick _ handled ih =>
      obtain ⟨-, le, -, states⟩ := onTick_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | attestation _ handled ih =>
      obtain ⟨le, -, states⟩ := onAttestation_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | attesterSlashing _ handled ih =>
      obtain ⟨le, -, states⟩ := onAttesterSlashing_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | payloadAttestation _ handled ih =>
      obtain ⟨le, -, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes handled).frame
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | envelope _ handled ih =>
      obtain ⟨le, -, states⟩ := onExecutionPayloadEnvelope_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | inclusionList _ handled ih =>
      obtain ⟨le, -, states⟩ := onInclusionList_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
  exact all root state stored

end Store

namespace Models.Network

variable {sources : BlockSources preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Cached checkpoint processing cannot remove a position already present at the anchor. -/
theorem Execution.validatorAt_checkpoint_of_anchor
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (stateOk : ((e.world k).state w).checkpointState checkpoint = .ok state)
    {v : ValidatorIndex} (inside : v.toNat < anchorState.validators.data.size) :
    ∃ validator, state.validators.data[v.toNat]? = some validator := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨base, slot, stored, -, advanced⟩ :=
    e.checkpointStates_fixedChecks anchored (start w honest)
      (Store.checkpointState_ok_iff.mp stateOk)
  have grows := reached.anchor_registry_le_blockState stored
  have later : base.validators.data.size ≤ state.validators.data.size := by
    unfold lookaheadState at advanced
    split at advanced
    · exact (runKept_processSlots (mapError_ok_iff.mp advanced)).grows
    · cases advanced
      exact Nat.le_refl _
  have bound := Nat.lt_of_lt_of_le inside (Nat.le_trans grows later)
  exact ⟨state.validators.data[v.toNat], Array.getElem?_eq_getElem bound⟩

end Models.Network

end EthLib.Consensus
