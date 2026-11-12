module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Attestations

/-! Empty-slot states used to form the witness's three honest votes. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness

open Base Serialization.Ssz

/-- The first empty slot records the child roots and fills its header's state root. -/
def secondState : BeaconState preset .phase0 :=
  { postState with
    slot := 2
    stateRoots := postState.stateRoots.set 1 postRoot (by decide)
    blockRoots := postState.blockRoots.set 1 blockRoot (by decide)
    latestBlockHeader := { postState.latestBlockHeader with stateRoot := postRoot } }

/-- The next empty slot records an arbitrary root supplied by SSZ totality. -/
def thirdState (root : Root) : BeaconState preset .phase0 :=
  { secondState with
    slot := 3
    stateRoots := secondState.stateRoots.set 2 root (by decide)
    blockRoots := secondState.blockRoots.set 2 blockRoot (by decide) }

/-- Filling the child's header recovers the certified block root. -/
theorem child_header_root :
    SszType.hashTreeRoot { postState.latestBlockHeader with stateRoot := postRoot } =
      .ok blockRoot :=
  (BeaconBlock.hashTreeRoot_header (block := signedBlock.message) body_root).trans first_block_root

set_option maxRecDepth 10000 in
/-- Neither empty slot crosses an epoch boundary, so vote sources and targets stay at genesis. -/
theorem exists_vote_state {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    ∃ current, lookaheadState config .acceptAll postState slot = .ok current ∧
      getAttestationData current blockRoot 1 0 .pending = .ok (voteData slot) := by
  have first : advanceSlot config .acceptAll postState = .ok secondState := by
    simp only [advanceSlot, epochIfLast, processSlot, post_root,
      show postState.latestBlockHeader.stateRoot = Vector.replicate 32 0 from rfl,
      ↓reduceIte, child_header_root, liftSsz, liftAccessor, Except.mapError, bind, Except.bind,
      pure, Except.pure]
    rfl
  rcases within with rfl | rfl | rfl
  · exact ⟨postState, rfl, rfl⟩
  · refine ⟨secondState, ?_, rfl⟩
    change (advanceSlots config .acceptAll 1 postState).mapError _ = .ok secondState
    rw [advanceSlots, first]
    rfl
  · let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
    let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
    let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
    let : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨by decide⟩
    let : NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := ⟨by decide⟩
    let : NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat := ⟨by decide⟩
    let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :=
      ⟨by decide⟩
    let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
    let : NeZero (2 * preset.SLOTS_PER_EPOCH.toNat) := ⟨by decide⟩
    let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat) :=
      ⟨by decide⟩
    let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
    -- No later comparison reads this state root, so totality replaces another hash certificate.
    obtain ⟨root, rooted⟩ := SszType.hashTreeRoot_total secondState
    have second : advanceSlot config .acceptAll secondState = .ok (thirdState root) := by
      simp only [advanceSlot, epochIfLast, processSlot, rooted,
        show secondState.latestBlockHeader.stateRoot = postRoot from rfl,
        postRoot_ne_zero, ↓reduceIte,
        show SszType.hashTreeRoot secondState.latestBlockHeader = .ok blockRoot from
          child_header_root,
        liftSsz, liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure]
      rfl
    refine ⟨thirdState root, ?_, ?_⟩
    · change (advanceSlots config .acceptAll 2 postState).mapError _ = .ok (thirdState root)
      rw [advanceSlots, first]
      change (advanceSlots config .acceptAll 1 secondState).mapError _ = .ok (thirdState root)
      rw [advanceSlots, second]
      rfl
    · -- Vote data reads the block history, not the state-root history.
      change getAttestationData (thirdState default) blockRoot 1 0 .pending = .ok (voteData 3)
      rfl

end EthLib.Consensus.Models.Network.EightValidatorWitness
