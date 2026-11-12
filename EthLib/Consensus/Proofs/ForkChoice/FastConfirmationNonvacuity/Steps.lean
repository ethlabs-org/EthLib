module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Stores

/-! Clock steps, fixed vote signers and repeated-message handling in the candidate stores. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz

set_option maxRecDepth 10000 in
/-- The candidate stores use genesis zero and 1000 milliseconds per slot. -/
theorem running_clock (time : UInt64) (count : Nat) :
    (running time count).getCurrentSlot config = .ok (time / 1000) := by
  change (computeSlotAtTimeMs config 0 time).mapError ForkChoiceError.arith = _
  simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
    bind, Except.bind, Except.mapError]

set_option maxRecDepth 10000 in
/-- Ticking within one slot changes only the clock. -/
theorem running_tick_same (first next : UInt64) (count : Nat)
    (same : first / 1000 = next / 1000)
    (boost : (first < 2000) = (next < 2000)) :
    (running first count).onTick config next = .ok (running next count) := by
  have slotted : computeSlotAtTimeMs config (running first count).genesisTimeMs next =
      .ok (next / 1000) := by
    change computeSlotAtTimeMs config 0 next = _
    simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
      bind, Except.bind]
  have step := onTick_sameSlot (running_clock first count) (same ▸ slotted)
  simpa [running, boost] using step

set_option maxRecDepth 10000 in
/-- The first three slot boundaries clear the boost without changing the genesis checkpoints. -/
theorem running_tick_boundary (count : Nat) {slot : Slot}
    (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    (running (slot * 1000 + 999) count).onTick config ((slot + 1) * 1000) =
      .ok (running ((slot + 1) * 1000) count) := by
  have perSlot : (running (slot * 1000 + 999) count).onTickPerSlot config
      ((slot + 1) * 1000) = .ok (running ((slot + 1) * 1000) count) := by
    rcases within with rfl | rfl | rfl <;>
      simp [Store.onTickPerSlot, Store.getCurrentSlot, computeSlotAtTimeMs,
        Uint64.subChecked, Uint64.divChecked, running, config,
        bind, Except.bind, Except.mapError] <;> rfl
  have afterSlot : (running ((slot + 1) * 1000) count).getCurrentSlot config =
      .ok (slot + 1) := by
    rw [running_clock]
    rcases within with rfl | rfl | rfl <;> rfl
  have catchup : Store.catchUp config (running (slot * 1000 + 999) count) (slot + 1) =
      .ok (running ((slot + 1) * 1000) count) := by
    rw [Store.catchUp, running_clock]
    have clock : (slot * 1000 + 999) / 1000 = slot := by
      rcases within with rfl | rfl | rfl <;> rfl
    rw [clock]
    have next : Uint64.addChecked slot 1 = .ok (slot + 1) := by
      rcases within with rfl | rfl | rfl <;> rfl
    have time : computeTimeAtSlotMs config 0 (slot + 1) = .ok ((slot + 1) * 1000) := by
      rcases within with rfl | rfl | rfl <;> rfl
    simp only [bind, Except.bind, show slot < slot + 1 by
      rcases within with rfl | rfl | rfl <;> decide, ↓reduceIte, next, Except.mapError,
      show (running (slot * 1000 + 999) count).genesisTimeMs = 0 from rfl, time, perSlot]
    have closer : (running ((slot + 1) * 1000) count).slotsBefore config (slot + 1) <
        (running (slot * 1000 + 999) count).slotsBefore config (slot + 1) := by
      simp only [Store.slotsBefore, afterSlot, running_clock, clock]
      rcases within with rfl | rfl | rfl <;> decide
    simp only [closer, ↓reduceDIte]
    rw [Store.catchUp, afterSlot]
    simp [bind, Except.bind, pure, Except.pure]
  have time : computeSlotAtTimeMs config 0 ((slot + 1) * 1000) = .ok (slot + 1) := by
    rcases within with rfl | rfl | rfl <;>
      simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
        bind, Except.bind]
  simp only [Store.onTick,
    show (running (slot * 1000 + 999) count).genesisTimeMs = 0 from rfl,
    time, Except.mapError, bind, Except.bind, catchup]
  -- The final per-slot tick is already at the boundary reached by catch-up.
  rcases within with rfl | rfl | rfl <;>
    simp [Store.onTickPerSlot, Store.getCurrentSlot, computeSlotAtTimeMs,
      Uint64.subChecked, Uint64.divChecked, running, config,
      bind, Except.bind, Except.mapError] <;> rfl

set_option maxRecDepth 10000 in
/-- Every reachable reading of a candidate vote names only its intended signer and data. -/
theorem running_vote_statements {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3)
    {x : ValidatorIndex × AttestationData}
    (member : x ∈ statements config .acceptAll (state bodyRoot) (anchorBlock stateRoot)
      (.attestation (vote slot))) : x = (voter slot, voteData slot) := by
  have initial : anchor.checkpointStates[(vote slot).data.target]? = some (state bodyRoot) := by
    simp [anchor, vote, voteData]
  have indexed := mem_indexedStatements_of_cached_target initialized initial
    (vote_indexed within) member
  simpa [indexedStatements, indexedVote, Prod.ext_iff] using indexed

set_option maxRecDepth 10000 in
/-- Reprocessing the already held empty block changes nothing. -/
theorem running_block_repeat (time : UInt64) (count : Nat) :
    (running time count).onBlockWithVotes config .acceptAll sources signedBlock =
      .ok (running time count) := by
  have present : (running time count).blocks.contains blockRoot := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, running_child]
    rfl
  have block : (running time count).onBlock config .acceptAll sources signedBlock =
      .ok (running time count) := by
    simp only [Store.onBlock, first_block_root, Except.mapError, bind, Except.bind,
      present, ↓reduceIte, pure, Except.pure]
  simp only [Store.onBlockWithVotes, block, bind, Except.bind]
  rfl

set_option maxRecDepth 10000 in
/-- A recorded vote cannot replace itself at the same target epoch. -/
theorem running_update_repeat (time : UInt64) {count : Nat} (bound : count ≤ 3)
    {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) (already : slot.toNat ≤ count) :
    (running time count).updateLatestMessages [voter slot] (vote slot) = running time count := by
  have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by omega
  rcases within with rfl | rfl | rfl <;>
    rcases cases with rfl | rfl | rfl | rfl <;>
    simp_all [Store.updateLatestMessages, running, recordVote, voter, LatestMessage.ofAttestation,
      vote, voteData, admitted, ticked, anchor, Std.TreeMap.getElem_insert]

set_option maxRecDepth 10000 in
/-- Accepting a recorded vote again changes no field of the store. -/
theorem running_vote_repeat (time : UInt64) {count : Nat} (bound : count ≤ 3)
    {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) (already : slot.toNat ≤ count)
    {after : Store preset .phase0}
    (step : (running time count).onAttestation config .acceptAll (vote slot) false = .ok after) :
    after = running time count := by
  have cached : (running time count).storeTargetCheckpointState config .acceptAll
      (vote slot).data.target = .ok (running time count) := by
    simp [Store.storeTargetCheckpointState, running, admitted, ticked, anchor,
      vote, voteData, Checkpoint.compare, pure, Except.pure]
  have target : (running time count).checkpointState (vote slot).data.target =
      .ok (state bodyRoot) := by
    simp [Store.checkpointState, running, admitted, ticked, anchor, vote, voteData,
      pure, Except.pure]
  simp only [Store.onAttestation, bind_ok_iff] at step
  obtain ⟨_, _, step⟩ := step
  simp [cached, target, vote_committees within, vote_indexed within,
    vote_signature within, Except.mapError, pure, Except.pure] at step
  change (running time count).updateLatestMessages [voter slot] (vote slot) = after at step
  exact step.symm.trans (running_update_repeat time bound within already)

end EthLib.Consensus.Models.Network.FiveValidatorWitness
