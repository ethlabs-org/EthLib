module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EthLib.Consensus.Proofs.Containers.Misc
import EthLib.Consensus.Proofs.Transition.BlockRoots
import EthLib.Consensus.Proofs.Transition.TargetUpgrades
import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Hash evidence restricted to the supplied executions

Collision evidence uses only the selected block headers, not full beacon-state commitments.

States are included only for the zero-root alternative.

A zero state root leaves processSlot's empty-root sentinel unset.

A later slot can then refill it.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

inductive HashObject (preset : Preset) where
  | header (value : BeaconBlockHeader)
  | state (value : ForkedBeaconState preset)

def HashObject.root (object : HashObject preset) : Option Root :=
  match object with
  | .header h => (hashTreeRoot h).toOption
  | .state s => (hashTreeRoot s.state).toOption

def HashObject.messages (object : HashObject preset) : List Bytes :=
  match object with
  | .header h => ((valueTree (SszType.desc BeaconBlockHeader) (SszType.toValue h)).toOption.map
      (fun tree => tree.messages)).getD []
  | .state _ => []

def _root_.EthLib.Consensus.Step.hashObjects {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List (HashObject preset) :=
  [.state before, .state after, .header before.state.latestBlockHeader,
    .header after.state.latestBlockHeader] ++
  (match step with
  | .slot _ => match (processSlot before.state).toOption with
    | none => []
    | some cached => [.state ⟨before.fork, cached⟩, .header cached.latestBlockHeader]
  | .block _ signed _ _ => ((blockHeader signed.message).toList.map HashObject.header))

def _root_.EthLib.Consensus.Run.hashObjects {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List (HashObject preset) :=
  match run with
  | .nil => [.state first, .header first.state.latestBlockHeader]
  | .snoc pre step => pre.hashObjects ++ step.hashObjects

def HashEvidence (objects : List (HashObject preset)) : Prop :=
  (∃ x ∈ objects.flatMap HashObject.messages, ∃ y ∈ objects.flatMap HashObject.messages,
    MessageCollision x y) ∨
  ∃ object ∈ objects, object.root = some (Vector.replicate 32 0)

theorem header_binding (objects : List (HashObject preset)) (a b : BeaconBlockHeader)
    (one : .header a ∈ objects) (two : .header b ∈ objects) (root : Root)
    (sameA : hashTreeRoot a = .ok root) (sameB : hashTreeRoot b = .ok root) :
    a = b ∨ HashEvidence objects := by
  have sized (h : BeaconBlockHeader) :
      CommitmentSized (SszType.desc BeaconBlockHeader) (SszType.toValue h) := by
    refine .container fun pair member => ?_
    simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
    repeat' rcases member with rfl | member
    all_goals first | exact .byteVector _ _ | exact .uint _ _
  rcases SszType.hashTreeRoot_binding (sized a) (sized b) sameA sameB with same | collision
  · exact .inl same
  · obtain ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, leftMem, rightMem, collided⟩ :=
      collision
    right
    left
    refine ⟨x, List.mem_flatMap.mpr ⟨.header a, one, ?_⟩,
      y, List.mem_flatMap.mpr ⟨.header b, two, ?_⟩, collided⟩
    · simpa [HashObject.messages, leftOk, Except.toOption] using leftMem
    · simpa [HashObject.messages, rightOk, Except.toOption] using rightMem

private theorem block_slot {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (ok : applySignedBlock config checks engine before signed true = .ok after) :
    signed.message.slot = before.slot := by
  have processed := (applySignedBlock_ok ok).2.1
  by_cases gloas : .glamsterdam ≤ fork
  · obtain ⟨parented, headed, _, _, _, parentOk, headerOk, _⟩ :=
      processBlock_steps gloas processed
    exact (processBlockHeader_checks headerOk).1.trans
      (payloadInputs_processParentExecutionPayload parentOk).slot
  · obtain ⟨headed, headerOk⟩ := processBlock_header_of_lt_gloas
      (Nat.lt_of_not_le gloas) processed
    exact (processBlockHeader_checks headerOk).1

private theorem slot_header {fork : Fork} {before after : BeaconState preset fork}
    (ok : processSlot before = .ok after) :
    ∃ root, hashTreeRoot before = .ok root ∧
      after.latestBlockHeader =
        (if before.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
          { before.latestBlockHeader with stateRoot := root } else before.latestBlockHeader) := by
  unfold processSlot at ok
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at ok
  obtain ⟨root, hashed, _, _, _, _, _, _, ok⟩ := ok
  refine ⟨root, hashed, ?_⟩
  split at ok
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp ok)
    rfl
  · cases ok
    rfl

private theorem slot_across_roots {before after : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks before = .ok after) :
    ∃ cached, processSlot before.state = .ok cached ∧
      after.state.blockRoots = cached.blockRoots ∧
      after.state.slot.toNat = before.state.slot.toNat + 1 := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  obtain ⟨cached, cachedOk, _, roots, _, _, _, slot⟩ := advanceSlot_cachedRoots advancedOk
  exact ⟨cached, cachedOk, (processUpgrades_blockRoots upgraded).trans roots,
    (congrArg UInt64.toNat (processUpgrades_slot upgraded)).trans slot⟩

private theorem slot_root_origin {before after : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks before = .ok after) {slot : Slot} {root : Root}
    (read : getBlockRootAtSlot after.state slot = .ok root) :
    getBlockRootAtSlot before.state slot = .ok root ∨
      ∃ cached, processSlot before.state = .ok cached ∧
        hashTreeRoot cached.latestBlockHeader = .ok root := by
  obtain ⟨cached, cachedOk, roots, advanced⟩ := slot_across_roots ok
  obtain ⟨lt, fits, recent, read⟩ := getBlockRootAtSlot_ok_iff.mp read
  obtain ⟨writtenRoot, hashed, written⟩ := processSlot_blockRoots cachedOk
  rw [roots] at read
  by_cases same : slot = before.state.slot
  · subst slot
    rw [readCircular_writeCircular written] at read
    cases read
    exact .inr ⟨cached, cachedOk, hashed⟩
  · left
    have earlier : slot.toNat < before.state.slot.toNat := by
      have different : slot.toNat ≠ before.state.slot.toNat :=
        fun eq => same (UInt64.toNat_inj.mp eq)
      omega
    have other : before.state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
        slot % preset.SLOTS_PER_HISTORICAL_ROOT := by
      intro eq
      have eq := congrArg UInt64.toNat eq
      rw [UInt64.toNat_mod, UInt64.toNat_mod] at eq
      exact Nat.mod_ne_of_sub_lt earlier (by omega) eq
    rw [readCircular_writeCircular_of_ne written other] at read
    exact getBlockRootAtSlot_ok_iff.mpr ⟨earlier, fits, by omega, read⟩

private theorem run_root_observed {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    {slot : Slot} {root : Root} (read : getBlockRootAtSlot a.state slot = .ok root) :
    ∃ header : BeaconBlockHeader,
      .header header ∈ run.hashObjects ∧ hashTreeRoot header = .ok root := by
  induction run with
  | nil =>
    obtain ⟨hash, time, deposits, initialized⟩ := genesis
    have zero := (initializeBeaconStateFromEth1_checkpoints initialized).1
    have before := (getBlockRootAtSlot_ok_iff.mp read).1
    rw [zero] at before
    simp [GENESIS_SLOT] at before
  | snoc pre step ih =>
    cases step with
    | slot ok =>
      rcases slot_root_origin ok read with earlier | ⟨cached, cachedOk, hashed⟩
      · obtain ⟨header, member, hashed⟩ := ih earlier
        exact ⟨header, List.mem_append_left _ member, hashed⟩
      · refine ⟨cached.latestBlockHeader, List.mem_append_right _ ?_, hashed⟩
        simp [Step.hashObjects, cachedOk, Except.toOption]
    | block engine signed due ok =>
      rename_i fork before after
      have frame := frame_processBlock (applySignedBlock_ok ok).2.1
      have roots := processBlock_blockRoots (applySignedBlock_ok ok).2.1
      have earlier : getBlockRootAtSlot before slot = .ok root := by
        simpa only [getBlockRootAtSlot_congr frame.slot roots] using read
      obtain ⟨header, member, hashed⟩ := ih earlier
      exact ⟨header, List.mem_append_left _ member, hashed⟩

private theorem step_slots {before after : ForkedBeaconState preset}
    (step : Step config checks before after) :
    before.state.slot.toNat ≤ after.state.slot.toNat ∧
      ∀ header ∈ step.headers, header.slot = before.state.slot := by
  cases step with
  | slot ok =>
    obtain ⟨_, _, _, advanced⟩ := slot_across_roots ok
    exact ⟨by omega, by simp [Step.headers]⟩
  | block engine signed due ok =>
    have same := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
    refine ⟨by rw [same], ?_⟩
    intro header member
    simp only [Step.headers, Option.mem_toList] at member
    unfold blockHeader at member
    cases body : (hashTreeRoot signed.message.body).toOption <;>
      simp [body] at member
    subst header
    exact block_slot ok

private theorem run_slots {a b : ForkedBeaconState preset} (run : Run config checks a b) :
    a.state.slot.toNat ≤ b.state.slot.toNat := by
  induction run with
  | nil => exact Nat.le_refl _
  | snoc _ edge ih => exact ih.trans (step_slots edge).1

theorem path_append_stable {g a b : ForkedBeaconState preset}
    (pre : Run config checks g a) (tail : Run config checks a b) (epoch : Epoch)
    (before : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < a.state.slot.toNat) :
    (pre.append tail).checkpointPath epoch = pre.checkpointPath epoch := by
  induction tail with
  | nil => rfl
  | @snoc middle last tail step ih =>
    have empty : step.headers.filter
        (fun h => h.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h member
      have same := (step_slots step).2 h member
      have bound := run_slots tail
      simp only [same, decide_eq_true_eq]
      omega
    simpa only [Run.append, Run.checkpointPath, Run.headers, List.filter_append, empty,
      List.append_nil] using ih

/-- Equal checkpoint roots identify equal header prefixes, or the scan finds hash evidence. -/
theorem checkpoint_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (epoch : Epoch) (root : Root)
    (one : getBlockRoot a.state epoch = .ok root)
    (two : getBlockRoot b.state epoch = .ok root) :
    left.checkpointPath epoch = right.checkpointPath epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  sorry

private theorem hashObjects_append_subset {g a b : ForkedBeaconState preset}
    (pre : Run config checks g a) (tail : Run config checks a b) :
    pre.hashObjects ⊆ (pre.append tail).hashObjects := by
  induction tail with
  | nil => exact fun _ h => h
  | snoc tail step ih => exact fun _ h => List.mem_append_left _ (ih h)

private theorem hashEvidence_mono {one two : List (HashObject preset)}
    (subset : one ⊆ two) (evidence : HashEvidence one) : HashEvidence two := by
  rcases evidence with ⟨x, xm, y, ym, collision⟩ | ⟨object, member, zero⟩
  · left
    have mem {z} (member : z ∈ one.flatMap HashObject.messages) :
        z ∈ two.flatMap HashObject.messages := by
      obtain ⟨object, member, hashed⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨object, subset member, hashed⟩
    exact ⟨x, mem xm, y, mem ym, collision⟩
  · exact .inr ⟨object, subset member, zero⟩

/-- Cached reads before a selected slot bind the full runs at an already passed boundary. -/
theorem checkpoint_binding_cached {g a b before₁ after₁ before₂ after₂ : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (ok₁ : advanceSlotAcross config checks before₁ = .ok after₁)
    (ok₂ : advanceSlotAcross config checks before₂ = .ok after₂)
    (member₁ : left.Contains (.slot ok₁)) (member₂ : right.Contains (.slot ok₂))
    (cached₁ : BeaconState preset before₁.fork) (cached₂ : BeaconState preset before₂.fork)
    (cachedOk₁ : processSlot before₁.state = .ok cached₁)
    (cachedOk₂ : processSlot before₂.state = .ok cached₂)
    (epoch : Epoch) (root : Root)
    (read₁ : getBlockRoot cached₁ epoch = .ok root)
    (read₂ : getBlockRoot cached₂ epoch = .ok root)
    (early₁ : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < before₁.state.slot.toNat)
    (early₂ : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < before₂.state.slot.toNat)
    (recent₁ : before₁.state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (recent₂ : before₂.state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    left.checkpointPath epoch = right.checkpointPath epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  rw [getBlockRoot_processSlot cachedOk₁ recent₁] at read₁
  rw [getBlockRoot_processSlot cachedOk₂ recent₂] at read₂
  obtain ⟨pre₁, post₁, rfl⟩ := left.contains_split (.slot ok₁) member₁
  obtain ⟨pre₂, post₂, rfl⟩ := right.contains_split (.slot ok₂) member₂
  have paths₁ := path_append_stable pre₁ ((Run.nil.snoc (.slot ok₁)).append post₁) epoch early₁
  have paths₂ := path_append_stable pre₂ ((Run.nil.snoc (.slot ok₂)).append post₂) epoch early₂
  have assoc {x y z w : ForkedBeaconState preset} (p : Run config checks x y)
      (q : Run config checks y z) (r : Run config checks z w) :
      p.append (q.append r) = (p.append q).append r := by
    induction r with
    | nil => rfl
    | snoc r step ih => exact congrArg (fun run => run.snoc step) ih
  rw [assoc] at paths₁ paths₂
  rcases checkpoint_binding pre₁ pre₂ parameters genesis epoch root
      read₁ read₂ with same | evidence
  · exact .inl (paths₁.trans (same.trans paths₂.symm))
  · right
    apply hashEvidence_mono (one := pre₁.hashObjects ++ pre₂.hashObjects) _ evidence
    intro object member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (hashObjects_append_subset _ post₁
        (List.mem_append_left _ member))
    · exact List.mem_append_right _ (hashObjects_append_subset _ post₂
        (List.mem_append_left _ member))

end EthLib.Consensus.DirectSafety
