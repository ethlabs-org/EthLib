module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.Slot
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Transition.Genesis

/-!
# Selected inputs of a validated chain

The trace retains block inputs, which cannot be recovered computationally from Prop reachability.

Erasure to ChainStep reuses its invariant and monotonicity theorems.

A run has at most one block step for each slot it spans, counting the slot of its first state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Successful genesis initialization; launch-time validity is not needed for trace invariants. -/
def Genesis (g : ForkedBeaconState preset) : Prop :=
  ∃ hash time deposits,
    initializeBeaconStateFromEth1 config checks hash time deposits = .ok g.state

inductive Step (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Type where
  | slot {before after} (ok : advanceSlotAcross config checks before = .ok after) :
      Step config checks before after
  | block {fork : Fork} {before after : BeaconState preset fork}
      (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
      (due : upgradeDue config ⟨fork, before⟩ = false)
      (ok : applySignedBlock config checks engine before signed true = .ok after) :
      Step config checks ⟨fork, before⟩ ⟨fork, after⟩

inductive Run (config : Config) (checks : SignatureChecks) (first : ForkedBeaconState preset) :
    ForkedBeaconState preset → Type where
  | nil : Run config checks first first
  | snoc {middle last} (pre : Run config checks first middle)
      (step : Step config checks middle last) : Run config checks first last

def Run.append {first middle last : ForkedBeaconState preset}
    (pre : Run config checks first middle) (tail : Run config checks middle last) :
    Run config checks first last :=
  match tail with
  | .nil => pre
  | .snoc tail step => .snoc (pre.append tail) step

/-- Membership retains the selected transition input, not only its endpoints. -/
inductive Run.Contains {first : ForkedBeaconState preset} :
    {last before after : ForkedBeaconState preset} → Run config checks first last →
      Step config checks before after → Prop where
  | last {middle after} (pre : Run config checks first middle)
      (step : Step config checks middle after) : Contains (.snoc pre step) step
  | earlier {middle last before after} {pre : Run config checks first middle}
      {step : Step config checks before after} (member : Contains pre step)
      (next : Step config checks middle last) : Contains (.snoc pre next) step

theorem Step.chainStep {x y : ForkedBeaconState preset} (step : Step config checks x y) :
    ChainStep config checks x y := by
  cases step with
  | slot ok => exact .slot ok
  | block engine signed _ ok => exact .block engine signed true ok

theorem Run.chainSteps {x y : ForkedBeaconState preset} (run : Run config checks x y) :
    Relation.ReflTransGen (ChainStep config checks) x y := by
  induction run with
  | nil => exact .refl
  | snoc _ step ih => exact ih.tail step.chainStep

theorem Run.contains_append {g x y u v : ForkedBeaconState preset}
    (pre : Run config checks g x) (tail : Run config checks x y)
    (step : Step config checks u v) :
    (pre.append tail).Contains step ↔ pre.Contains step ∨ tail.Contains step := by
  induction tail with
  | nil =>
    constructor
    · exact Or.inl
    · rintro (member | member)
      · exact member
      · cases member
  | snoc tail next ih =>
    constructor
    · intro member
      cases member with
      | last => exact .inr (.last _ _)
      | earlier member =>
        rcases ih.mp member with member | member
        · exact .inl member
        · exact .inr (.earlier member next)
    · rintro (member | member)
      · exact .earlier (ih.mpr (.inl member)) next
      · cases member with
        | last => exact .last _ _
        | earlier member => exact .earlier (ih.mpr (.inr member)) next

/-- A selected occurrence splits into its exact prefix, edge and suffix. -/
theorem Run.contains_split {g a x y : ForkedBeaconState preset}
    (run : Run config checks g a) (step : Step config checks x y) (member : run.Contains step) :
    ∃ (pre : Run config checks g x) (post : Run config checks y a),
      run = (pre.snoc step).append post := by
  induction member with
  | last pre step => exact ⟨pre, .nil, rfl⟩
  | earlier member next ih =>
    obtain ⟨pre, post, same⟩ := ih
    exact ⟨pre, post.snoc next, congrArg (fun run => run.snoc next) same⟩

/-- A successful block transition selects its slot prefix and the supplied final block input. -/
theorem Run.stateTransition {fork : Fork} {first : ForkedBeaconState preset}
    {last : BeaconState preset fork} (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork)
    (ok : stateTransitionAcross config checks engine first signed true = .ok last) :
    ∃ (advanced : BeaconState preset fork) (pre : Run config checks first ⟨fork, advanced⟩)
      (due : upgradeDue config ⟨fork, advanced⟩ = false)
      (applied : applySignedBlock config checks engine advanced signed true = .ok last),
      processSlotsAcross config checks first signed.message.slot = .ok ⟨fork, advanced⟩ ∧
      (∀ {x y} (step : Step config checks x y), pre.Contains step →
        ∃ h : advanceSlotAcross config checks x = .ok y, step = .slot h) ∧
      (pre.snoc (.block engine signed due applied)).Contains
        (.block engine signed due applied) := by
  have upgrades_done {before after : ForkedBeaconState preset}
      (computed : processUpgrades config checks before = .ok after) :
      upgradeDue config after = false := by
    fun_induction processUpgrades config checks before generalizing after with
    | case1 before _ ih =>
      obtain ⟨next, _, rest⟩ := bind_ok_iff.mp computed
      exact ih next rest
    | case2 before notDue =>
      cases computed
      simpa using notDue
  have slots_run (count : Nat) : ∀ {before after : ForkedBeaconState preset},
      advanceSlotsAcross config checks count before = .ok after →
      ∃ run : Run config checks before after,
        (∀ {x y} (step : Step config checks x y), run.Contains step →
          ∃ h : advanceSlotAcross config checks x = .ok y, step = .slot h) ∧
        (count ≠ 0 → upgradeDue config after = false) := by
    induction count with
    | zero =>
      intro before after computed
      cases computed
      exact ⟨.nil, (by intro x y step member; cases member), (by omega)⟩
    | succ count ih =>
      intro before after computed
      obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp computed
      obtain ⟨tail, slotsOnly, done⟩ := ih rest
      refine ⟨(Run.nil.snoc (.slot nextOk)).append tail, ?_, ?_⟩
      · intro x y step member
        rcases (Run.contains_append _ _ step).mp member with member | member
        · cases member with
          | last => exact ⟨nextOk, rfl⟩
          | earlier member => cases member
        · exact slotsOnly step member
      · intro _
        by_cases zero : count = 0
        · subst count
          cases rest
          obtain ⟨_, _, upgraded⟩ := bind_ok_iff.mp nextOk
          exact upgrades_done upgraded
        · exact done zero
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok ok
  have computed := slotsOk
  simp only [processSlotsAcross, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, later, computed⟩ := computed
  obtain ⟨pre, slotsOnly, done⟩ := slots_run _ computed
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  have due : upgradeDue config ⟨fork, advanced⟩ = false := done (by omega)
  exact ⟨advanced, pre, due, applied, slotsOk, slotsOnly, .last pre _⟩

/-- A run of empty slots, when all of them stay before the next fork. -/
theorem run_of_advanceSlots {fork : Fork} (count : Nat) {state after : BeaconState preset fork}
    (advanced : advanceSlots config checks count state = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      after.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, state⟩ ⟨fork, after⟩) := by
  induction count generalizing state with
  | zero =>
    cases advanced
    exact ⟨.nil⟩
  | succ count ih =>
    obtain ⟨next, stepped, rest⟩ := bind_ok_iff.mp advanced
    have slotsEq := advanceSlots_slot count rest
    have nextSlot := advanceSlot_slot stepped
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, next⟩ := by
      rw [advanceSlotAcross_of_before (fun nextFork scheduled => by
        have := before nextFork scheduled
        omega), stepped]
      rfl
    obtain ⟨tail⟩ := ih rest
    exact ⟨(Run.nil.snoc (.slot across)).append tail⟩

/-- A run from a state to the state at a later slot, when the slot stays before the next fork. -/
theorem run_of_processSlots {fork : Fork} {state after : BeaconState preset fork} {slot : Slot}
    (processed : processSlots config checks state slot = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, state⟩ ⟨fork, after⟩) := by
  have lastSlot := (processSlots_slot processed).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
  obtain ⟨_, _, advanced⟩ := processed
  exact run_of_advanceSlots _ advanced (by simpa only [lastSlot] using before)

/-- The number of block steps of a run. -/
def Run.blockCount {first last : ForkedBeaconState preset} :
    Run config checks first last → Nat
  | .nil => 0
  | .snoc pre (.slot _) => pre.blockCount
  | .snoc pre (.block ..) => pre.blockCount + 1

/-- The block steps of a run, and one more if its last state can still take a block, fit its slots.

A state can take a block when its latest block header is before its slot.

A slot step moves the slot on by one, even across the upgrades due at it.

A block step spends the slot of its state, and leaves the header of the block at that slot. -/
private theorem Run.blockCount_le {first last : ForkedBeaconState preset}
    (run : Run config checks first last) :
    run.blockCount +
      (if last.state.latestBlockHeader.slot < last.state.slot then 1 else 0) +
        first.state.slot.toNat ≤ last.state.slot.toNat + 1 := by
  induction run with
  | nil =>
    simp only [Run.blockCount]
    split <;> omega
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      have moved : last.state.slot.toNat = middle.state.slot.toNat + 1 :=
        (congrArg UInt64.toNat (processUpgrades_slot upgraded)).trans (advanceSlot_slot advancedOk)
      simp only [Run.blockCount]
      split at ih <;> split <;> omega
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      obtain ⟨atSlot, newer, -⟩ := processBlock_parentRoot processed
      obtain ⟨parented, headed, -, headerOk, kept⟩ := processBlock_header_split processed
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
      have slot := processBlock_slot processed
      -- The state before the block has a free slot, which the block spends.
      have free : before.latestBlockHeader.slot < before.slot := atSlot ▸ newer
      have spent : ¬ after.latestBlockHeader.slot < after.slot := by
        rw [kept, slot, ← atSlot]
        exact UInt64.lt_irrefl _
      have slotNat : after.slot.toNat = before.slot.toNat := congrArg UInt64.toNat slot
      simp only [Run.blockCount, spent, ↓reduceIte]
      simp only [free, ↓reduceIte] at ih
      omega

/-- A run has at most one block step for each slot of its range.

Every state of the run is at a slot of the range, and a block spends the slot of its state. -/
theorem Run.blocks_le_slots {first last : ForkedBeaconState preset}
    (run : Run config checks first last) {a b : Nat} (low : a ≤ first.state.slot.toNat)
    (high : last.state.slot.toNat ≤ b) : run.blockCount ≤ b - a + 1 := by
  have := run.blockCount_le
  split at this <;> omega

end EthLib.Consensus
