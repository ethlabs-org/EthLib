module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Transition.Genesis

/-!
# Proofs: a trace of the steps of a chain, with their inputs

A step of a chain says that one state follows from another, but it does not keep the block.

A run keeps each step with its inputs: the slot step, or the signed block and its engine.

So a theorem about a run can name the blocks of that run and the attestations in them.

A block step of a run checks its state root, and is applied on a state with no upgrade due.

Each step of a run is a step of a chain, so the invariants of chains hold along a run.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A genesis state built from deposits.

It need not be valid for launch. -/
def Genesis (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset) : Prop :=
  ∃ hash time deposits,
    initializeBeaconStateFromEth1 config checks hash time deposits = .ok g.state

/-- One step of a run: a slot, or a signed block applied with its state root checked. -/
inductive Step (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Type where
  | slot {before after} (ok : advanceSlotAcross config checks before = .ok after) :
      Step config checks before after
  | block {fork : Fork} {before after : BeaconState preset fork}
      (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
      (due : upgradeDue config ⟨fork, before⟩ = false)
      (ok : applySignedBlock config checks engine before signed true = .ok after) :
      Step config checks ⟨fork, before⟩ ⟨fork, after⟩

/-- A sequence of steps from `first`, which keeps the input of each step. -/
inductive Run (config : Config) (checks : SignatureChecks) (first : ForkedBeaconState preset) :
    ForkedBeaconState preset → Type where
  | nil : Run config checks first first
  | snoc {middle last} (pre : Run config checks first middle)
      (step : Step config checks middle last) : Run config checks first last

/-- The steps of `pre`, then the steps of `tail`. -/
def Run.append {first middle last : ForkedBeaconState preset}
    (pre : Run config checks first middle) (tail : Run config checks middle last) :
    Run config checks first last :=
  match tail with
  | .nil => pre
  | .snoc tail step => .snoc (pre.append tail) step

/-- A step is in a run, with its inputs, not only its two states. -/
inductive Run.Contains {first : ForkedBeaconState preset} :
    {last before after : ForkedBeaconState preset} → Run config checks first last →
      Step config checks before after → Prop where
  | last {middle after} (pre : Run config checks first middle)
      (step : Step config checks middle after) : Contains (.snoc pre step) step
  | earlier {middle last before after} {pre : Run config checks first middle}
      {step : Step config checks before after} (member : Contains pre step)
      (next : Step config checks middle last) : Contains (.snoc pre next) step

/-- A step of a run is a step of a chain. -/
theorem Step.chainStep {x y : ForkedBeaconState preset} (step : Step config checks x y) :
    ChainStep config checks x y := by
  cases step with
  | slot ok => exact .slot ok
  | block engine signed _ ok => exact .block engine signed true ok

/-- A run is a sequence of steps of a chain. -/
theorem Run.chainSteps {x y : ForkedBeaconState preset} (run : Run config checks x y) :
    Relation.ReflTransGen (ChainStep config checks) x y := by
  induction run with
  | nil => exact .refl
  | snoc _ step ih => exact ih.tail step.chainStep

/-- Appending runs is associative. -/
theorem Run.append_assoc {a b c d : ForkedBeaconState preset} (one : Run config checks a b)
    (two : Run config checks b c) (three : Run config checks c d) :
    one.append (two.append three) = (one.append two).append three := by
  induction three with
  | nil => rfl
  | snoc three step ih => exact congrArg (fun run => run.snoc step) ih

/-- A step of two appended runs is a step of one of them. -/
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

/-- A step of a run splits it into the run before the step, the step and the run after it. -/
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
theorem Run.exists_of_stateTransitionAcross {fork : Fork} {first : ForkedBeaconState preset}
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
    ∃ run : Run config checks ⟨fork, state⟩ ⟨fork, after⟩,
      ∀ {x y} (step : Step config checks x y), run.Contains step →
        ∃ h : advanceSlotAcross config checks x = .ok y, step = .slot h := by
  induction count generalizing state with
  | zero =>
    cases advanced
    exact ⟨.nil, by intro x y step member; cases member⟩
  | succ count ih =>
    obtain ⟨next, stepped, rest⟩ := bind_ok_iff.mp advanced
    have slotsEq := advanceSlots_slot count rest
    have nextSlot := advanceSlot_slot stepped
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, next⟩ := by
      rw [advanceSlotAcross_of_before (fun nextFork scheduled => by
        have := before nextFork scheduled
        omega), stepped]
      rfl
    obtain ⟨tail, slotsOnly⟩ := ih rest
    refine ⟨(Run.nil.snoc (.slot across)).append tail, ?_⟩
    intro x y step member
    rcases (Run.contains_append _ _ step).mp member with member | member
    · cases member with
      | last => exact ⟨across, rfl⟩
      | earlier member => cases member
    · exact slotsOnly step member

/-- A run from a state to the state at a later slot, when the slot stays before the next fork. -/
theorem run_of_processSlots {fork : Fork} {state after : BeaconState preset fork} {slot : Slot}
    (processed : processSlots config checks state slot = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, state⟩ ⟨fork, after⟩) := by
  have lastSlot := (processSlots_slot processed).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
  obtain ⟨_, _, advanced⟩ := processed
  obtain ⟨run, -⟩ := run_of_advanceSlots _ advanced (by simpa only [lastSlot] using before)
  exact ⟨run⟩

end EthLib.Consensus
