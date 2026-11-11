module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Transition.Genesis

/-!
# Selected inputs of a validated chain

The trace retains block inputs, which cannot be recovered computationally from Prop reachability.

Erasure to ChainStep reuses its invariant and monotonicity theorems.
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

end EthLib.Consensus
