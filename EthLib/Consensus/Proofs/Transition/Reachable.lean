module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Proofs: reachable states, and lifting a step property to whole chains

A chain runs three kinds of step on a beacon state.

- One slot: `advanceSlot`, which caches the slot and closes the epoch at its last slot.
- One upgrade: `upgradeNext`, run by `processUpgrades` when the next fork is due.
- One block: `applySignedBlock`, run by `stateTransitionAcross` once the state is at its slot.

Take a relation between two states that is reflexive and transitive.

When every such step satisfies it, it holds between the two ends of every chain.

That is the one lemma behind every invariant of the state transition.

A property of one state is the relation "if it holds before, it holds after".

A relation may need a property of the state before each step, such as an invariant.

It then carries that property along.

`Reaches` is the chain itself: empty slots and valid blocks, from one forked state to another.

`Reachable` starts it at a genesis state that launches the chain.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A relation between two forked states that every step of a chain satisfies.

It is reflexive and transitive, so it then holds between the two ends of a chain.

An upgrade is a step only when it is due, as `processUpgrades` runs it.

A block is a step for every execution engine, signed block and choice of result validation. -/
structure StepRelation (config : Config) (checks : SignatureChecks)
    (relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop) : Prop where
  refl : ∀ forked, relates forked forked
  trans : ∀ {first second third}, relates first second → relates second third →
    relates first third
  advanceSlot : ∀ {fork : Fork} {state after : BeaconState preset fork},
    advanceSlot config checks state = .ok after → relates ⟨fork, state⟩ ⟨fork, after⟩
  upgradeNext : ∀ {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
    upgradeDue config pre = true → upgradeNext config checks pre = .ok post →
    relates pre post.val
  applySignedBlock : ∀ {fork : Fork} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool},
    applySignedBlock config checks engine state signed validateResult = .ok after →
    relates ⟨fork, state⟩ ⟨fork, after⟩

namespace StepRelation

variable {relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop}

/-! ## Lifting through the chain functions -/

/-- The upgrades due at a slot are steps, one after another. -/
theorem processUpgrades (steps : StepRelation config checks relates)
    {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) : relates forked after := by
  fun_induction EthLib.Consensus.processUpgrades config checks forked generalizing after with
  | case1 forked due more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    exact steps.trans (steps.upgradeNext due stepOk) (more step rest)
  | case2 forked _ =>
    cases computed
    exact steps.refl _

/-- One slot, then the upgrades due at the slot it reaches. -/
theorem advanceSlotAcross (steps : StepRelation config checks relates)
    {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) : relates forked after := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  exact steps.trans (steps.advanceSlot advancedOk) (steps.processUpgrades upgraded)

theorem advanceSlotsAcross (steps : StepRelation config checks relates) :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset},
      advanceSlotsAcross config checks count forked = .ok after → relates forked after
  | 0, forked, after, computed => by
    simp only [EthLib.Consensus.advanceSlotsAcross, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact steps.refl _
  | count + 1, forked, after, computed => by
    simp only [EthLib.Consensus.advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact steps.trans (steps.advanceSlotAcross nextOk) (steps.advanceSlotsAcross rest)

/-- Advancing to a later slot, with the upgrades on the way. -/
theorem processSlotsAcross (steps : StepRelation config checks relates)
    {forked after : ForkedBeaconState preset} {slot : Slot}
    (computed : processSlotsAcross config checks forked slot = .ok after) :
    relates forked after := by
  simp only [EthLib.Consensus.processSlotsAcross, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact steps.advanceSlotsAcross advanced

/-- A valid block, from a state that may be of an earlier fork. -/
theorem stateTransitionAcross (steps : StepRelation config checks relates) {fork : Fork}
    {engine : ExecutionEngine preset fork} {forked : ForkedBeaconState preset}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    {after : BeaconState preset fork}
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    relates forked ⟨fork, after⟩ := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  exact steps.trans (steps.processSlotsAcross slotsOk) (steps.applySignedBlock applied)

/-! ## Lifting within one fork -/

theorem advanceSlots (steps : StepRelation config checks relates) {fork : Fork} :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      relates ⟨fork, state⟩ ⟨fork, after⟩
  | 0, state, after, computed => by
    simp only [EthLib.Consensus.advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact steps.refl _
  | count + 1, state, after, computed => by
    simp only [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact steps.trans (steps.advanceSlot nextOk) (steps.advanceSlots rest)

theorem processSlots (steps : StepRelation config checks relates) {fork : Fork}
    {state after : BeaconState preset fork} {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    relates ⟨fork, state⟩ ⟨fork, after⟩ := by
  simp only [EthLib.Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact steps.advanceSlots advanced

/-- A valid block, from a state of its own fork. -/
theorem stateTransition (steps : StepRelation config checks relates) {fork : Fork}
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    relates ⟨fork, state⟩ ⟨fork, after⟩ := by
  simp only [EthLib.Consensus.stateTransition, bind_ok_iff] at computed
  obtain ⟨advanced, slotsOk, applied⟩ := computed
  exact steps.trans (steps.processSlots slotsOk) (steps.applySignedBlock applied)

/-! ## Building a step relation -/

/-- A property of one state that every step keeps.

The relation is "if the property holds before, it holds after". -/
theorem ofPreserves {holds : ForkedBeaconState preset → Prop}
    (advanceSlot : ∀ {fork : Fork} {state after : BeaconState preset fork},
      holds ⟨fork, state⟩ → EthLib.Consensus.advanceSlot config checks state = .ok after →
      holds ⟨fork, after⟩)
    (upgradeNext : ∀ {pre : ForkedBeaconState preset}
      {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
      holds pre → upgradeDue config pre = true →
      EthLib.Consensus.upgradeNext config checks pre = .ok post → holds post.val)
    (applySignedBlock : ∀ {fork : Fork} {engine : ExecutionEngine preset fork}
      {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
      {validateResult : Bool}, holds ⟨fork, state⟩ →
      EthLib.Consensus.applySignedBlock config checks engine state signed validateResult =
        .ok after →
      holds ⟨fork, after⟩) :
    StepRelation config checks fun forked after => holds forked → holds after where
  refl _ := id
  trans first second := second ∘ first
  advanceSlot computed before := advanceSlot before computed
  upgradeNext due computed before := upgradeNext before due computed
  applySignedBlock computed before := applySignedBlock before computed

/-- A relation that each step satisfies when a property holds before it.

Each step also keeps the property.

Along a chain from a state with the property, every state has it, so the relation holds. -/
theorem ofGuarded {holds : ForkedBeaconState preset → Prop}
    (refl : ∀ forked, relates forked forked)
    (trans : ∀ {first second third}, relates first second → relates second third →
      relates first third)
    (advanceSlot : ∀ {fork : Fork} {state after : BeaconState preset fork},
      holds ⟨fork, state⟩ → EthLib.Consensus.advanceSlot config checks state = .ok after →
      holds ⟨fork, after⟩ ∧ relates ⟨fork, state⟩ ⟨fork, after⟩)
    (upgradeNext : ∀ {pre : ForkedBeaconState preset}
      {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
      holds pre → upgradeDue config pre = true →
      EthLib.Consensus.upgradeNext config checks pre = .ok post →
      holds post.val ∧ relates pre post.val)
    (applySignedBlock : ∀ {fork : Fork} {engine : ExecutionEngine preset fork}
      {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
      {validateResult : Bool}, holds ⟨fork, state⟩ →
      EthLib.Consensus.applySignedBlock config checks engine state signed validateResult =
        .ok after →
      holds ⟨fork, after⟩ ∧ relates ⟨fork, state⟩ ⟨fork, after⟩) :
    StepRelation config checks fun forked after =>
      holds forked → holds after ∧ relates forked after where
  refl forked before := ⟨before, refl forked⟩
  trans first second before :=
    -- The property reaches the middle state, which starts the second part.
    have ⟨middle, firstRelates⟩ := first before
    have ⟨last, secondRelates⟩ := second middle
    ⟨last, trans firstRelates secondRelates⟩
  advanceSlot computed before := advanceSlot before computed
  upgradeNext due computed before := upgradeNext before due computed
  applySignedBlock computed before := applySignedBlock before computed

end StepRelation

/-! ## Chains and reachable states -/

/-- One forked state leads to another by empty slots and valid blocks.

Each empty-slot run and each block may cross fork boundaries on the way.

A block may run with any execution engine and with or without validating the result. -/
inductive Reaches (config : Config) (checks : SignatureChecks) (start : ForkedBeaconState preset) :
    ForkedBeaconState preset → Prop where
  | refl : Reaches config checks start start
  | slots {forked after : ForkedBeaconState preset} {slot : Slot} :
    Reaches config checks start forked →
    processSlotsAcross config checks forked slot = .ok after →
    Reaches config checks start after
  | block {forked : ForkedBeaconState preset} {fork : Fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    {after : BeaconState preset fork} :
    Reaches config checks start forked →
    stateTransitionAcross config checks engine forked signed validateResult = .ok after →
    Reaches config checks start ⟨fork, after⟩

/-- A step relation holds between the two ends of every chain. -/
theorem StepRelation.reaches {relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop}
    (steps : StepRelation config checks relates) {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) : relates start after := by
  induction chain with
  | refl => exact steps.refl _
  | slots _ computed before => exact steps.trans before (steps.processSlotsAcross computed)
  | block _ computed before => exact steps.trans before (steps.stateTransitionAcross computed)

/-- A chain followed by another chain is a chain. -/
theorem Reaches.trans {first second third : ForkedBeaconState preset}
    (head : Reaches config checks first second) (tail : Reaches config checks second third) :
    Reaches config checks first third := by
  induction tail with
  | refl => exact head
  | slots _ computed more => exact .slots more computed
  | block _ computed more => exact .block more computed

/-- A genesis state that launches the chain.

It is the candidate state of a proof-of-work block.

Its genesis time is late enough, and enough validators are active. -/
def Genesis (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset) :
    Prop :=
  (∃ eth1BlockHash eth1Timestamp deposits,
    initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok forked.state) ∧
    isValidGenesisState config forked.state = true

/-- A state that a chain from a genesis state reaches. -/
def Reachable (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset) :
    Prop :=
  ∃ genesis, Genesis config checks genesis ∧ Reaches config checks genesis forked

/-- A property that holds at genesis and that every step keeps holds in every reachable state. -/
theorem Reachable.of_preserves {holds : ForkedBeaconState preset → Prop}
    (steps : StepRelation config checks fun forked after => holds forked → holds after)
    (genesis : ∀ forked, Genesis config checks forked → holds forked)
    {forked : ForkedBeaconState preset} (reachable : Reachable config checks forked) :
    holds forked :=
  have ⟨start, launched, chain⟩ := reachable
  steps.reaches chain (genesis start launched)

/-! ## The invariant of the state transition -/

/-- Each step keeps the invariant of the state transition, and never lowers the finalized epoch.

So both hold along every chain from a state that satisfies the invariant. -/
theorem stepRelation_invariant :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      Invariant forked.state → Invariant after.state ∧
        forked.state.finalizedCheckpoint.epoch ≤ after.state.finalizedCheckpoint.epoch :=
  StepRelation.ofGuarded (holds := fun forked => Invariant forked.state)
    (relates := fun forked after =>
      forked.state.finalizedCheckpoint.epoch ≤ after.state.finalizedCheckpoint.epoch)
    (fun _ => UInt64.le_refl _) UInt64.le_trans
    (fun holds computed => advanceSlot_invariant holds computed)
    (fun holds _ computed =>
      have ⟨after, same⟩ := upgradeNext_invariant holds computed
      ⟨after, same ▸ UInt64.le_refl _⟩)
    (fun holds computed =>
      -- The block is a frame, which keeps the checkpoints.
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      ⟨frame.invariant holds, frame.finalized ▸ UInt64.le_refl _⟩)

/-- Every reachable state satisfies the invariant of the state transition. -/
theorem Reachable.invariant {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) : Invariant forked.state := by
  obtain ⟨start, ⟨⟨_, _, _, initialized⟩, _⟩, chain⟩ := reachable
  have holds := (initializeBeaconStateFromEth1_invariant initialized).2
  exact (stepRelation_invariant.reaches chain holds).1

/-- Along a chain between reachable states, the finalized epoch never decreases. -/
theorem Reaches.finalized_le {start after : ForkedBeaconState preset}
    (reachable : Reachable config checks start) (chain : Reaches config checks start after) :
    start.state.finalizedCheckpoint.epoch ≤ after.state.finalizedCheckpoint.epoch :=
  (stepRelation_invariant.reaches chain reachable.invariant).2

end EthLib.Consensus
