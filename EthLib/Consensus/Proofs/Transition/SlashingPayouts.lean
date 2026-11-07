module

public import EthLib.Consensus.Proofs.Transition.Lifecycle
public import EthLib.Consensus.Proofs.Transition.SlashingBalances

/-!
# Proofs: the payouts of slashings, at every fork

A slashing pays a reward to the proposer of the block that includes it.

The reward is the effective balance of the slashed validator over the whistleblower quotient.

The quotient depends on the fork.

Before Electra it is `WHISTLEBLOWER_REWARD_QUOTIENT`.

From Electra it is `WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA`.

The proposer is the whistleblower by default, so the proposer gets the whole reward.

The reward splits into a proposer part and a whistleblower part.

Before Altair the proposer part is the reward over `PROPOSER_REWARD_QUOTIENT`.

From Altair it is `PROPOSER_WEIGHT / WEIGHT_DENOMINATOR` of the reward.

A slashing happens in exactly one place: `slashValidator`.

Only a proposer slashing and an attester slashing call it.

Each first checks that the validator is slashable, so not yet slashed.

So along a chain each validator is paid for at most once.

This file records each call as a `SlashingPayout`, along any run of the chain.

They form a `SlashingLedger`, which pays no validator twice.

Each validator it pays is not slashed at the start, and is slashed at the end.

From Gloas this needs a registry below `2^64` validators, as in `Lifecycle`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Slashed flags -/

/-- A slashing keeps every slashed flag that is set. -/
theorem slashValidator_keeps_slashed {state after : BeaconState preset fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after)
    {index : ValidatorIndex} (flag : slashedFlag state index = .ok true) :
    slashedFlag after index = .ok true := by
  obtain ⟨set, others⟩ := slashValidator_slashedFlag computed
  by_cases same : index = slashedIndex
  · exact same ▸ set
  · exact (others index same).trans flag

theorem processProposerSlashing_keeps_slashed {state after : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after)
    {index : ValidatorIndex} (flag : slashedFlag state index = .ok true) :
    slashedFlag after index = .ok true := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact slashValidator_keeps_slashed slashed flag

theorem processAttesterSlashing_keeps_slashed {state after : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after)
    {index : ValidatorIndex} (flag : slashedFlag state index = .ok true) :
    slashedFlag after index = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact (foldlM_slashIfSlashable _ foldOk).2.1 index flag

/-- Along a lifecycle, a slashed validator stays slashed, while the registry is below `2^64`. -/
theorem RegistryLifecycle.keeps_slashed {fork' : Base.Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork'} (lifecycle : RegistryLifecycle state after)
    (small : after.validators.data.size < 2 ^ 64) {index : ValidatorIndex}
    (flag : slashedFlag state index = .ok true) : slashedFlag after index = .ok true := by
  unfold slashedFlag getValidator at flag ⊢
  split at flag
  · rename_i validator found
    simp only [Except.map, Except.ok.injEq] at flag
    obtain ⟨later, laterFound, step⟩ := lifecycle.validators small _ validator found
    simp [laterFound, Except.map, step.slashed flag]
  · simp [Except.map] at flag

/-- A slashable validator is not yet slashed. -/
theorem not_slashed_of_isSlashableValidator {validator : Validator} {epoch : Epoch}
    (slashable : isSlashableValidator validator epoch = true) : validator.slashed = false := by
  cases flag : validator.slashed <;> simp_all [isSlashableValidator]

/-! ## Payouts and ledgers -/

/-- One call of `slashValidator`.

It holds the states before and after the call, the index, and the validator before the call.

Its fork is the fork of the block that includes the slashing. -/
structure SlashingPayout (preset : Preset) where
  fork : Base.Fork
  before : BeaconState preset fork
  after : BeaconState preset fork
  index : ValidatorIndex
  validator : Validator

namespace SlashingPayout

/-- The reward that the payout pays to the proposer. -/
def reward (payout : SlashingPayout preset) : Gwei :=
  whistleblowerReward preset payout.fork payout.validator

/-- The payout is a call that the chain makes.

The validator is read at its index, it may be slashed, and the call succeeds. -/
structure Valid (config : Config) (payout : SlashingPayout preset) : Prop where
  found : getValidator payout.before payout.index = .ok payout.validator
  slashable : isSlashableValidator payout.validator (getCurrentEpoch payout.before) = true
  called : slashValidator config payout.before payout.index = .ok payout.after

end SlashingPayout

/-- The payouts of a part of a chain, from `start` to `after`.

Each validator is paid for at most once.

Each was not slashed at the start, and is slashed at the end.

Each payout is a call that the chain makes. -/
structure SlashingLedger (config : Config) {fork' : Base.Fork} (start : BeaconState preset fork)
    (after : BeaconState preset fork') (payouts : List (SlashingPayout preset)) : Prop where
  nodup : (payouts.map (·.index)).Nodup
  unslashed : ∀ payout ∈ payouts, slashedFlag start payout.index ≠ .ok true
  slashed : ∀ payout ∈ payouts, slashedFlag after payout.index = .ok true
  valid : ∀ payout ∈ payouts, payout.Valid config

namespace SlashingLedger

theorem nil (state : BeaconState preset fork) : SlashingLedger config state state [] where
  nodup := List.nodup_nil
  unslashed _ member := absurd member List.not_mem_nil
  slashed _ member := absurd member List.not_mem_nil
  valid _ member := absurd member List.not_mem_nil

/-- Two ledgers in a row make one.

A validator paid in the first part is slashed at the middle state.

So the second part, which pays only validators not slashed there, cannot pay it again. -/
theorem append {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    {head tail : List (SlashingPayout preset)}
    (one : SlashingLedger config first second head) (two : SlashingLedger config second third tail)
    (keptOne : ∀ index, slashedFlag first index = .ok true → slashedFlag second index = .ok true)
    (keptTwo : ∀ index, slashedFlag second index = .ok true → slashedFlag third index = .ok true) :
    SlashingLedger config first third (head ++ tail) where
  nodup := by
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨one.nodup, two.nodup, ?_⟩
    intro index member other otherMember same
    obtain ⟨payout, payoutMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨later, laterMember, rfl⟩ := List.mem_map.mp otherMember
    exact two.unslashed later laterMember (same ▸ one.slashed payout payoutMember)
  unslashed payout member := by
    rcases List.mem_append.mp member with member | member
    · exact one.unslashed payout member
    · exact fun flag => two.unslashed payout member (keptOne _ flag)
  slashed payout member := by
    rcases List.mem_append.mp member with member | member
    · exact keptTwo _ (one.slashed payout member)
    · exact two.slashed payout member
  valid payout member := by
    rcases List.mem_append.mp member with member | member
    · exact one.valid payout member
    · exact two.valid payout member

/-- One call of `slashValidator` on a slashable validator. -/
theorem single {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (found : getValidator state index = .ok validator)
    (slashable : isSlashableValidator validator (getCurrentEpoch state) = true)
    (called : slashValidator config state index = .ok after) :
    SlashingLedger config state after [⟨fork, state, after, index, validator⟩] where
  nodup := by simp
  unslashed payout member := by
    obtain rfl := List.mem_singleton.mp member
    simp [slashedFlag, found, Except.map, not_slashed_of_isSlashableValidator slashable]
  slashed payout member := by
    obtain rfl := List.mem_singleton.mp member
    exact (slashValidator_slashedFlag called).1
  valid payout member := by
    obtain rfl := List.mem_singleton.mp member
    exact ⟨found, slashable, called⟩

/-- A ledger with the same payouts, between states with the same registry. -/
theorem congr {fork' : Base.Fork} {start start' : BeaconState preset fork}
    {after after' : BeaconState preset fork'} {payouts : List (SlashingPayout preset)}
    (ledger : SlashingLedger config start after payouts)
    (sameStart : start'.validators = start.validators)
    (sameAfter : after'.validators = after.validators) :
    SlashingLedger config start' after' payouts := by
  refine ⟨ledger.nodup, fun payout member => ?_, fun payout member => ?_, ledger.valid⟩
  · rw [slashedFlag, getValidator_of_validators_eq sameStart]
    exact ledger.unslashed payout member
  · rw [slashedFlag, getValidator_of_validators_eq sameAfter]
    exact ledger.slashed payout member

end SlashingLedger

/-! ## The payouts of the slashing operations -/

/-- The payout of a call of `slashValidator` on a state, read from that state. -/
def slashingPayout (state after : BeaconState preset fork) (index : ValidatorIndex) :
    Except TransitionError (SlashingPayout preset) := do
  let validator ← liftAccessor (getValidator state index)
  return ⟨fork, state, after, index, validator⟩

/-- The proposer slashings of a block, in order, with the payout of each. -/
def proposerSlashingPayouts (config : Config) (checks : SignatureChecks) :
    List ProposerSlashing → BeaconState preset fork →
      Except TransitionError (BeaconState preset fork × List (SlashingPayout preset))
  | [], state => .ok (state, [])
  | slashing :: rest, state => do
    let middle ← processProposerSlashing config checks state slashing
    let payout ← slashingPayout state middle slashing.signedHeader1.message.proposerIndex
    let (after, payouts) ← proposerSlashingPayouts config checks rest middle
    return (after, payout :: payouts)

/-- The steps of one attester slashing, with the payout of each step that slashes. -/
def indexSlashingPayouts (config : Config) :
    List ValidatorIndex → BeaconState preset fork × Bool →
      Except TransitionError ((BeaconState preset fork × Bool) × List (SlashingPayout preset))
  | [], step => .ok (step, [])
  | index :: rest, step => do
    let validator ← liftAccessor (getValidator step.1 index)
    let middle ← slashIfSlashable config step index
    let (after, payouts) ← indexSlashingPayouts config rest middle
    if isSlashableValidator validator (getCurrentEpoch step.1) then
      let payout ← slashingPayout step.1 middle.1 index
      return (after, payout :: payouts)
    else return (after, payouts)

/-- The attester slashings of a block, in order, with the payouts of each. -/
def attesterSlashingPayouts (config : Config) (checks : SignatureChecks) :
    List (AttesterSlashing preset fork) → BeaconState preset fork →
      Except TransitionError (BeaconState preset fork × List (SlashingPayout preset))
  | [], state => .ok (state, [])
  | slashing :: rest, state => do
    let middle ← processAttesterSlashing config checks state slashing
    let (_, payouts) ← indexSlashingPayouts config (slashingIndices slashing) (state, false)
    let (after, tail) ← attesterSlashingPayouts config checks rest middle
    return (after, payouts ++ tail)

/-- Each successful proposer slashing has its payout, and the payouts end at the same state. -/
theorem proposerSlashingPayouts_ok (slashings : List ProposerSlashing)
    {state after : BeaconState preset fork}
    (computed : slashings.foldlM (processProposerSlashing config checks) state = .ok after) :
    ∃ payouts, proposerSlashingPayouts config checks slashings state = .ok (after, payouts) ∧
      SlashingLedger config state after payouts := by
  induction slashings generalizing state with
  | nil =>
    cases computed
    exact ⟨[], rfl, .nil _⟩
  | cons slashing rest more =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨payouts, collected, ledger⟩ := more tail
    obtain ⟨_, _, _, validator, found, slashable, _⟩ := processProposerSlashing_checks first
    have called := first
    simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at called
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, called⟩ := called
    refine ⟨_ :: payouts, ?_, (SlashingLedger.single found slashable called).append ledger
      (fun _ flag => processProposerSlashing_keeps_slashed first flag)
      (fun index flag => foldlM_ok_invariant (fun state => slashedFlag state index = .ok true)
        (fun _ _ _ kept ok => processProposerSlashing_keeps_slashed ok kept) flag tail)⟩
    simp [proposerSlashingPayouts, first, slashingPayout, found, liftAccessor, Except.mapError,
      collected, bind, Except.bind, pure, Except.pure]

/-- Each step of an attester slashing that slashes has its payout. -/
theorem indexSlashingPayouts_ok (indices : List ValidatorIndex)
    {step after : BeaconState preset fork × Bool}
    (computed : indices.foldlM (slashIfSlashable config) step = .ok after) :
    ∃ payouts, indexSlashingPayouts config indices step = .ok (after, payouts) ∧
      SlashingLedger config step.1 after.1 payouts := by
  induction indices generalizing step with
  | nil =>
    cases computed
    exact ⟨[], rfl, .nil _⟩
  | cons index rest more =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨payouts, collected, ledger⟩ := more tail
    have read := first
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
    obtain ⟨validator, found, action⟩ := read
    have keptTail := fun index flag => (foldlM_slashIfSlashable rest tail).2.1 index flag
    by_cases slashable : isSlashableValidator validator (getCurrentEpoch step.1) = true
    · simp only [slashable, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at action
      obtain ⟨slashed, called, rfl⟩ := action
      refine ⟨_ :: payouts, ?_, (SlashingLedger.single found slashable called).append ledger
        (slashIfSlashable_ok first).2.1 keptTail⟩
      simp [indexSlashingPayouts, first, found, liftAccessor, Except.mapError, collected,
        slashable, slashingPayout, bind, Except.bind, pure, Except.pure]
    · have same : middle = step := by
        simpa [slashable, pure, Except.pure] using action.symm
      subst same
      refine ⟨payouts, ?_, ledger⟩
      simp [indexSlashingPayouts, first, found, liftAccessor, Except.mapError, collected,
        slashable, bind, Except.bind, pure, Except.pure]

/-- Each successful attester slashing has its payouts. -/
theorem attesterSlashingPayouts_ok (slashings : List (AttesterSlashing preset fork))
    {state after : BeaconState preset fork}
    (computed : slashings.foldlM (processAttesterSlashing config checks) state = .ok after) :
    ∃ payouts, attesterSlashingPayouts config checks slashings state = .ok (after, payouts) ∧
      SlashingLedger config state after payouts := by
  induction slashings generalizing state with
  | nil =>
    cases computed
    exact ⟨[], rfl, .nil _⟩
  | cons slashing rest more =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨payouts, collected, ledger⟩ := more tail
    have read := first
    simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at read
    obtain ⟨_, _, _, _, _, _, _, _, _, _, folded, foldOk, done⟩ := read
    simp only [pure, Except.pure, Except.ok.injEq] at done
    obtain ⟨_, _, rfl⟩ := done
    obtain ⟨paid, paidOk, paidLedger⟩ := indexSlashingPayouts_ok _ foldOk
    refine ⟨paid ++ payouts, ?_, paidLedger.append ledger
      (fun _ flag => processAttesterSlashing_keeps_slashed first flag)
      (fun index flag => foldlM_ok_invariant (fun state => slashedFlag state index = .ok true)
        (fun _ _ _ kept ok => processAttesterSlashing_keeps_slashed ok kept) flag tail)⟩
    simp [attesterSlashingPayouts, first, paidOk, collected, bind, Except.bind, pure,
      Except.pure]

/-! ## The payouts of a block -/

/-- The state on which the operations of a block run.

It is the part of `processBlock` before `processOperations`.

Before Altair it runs the header, the RANDAO reveal and the vote on the deposit contract.

From Altair it runs the same steps, with three changes.

- From Gloas the payload of the parent runs first.
- From Bellatrix the execution part runs after the header.
- From Heze there is no vote on the deposit contract. -/
def operationsInput (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then do
    let state ← (if gloas : .glamsterdam ≤ fork then
        processParentExecutionPayload config checks state gloas block.body
      else pure state)
    let state ← processBlockHeader state block
    let state ← (if bellatrix : .bellatrix ≤ fork then
        processBlockExecution config checks engine state block.body bellatrix
      else pure state)
    let state ← processRandao config checks state block.body
    if before : fork < .hegota then processEth1Data before state block.body else pure state
  else do
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
    let state ← processBlockHeader state block
    let state ← processRandao config checks state block.body
    processEth1Data before state block.body

/-- A block runs its operations on the state that `operationsInput` gives.

The validators keep their lifecycle before and after the operations. -/
theorem processBlock_operations {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ input operated, operationsInput config checks engine state block = .ok input ∧
      processOperations config checks input block.body state.latestBlockHeader.slot =
        .ok operated ∧
      RegistryLifecycle state input ∧ RegistryLifecycle operated after := by
  unfold processBlock at computed
  split at computed
  · rename_i altair
    unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    have paidKept : RegistryLifecycle state paid := by
      split at paidOk
      · exact registryLifecycle_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    have executedKept : RegistryLifecycle headed executed := by
      split at executedOk
      · exact registryLifecycle_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    have votedKept : RegistryLifecycle revealed voted := by
      split at votedOk
      · exact registryLifecycle_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    refine ⟨voted, operated, ?_, operatedOk, ?_, registryLifecycle_processSyncAggregate synced⟩
    · simp only [operationsInput, altair, ↓reduceDIte, bind_ok_iff]
      exact ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, votedOk⟩
    · exact paidKept.trans <| (registryLifecycle_processBlockHeader headedOk).trans <|
        executedKept.trans <| (registryLifecycle_processRandao revealedOk).trans votedKept
  · rename_i altair
    simp only [bind_ok_iff] at computed
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := computed
    refine ⟨voted, after, ?_, operatedOk, ?_, .refl _⟩
    · simp only [operationsInput, altair, ↓reduceDIte, bind_ok_iff]
      exact ⟨headed, headedOk, revealed, revealedOk, votedOk⟩
    · exact (registryLifecycle_processBlockHeader headedOk).trans <|
        (registryLifecycle_processRandao revealedOk).trans
          (registryLifecycle_processEth1Data votedOk)

/-- The operations of a block run the proposer slashings first, then the attester slashings.

The validators keep their lifecycle through the operations after them. -/
theorem processOperations_slashings {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∃ proposers attesters,
      body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) state =
        .ok proposers ∧
      body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks)
        proposers = .ok attesters ∧
      RegistryLifecycle attesters after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, proposersOk, attesters,
      attestersOk, _, attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    refine ⟨proposers, attesters, proposersOk, attestersOk, ?_⟩
    exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
        attestedOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok)
        exitsOk).trans <|
      (RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk).trans <|
      RegistryLifecycle.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, _, attestedOk, _,
    depositedOk, exited, exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : RegistryLifecycle exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : RegistryLifecycle changed after := by
    split at requestsOk
    · exact registryLifecycle_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  refine ⟨proposers, attesters, proposersOk, attestersOk, ?_⟩
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
      attestedOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDeposit ok)
      depositedOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

/-- The payouts of a block.

The payouts of its proposer slashings come first, then those of its attester slashings. -/
def blockSlashingPayouts (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (List (SlashingPayout preset)) := do
  let input ← operationsInput config checks engine state block
  let (proposers, first) ← proposerSlashingPayouts config checks
    block.body.proposerSlashings.data.toList input
  let (_, second) ← attesterSlashingPayouts config checks
    block.body.attesterSlashings.data.toList proposers
  return first ++ second

namespace SlashingLedger

/-- A ledger between two states is one between an earlier state and a later one.

The validators keep their lifecycle throughout, and the last registry is below `2^64`. -/
theorem widen {fork₁ fork₂ fork₃ : Base.Fork} {start : BeaconState preset fork}
    {first : BeaconState preset fork₁} {last : BeaconState preset fork₂}
    {after : BeaconState preset fork₃} {payouts : List (SlashingPayout preset)}
    (ledger : SlashingLedger config first last payouts)
    (before : RegistryLifecycle start first) (middle : RegistryLifecycle first last)
    (later : RegistryLifecycle last after) (small : after.validators.data.size < 2 ^ 64) :
    SlashingLedger config start after payouts where
  nodup := ledger.nodup
  unslashed payout member flag := ledger.unslashed payout member
    (before.keeps_slashed
      (Nat.lt_of_le_of_lt (Nat.le_trans middle.size_le later.size_le) small) flag)
  slashed payout member := later.keeps_slashed small (ledger.slashed payout member)
  valid := ledger.valid

end SlashingLedger

/-- A successful block has its payouts.

They form a ledger from the state before the block to the state after it.

This needs a registry below `2^64` after the block. -/
theorem blockSlashingPayouts_ok {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ payouts, blockSlashingPayouts config checks engine state block = .ok payouts ∧
      (after.validators.data.size < 2 ^ 64 → SlashingLedger config state after payouts) := by
  obtain ⟨input, operated, inputOk, operatedOk, before, later⟩ := processBlock_operations computed
  obtain ⟨proposers, attesters, proposersOk, attestersOk, rest⟩ :=
    processOperations_slashings operatedOk
  obtain ⟨first, firstOk, one⟩ := proposerSlashingPayouts_ok _ proposersOk
  obtain ⟨second, secondOk, two⟩ := attesterSlashingPayouts_ok _ attestersOk
  refine ⟨first ++ second, ?_, fun small => ?_⟩
  · simp [blockSlashingPayouts, inputOk, firstOk, secondOk, bind, Except.bind, pure,
      Except.pure]
  · have ledger := one.append two
      (fun index flag => foldlM_ok_invariant (fun state => slashedFlag state index = .ok true)
        (fun _ _ _ kept ok => processProposerSlashing_keeps_slashed ok kept) flag proposersOk)
      (fun index flag => foldlM_ok_invariant (fun state => slashedFlag state index = .ok true)
        (fun _ _ _ kept ok => processAttesterSlashing_keeps_slashed ok kept) flag attestersOk)
    have middle := (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok) proposersOk).trans
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
        attestersOk)
    exact ledger.widen before middle (rest.trans later) small

namespace SlashingLedger

/-- Between any two states, no payout is a ledger. -/
theorem empty {fork' : Base.Fork} (start : BeaconState preset fork)
    (after : BeaconState preset fork') : SlashingLedger config start after [] where
  nodup := List.nodup_nil
  unslashed _ member := absurd member List.not_mem_nil
  slashed _ member := absurd member List.not_mem_nil
  valid _ member := absurd member List.not_mem_nil

end SlashingLedger

/-! ## The payouts of a run -/

/-- The payouts of one step of a chain.

Only a block pays: a slot and an upgrade slash no validator. -/
def Step.slashingPayouts :
    {before after : ForkedBeaconState preset} → Step config checks before after →
      List (SlashingPayout preset)
  | _, _, .slot _ _ => []
  | _, _, .upgrade _ _ => []
  | _, _, .block (state := state) engine signed _ _ _ =>
    match blockSlashingPayouts config checks engine state signed.message with
    | .ok payouts => payouts
    | .error _ => []

/-- The payouts of a run, step by step, in the order the chain makes them. -/
def Run.slashingPayouts {start : ForkedBeaconState preset} :
    {after : ForkedBeaconState preset} → Run config checks start after →
      List (SlashingPayout preset)
  | _, .nil => []
  | _, .snoc run step => run.slashingPayouts ++ step.slashingPayouts

/-- The payouts of one step form a ledger, while the registry after it is below `2^64`. -/
theorem Step.slashingLedger {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (small : after.state.validators.data.size < 2 ^ 64) :
    SlashingLedger config before.state after.state step.slashingPayouts := by
  cases step with
  | slot _ _ => exact .empty _ _
  | upgrade _ _ => exact .empty _ _
  | block engine signed validateResult _ computed =>
    obtain ⟨payouts, collected, ledger⟩ :=
      blockSlashingPayouts_ok (applySignedBlock_ok computed).2.1
    simp only [Step.slashingPayouts, collected]
    exact ledger small

/-- The payouts of a run form a ledger, while the registry at its end is below `2^64`.

So each validator is paid for at most once along the run.

From Gloas the condition is needed.

There a registry of `2^64` validators gives a new validator an index that is already used. -/
theorem Run.slashingLedger {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      SlashingLedger config start.state after.state run.slashingPayouts
  | _, .nil, _ => .empty _ _
  | _, .snoc run step, small => by
    have stepLifecycle := stepRelation_registryLifecycle.step step
    have middleSmall := Nat.lt_of_le_of_lt stepLifecycle.size_le small
    exact (run.slashingLedger middleSmall).append (step.slashingLedger small)
      (fun _ flag => (stepRelation_registryLifecycle.run run).keeps_slashed middleSmall flag)
      (fun _ flag => stepLifecycle.keeps_slashed small flag)

end EthLib.Consensus
