module

public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Proofs.Transition.Trace
public import Mathlib.Data.Finset.Card

/-!
# Proofs: before Altair, each pending attestation lies in the epoch of its list

A block accepts an attestation only when its target epoch is the current or the previous epoch.

That target epoch must also be the epoch of its slot.

The block records it in the list of the current epoch or of the previous one, by its target.

At the end of an epoch the list of the current epoch becomes that of the previous one.

The other steps keep both lists, and genesis starts with both empty.

An upgrade moves the state to Altair, where no pending attestation remains.

So along a run from genesis, each pending attestation of the previous epoch has its slot in it.

Its committee is cut from the validators active in that epoch.

This is `PendingVoted` for the set of all votes, whose votes then say nothing.

Each pending attestation also names the proposer of the block that included it.

The steps of a block before its attestations keep the proposer of the slot.

So those attestations and the blocks of two epochs have at most two epochs of proposers.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- Along a run from genesis, the pending attestations lie in the epochs of their lists.

Their target epoch is the epoch of their list, and the epoch of their slot.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem Run.pendingVoted_univ {g x : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (run : Run config checks g x)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    PendingVoted Set.univ x.state := by
  -- The two justified checkpoints are equal in the first two epochs, which the slots need.
  suffices both : JustifiedEarly x.state ∧ PendingVoted Set.univ x.state from both.2
  induction run with
  | nil =>
    obtain ⟨_, _, _, computed⟩ := genesis
    refine ⟨JustifiedEarly.of_initializeBeaconStateFromEth1 computed,
      fun before current pending member => ?_⟩
    rw [initializeBeaconStateFromEth1_pending computed before current] at member
    simp at member
  | @snoc middle last pre step ih =>
    obtain ⟨early, holds⟩ := ih
    cases step with
    | slot computed =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
      have pending : PendingVoted Set.univ advanced := by
        by_cases before : middle.fork < .altair
        · exact holds.of_advanceSlot before apart early advancedOk
        · exact fun before' => absurd before' before
      exact ⟨(early.of_advanceSlot advancedOk).of_processUpgrades upgraded,
        pending.of_processUpgrades upgraded⟩
    | block engine signed due applied =>
      obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
      exact ⟨early.of_frame (frame_processBlock blockOk), fun before =>
        (PendingVoted.of_processBlock before apart holds blockOk).mono
          (fun _ _ => trivial) before⟩

/-- Before Altair, the attestations that match the source of the previous epoch lie in it.

Each has its slot in the previous epoch.

At genesis the previous epoch is the current one, and the list of the current epoch is read. -/
theorem PendingVoted.matchingSource_slot {votes : Set (ValidatorIndex × AttestationData)}
    {state : BeaconState preset fork} (holds : PendingVoted votes state) (before : fork < .altair)
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingSourceAttestations state before (getPreviousEpoch state) =
      .ok attestations) :
    ∀ pending ∈ attestations,
      computeEpochAtSlot preset pending.data.slot = getPreviousEpoch state := by
  intro pending member
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at matching
  obtain ⟨_, _, rfl⟩ := matching
  by_cases here : getPreviousEpoch state = getCurrentEpoch state
  · simp only [here, ↓reduceIte] at member
    obtain ⟨epoch, slot, -⟩ := holds before true pending member
    simp only [↓reduceIte] at epoch
    rw [slot, epoch, here]
  · simp only [here, ↓reduceIte] at member
    obtain ⟨epoch, slot, -⟩ := holds before false pending member
    simp only [Bool.false_eq_true, ↓reduceIte] at epoch
    rw [slot, epoch]

/-! ## The proposers that an epoch boundary pays, before Altair -/

/-- A proposer search reads a validator only for its effective balance. -/
private theorem proposerSearch_eq_of_effectiveBalances {vs ws : Array Validator}
    {indices : Array ValidatorIndex}
    {order : Nat → Nat} {seed : Bytes32}
    (same : ∀ i : Nat,
      (ws[i]?).map Validator.effectiveBalance = (vs[i]?).map Validator.effectiveBalance)
    (i : Nat) :
    proposerSearch preset fork ws indices order seed i =
      proposerSearch preset fork vs indices order seed i := by
  unfold proposerSearch
  generalize indices.getD (order (i % indices.size)) 0 = candidate
  dsimp only
  have read := same candidate.toNat
  cases w : ws[candidate.toNat]? <;> cases v : vs[candidate.toNat]? <;>
    simp only [w, v, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at read
  · rfl
  · simp only [read]
    split
    · rw [proposerSearch_eq_of_effectiveBalances same (i + 1)]
    · rfl
termination_by 2 ^ 64 - i

variable {state after : BeaconState preset fork}

/-- Before Fulu, two states of one slot with the same proposer of the slot.

They agree on activity up to the current epoch and on every effective balance.

Of the RANDAO mixes, they may differ only at the one of the current epoch. -/
private structure ProposerKept (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  active : ActiveKept (getCurrentEpoch state) state after
  mixes : MixesKeptBut (getCurrentEpoch state) state after
  balances : ∀ i : Nat, (after.validators.data[i]?).map Validator.effectiveBalance =
    (state.validators.data[i]?).map Validator.effectiveBalance

/-- Every state keeps its own proposer. -/
private theorem ProposerKept.refl (state : BeaconState preset fork) : ProposerKept state state :=
  ⟨rfl, ActiveKept.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

/-- Two steps that keep the proposer in a row keep it. -/
private theorem ProposerKept.trans {first second third : BeaconState preset fork}
    (one : ProposerKept first second) (two : ProposerKept second third) :
    ProposerKept first third := by
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.slot]
  exact ⟨two.slot.trans one.slot, one.active.trans (epoch ▸ two.active),
    fun other apart => (two.mixes other (epoch ▸ apart)).trans (one.mixes other apart),
    fun i => (two.balances i).trans (one.balances i)⟩

/-- A step that keeps the registry, the mixes and the slot keeps the proposer. -/
private theorem ProposerKept.of_eq (validators : after.validators = state.validators)
    (mixes : after.randaoMixes = state.randaoMixes) (slot : after.slot = state.slot) :
    ProposerKept state after :=
  ⟨slot, ActiveKept.of_validators (by rw [validators]) _, fun _ _ => by rw [mixes],
    fun _ => by rw [validators]⟩

/-- Before Fulu, the proposer of the slot reads the slot, activity, a mix and effective balances.

The mix is `MIN_SEED_LOOKAHEAD + 1` epochs back, never the one of the current epoch.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
private theorem ProposerKept.proposer (early : fork < .fusaka)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (kept : ProposerKept state after) :
    getBeaconProposerIndex after = getBeaconProposerIndex state := by
  have notFulu : ¬ .fusaka ≤ fork := Nat.not_le_of_lt early
  have epoch : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, kept.slot]
  -- The seed reads the mix `MIN_SEED_LOOKAHEAD + 1` epochs back, never that of the current epoch.
  have seed : getSeed after (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER =
      getSeed state (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER := by
    refine getSeed_eq_of_mix _ fun shifted shiftedEq => kept.mixes shifted fun same => ?_
    have same := congrArg UInt64.toNat same
    rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
    exact Nat.mod_ne_of_sub_lt (low := (getCurrentEpoch state).toNat) (high := shifted.toNat)
      (length := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (by omega) (by omega) same
  unfold getBeaconProposerIndex computeProposerIndex
  simp only [notFulu, ↓reduceDIte, epoch, seed, kept.slot,
    kept.active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _),
    proposerSearch_eq_of_effectiveBalances kept.balances]

/-- Before Altair, a step of a block before its attestations.

It keeps the proposer of the slot and both lists of pending attestations. -/
private structure HeadKept (state after : BeaconState preset fork) : Prop
    extends ProposerKept state after where
  previous : after.previousEpochAttestations = state.previousEpochAttestations
  current : after.currentEpochAttestations = state.currentEpochAttestations

/-- Every state is such a step to itself. -/
private theorem HeadKept.refl (state : BeaconState preset fork) : HeadKept state state :=
  ⟨ProposerKept.refl state, rfl, rfl⟩

/-- Two such steps in a row are one. -/
private theorem HeadKept.trans {first second third : BeaconState preset fork}
    (one : HeadKept first second) (two : HeadKept second third) : HeadKept first third :=
  ⟨one.toProposerKept.trans two.toProposerKept, two.previous.trans one.previous,
    two.current.trans one.current⟩

/-- A step that keeps the registry, the mixes, the slot and the lists is such a step. -/
private theorem HeadKept.of_eq (validators : after.validators = state.validators)
    (mixes : after.randaoMixes = state.randaoMixes) (slot : after.slot = state.slot)
    (previous : after.previousEpochAttestations = state.previousEpochAttestations)
    (current : after.currentEpochAttestations = state.currentEpochAttestations) :
    HeadKept state after :=
  ⟨ProposerKept.of_eq validators mixes slot, previous, current⟩

/-- A fold of such steps is one. -/
private theorem HeadKept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x t, step s x = .ok t → HeadKept s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : HeadKept state after :=
  foldlM_ok_invariant (HeadKept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (HeadKept.refl state) computed

/-- A write of a validator with the old effective balance and activity is such a step. -/
private theorem headKept_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (balance : validator.effectiveBalance = old.effectiveBalance)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : HeadKept state after := by
  have step := activeStep_setValidator found same set
  rw [setValidator_eq_setValidatorAt] at set
  rw [getValidator_eq_getValidatorAt] at found
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have read : state.validators.data[index.toNat]? = some old := by
    simpa [getValidatorAt, inside] using found
  refine ⟨⟨rfl, step.2.mono (getCurrentEpoch_le_activityFixedEpoch _), fun _ _ => rfl,
    fun i => ?_⟩, rfl, rfl⟩
  by_cases eq : i = index.toNat
  · subst i
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, read, balance]
  · simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm eq]

/-- A write of a balance is such a step. -/
private theorem headKept_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : HeadKept state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact HeadKept.of_eq rfl rfl rfl rfl rfl

/-- Starting an exit is such a step: the new exit epoch is after the fixed epoch. -/
private theorem headKept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : HeadKept state after := by
  obtain ⟨validator, found,
    ⟨_, rfl⟩ | ⟨far, queued, exitEpoch, withdrawableEpoch, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact HeadKept.refl _
  have later := exitQueue_lt queue
  obtain ⟨left, earliest, rfl⟩ := exitQueue_eq queue
  -- The validator had not started to exit, and its new exit epoch is after the fixed epoch.
  exact (HeadKept.of_eq rfl rfl rfl rfl rfl :
    HeadKept state { state with exitBalanceToConsume := left, earliestExitEpoch := earliest }).trans
    (headKept_setValidator
      (state := { state with exitBalanceToConsume := left, earliestExitEpoch := earliest })
      (validator := { validator with exitEpoch, withdrawableEpoch }) found rfl
      (fun _ le => isActiveValidator_eq_of_exit rfl far
        (activityFixedEpoch_lt_of_toNat_lt later) le) set)

/-- Before Altair, a slashing is such a step. -/
private theorem headKept_slashValidator (early : fork < .altair) {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    HeadKept state after := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitedOk,
    found, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok computed
  -- Marking the validator slashed keeps its activation and exit epochs and its balance.
  refine (headKept_initiateValidatorExit exitedOk).trans <|
    (headKept_setValidator (validator := { validator with slashed := true, withdrawableEpoch := _ })
      found rfl (fun _ _ => rfl) markedOk).trans <|
    (HeadKept.of_eq rfl rfl rfl rfl rfl : HeadKept marked { marked with slashings }).trans <|
    (headKept_setBalance (decreaseBalance_ok loweredOk).choose_spec).trans <|
    (headKept_setBalance (increaseBalance_ok raisedOk).choose_spec).trans <|
    (headKept_setBalance (increaseBalance_ok lastOk).choose_spec).trans ?_
  subst done
  split
  · exact absurd ‹_› (Nat.not_le_of_lt (Nat.lt_trans early (by decide)))
  · exact HeadKept.refl _

/-- Before Altair, a proposer slashing is such a step. -/
private theorem headKept_processProposerSlashing (early : fork < .altair)
    {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    HeadKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact headKept_slashValidator early slashed

/-- Before Altair, an attester slashing is such a step. -/
private theorem headKept_processAttesterSlashing (early : fork < .altair)
    {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    HeadKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine (foldlM_ok_invariant (fun step => HeadKept state step.1)
    (fun step _ next before ok => ?_) (HeadKept.refl state) folded)
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.trans (headKept_slashValidator early slashed)
  · cases ok
    exact before

/-- A voluntary exit is such a step. -/
private theorem headKept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    HeadKept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact headKept_initiateValidatorExit exited

/-- Before Altair, a block records each of its attestations with the proposer of the block.

Every pending attestation after the block was there before it, or names the proposer of the block.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
private theorem processBlock_pendingProposer (early : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) (current : Bool) :
    ∀ pending ∈ recentPending after early current,
      pending ∈ recentPending state early current ∨
        pending.proposerIndex = block.proposerIndex := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt early
  have notCapella : ¬Fork.shapella ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans early (by decide : Fork.altair < Fork.shapella))
  have notElectra : ¬Fork.pectra ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans early (by decide : Fork.altair < Fork.pectra))
  have notGloas : ¬Fork.glamsterdam ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans early (by decide : Fork.altair < Fork.glamsterdam))
  have beforeFulu : fork < .fusaka := Nat.lt_trans early (by decide)
  unfold processBlock at computed
  simp only [notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨headed, headerOk, revealed, randaoOk, voted, eth1Ok, operationsOk⟩ := computed
  unfold processOperations at operationsOk
  simp only [notGloas, notElectra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at operationsOk
  obtain ⟨_, _, _, _, proposersDone, proposersOk, slashingsDone, attestersOk, attested,
    attestedOk, deposited, depositedOk, exited, exitsOk, changed, changesOk, requestsOk⟩ :=
    operationsOk
  simp only [processBlsToExecutionChanges, notCapella, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at changesOk requestsOk
  subst changesOk requestsOk
  -- The proposer of the slot, which the header checks against the block.
  have proposer := (processBlockHeader_checks headerOk).2.2.1
  -- The steps before the attestations keep the proposer and the pending attestations.
  have header : HeadKept state headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact HeadKept.of_eq rfl rfl rfl rfl rfl
  have randao : HeadKept headed revealed := by
    have mixes := mixesKeptBut_processRandao randaoOk
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    exact ⟨⟨rfl, ActiveKept.of_validators rfl _, mixes, fun _ => rfl⟩, rfl, rfl⟩
  have vote : HeadKept revealed voted := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
    rw [← rest]
    exact HeadKept.of_eq rfl rfl rfl rfl rfl
  have head : HeadKept state slashingsDone :=
    header.trans <| randao.trans <| vote.trans <|
      (HeadKept.foldlM (fun _ _ _ ok => headKept_processProposerSlashing early ok)
        proposersOk).trans
      (HeadKept.foldlM (fun _ _ _ ok => headKept_processAttesterSlashing early ok) attestersOk)
  -- Each attestation names the proposer of the slot, which the steps before it keep.
  have recorded := foldlM_ok_invariant (fun middle : BeaconState preset fork =>
      ProposerKept state middle ∧ ∀ current, ∀ pending ∈ recentPending middle early current,
        pending ∈ recentPending state early current ∨
          pending.proposerIndex = block.proposerIndex)
    (fun middle attestation next holds ok => by
      obtain ⟨kept, listed⟩ := holds
      obtain ⟨pending, -, -, -, named, stored, -⟩ := processAttestation_records early ok
      have same : pending.proposerIndex = block.proposerIndex := by
        rw [kept.proposer beforeFulu apart, proposer] at named
        exact (Except.ok.inj named).symm
      have registry := processAttestation_registry ok
      refine ⟨kept.trans (ProposerKept.of_eq registry.1 registry.2
        (frame_processAttestation ok).slot), fun current other member => ?_⟩
      have lists := recordPendingAttestation_ok stored
      generalize (attestation.data.target.epoch == getCurrentEpoch middle) = target at lists
      cases target <;> cases current <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at lists <;>
        obtain ⟨pushed, rest⟩ := lists <;>
        simp only [recentPending, Bool.false_eq_true, ↓reduceIte] at member listed ⊢
      · rw [pushed] at member
        rcases Array.mem_push.mp member with old | rfl
        · exact listed false other old
        · exact .inr same
      · have kept := congrArg (fun s => (s.currentEpochAttestations early).data) rest
        simp only at kept
        rw [kept] at member
        exact listed true other member
      · have kept := congrArg (fun s => (s.previousEpochAttestations early).data) rest
        simp only at kept
        rw [kept] at member
        exact listed false other member
      · rw [pushed] at member
        rcases Array.mem_push.mp member with old | rfl
        · exact listed true other old
        · exact .inr same)
    ⟨head.toProposerKept, fun current other member => by
      left
      cases current <;> simpa [recentPending, head.previous, head.current] using member⟩
    attestedOk
  -- The deposits and exits after them keep the pending attestations.
  have tail : HeadKept deposited exited ∧ ∀ current,
      recentPending deposited early current = recentPending attested early current := by
    refine ⟨HeadKept.foldlM (fun _ _ _ ok => headKept_processVoluntaryExit ok) exitsOk,
      fun current => ?_⟩
    have frame := foldlM_ok_invariant (PendingFrame attested)
      (fun _ _ _ holds ok => holds.trans (pendingFrame_processDeposit early ok))
      (PendingFrame.refl _) depositedOk
    cases current <;> simp [recentPending, frame.previousPending early, frame.currentPending early]
  intro pending member
  have : recentPending exited early current = recentPending attested early current := by
    rw [← tail.2 current]
    cases current <;> simp [recentPending, tail.1.previous, tail.1.current]
  rw [this] at member
  exact recorded.2 current pending member

/-- The proposer of a block step at a state of an epoch or later, and nothing for a slot step. -/
private def Step.proposerFrom (epoch : Epoch) {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : List Nat :=
  if epoch ≤ getCurrentEpoch x.state then
    match step with
    | .slot _ => []
    | .block _ signed _ _ => [signed.message.proposerIndex.toNat]
  else []

/-- The proposers of the block steps of a run at states of an epoch or later, in order. -/
private def Run.proposersFrom {g : ForkedBeaconState preset} (epoch : Epoch) :
    {y : ForkedBeaconState preset} → Run config checks g y → List Nat
  | _, .nil => []
  | _, .snoc pre step => Run.proposersFrom epoch pre ++ step.proposerFrom epoch

/-- A run has at most one block step for each slot from the first slot of an epoch on.

A block step spends the slot of its state, as `Run.blocks_le_slots` counts. -/
private theorem Run.proposersFrom_length (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g y : ForkedBeaconState preset} (run : Run config checks g y) (epoch : Epoch) :
    (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ y.state.slot.toNat →
      (run.proposersFrom epoch).length +
          (if y.state.latestBlockHeader.slot < y.state.slot then 1 else 0) +
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ y.state.slot.toNat + 1) ∧
    (y.state.slot.toNat < epoch.toNat * preset.SLOTS_PER_EPOCH.toNat →
      run.proposersFrom epoch = []) := by
  induction run with
  | nil =>
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    simp only [Run.proposersFrom, List.length_nil]
    split <;> omega
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      have moved : last.state.slot.toNat = middle.state.slot.toNat + 1 :=
        (congrArg UInt64.toNat (processUpgrades_slot upgraded)).trans (advanceSlot_slot advancedOk)
      have nothing : (Step.slot (config := config) (checks := checks) ok).proposerFrom epoch =
          [] := by
        simp only [Step.proposerFrom]
        split <;> rfl
      simp only [Run.proposersFrom, nothing, List.append_nil]
      by_cases low : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ middle.state.slot.toNat
      · have := ih.1 low
        refine ⟨fun _ => ?_, fun _ => by omega⟩
        split at this <;> split <;> omega
      · rw [ih.2 (by omega)]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        simp only [List.length_nil]
        split <;> omega
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      obtain ⟨atSlot, newer, -⟩ := processBlock_parentRoot processed
      obtain ⟨parented, headed, -, headerOk, kept⟩ := processBlock_header_split processed
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
      have slot := (frame_processBlock processed).slot
      -- The state before the block has a free slot, which the block spends.
      have free : before.latestBlockHeader.slot < before.slot := atSlot ▸ newer
      have spent : ¬ after.latestBlockHeader.slot < after.slot := by
        rw [kept, slot, ← atSlot]
        exact UInt64.lt_irrefl _
      have slotNat : after.slot.toNat = before.slot.toNat := congrArg UInt64.toNat slot
      -- The block counts exactly when its state is in the epoch or later.
      have late : epoch ≤ getCurrentEpoch before ↔
          epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ before.slot.toNat := by
        rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, Nat.le_div_iff_mul_le positive]
      simp only [Run.proposersFrom, Step.proposerFrom, spent, ↓reduceIte] at ih ⊢
      simp only [free, ↓reduceIte] at ih
      by_cases counted : epoch ≤ getCurrentEpoch before
      · have low := late.mp counted
        simp only [counted, ↓reduceIte, List.length_append, List.length_singleton]
        exact ⟨fun _ => by have := ih.1 low; omega, fun high => by omega⟩
      · simp only [counted, ↓reduceIte, List.append_nil]
        have high : before.slot.toNat < epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
          have := mt late.mpr counted
          omega
        rw [ih.2 high]
        exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- The proposers that a step of a run names are among those of the run. -/
private theorem Run.proposerFrom_subset {g y : ForkedBeaconState preset}
    {run : Run config checks g y} (epoch : Epoch) {u v : ForkedBeaconState preset}
    {step : Step config checks u v} (member : run.Contains step) :
    ∀ proposer ∈ step.proposerFrom epoch, proposer ∈ run.proposersFrom epoch := by
  induction member with
  | last pre step => exact fun _ inside => List.mem_append_right _ inside
  | earlier member next ih => exact fun _ inside => List.mem_append_left _ (ih _ inside)

/-- Each block step at a state of an epoch or later names its proposer among those of the run. -/
private theorem Run.mem_proposersFrom {g y : ForkedBeaconState preset}
    {run : Run config checks g y} (epoch : Epoch) {fork : Fork} {x t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, x⟩ = false}
    {ok : applySignedBlock config checks engine x signed true = .ok t}
    (member : run.Contains (.block engine signed due ok)) (late : epoch ≤ getCurrentEpoch x) :
    signed.message.proposerIndex.toNat ∈ run.proposersFrom epoch :=
  Run.proposerFrom_subset epoch member _ (by simp [Step.proposerFrom, late])

/-- An upgrade reaches Altair or a later fork. -/
private theorem altair_le_of_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) : .altair ≤ post.val.fork := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed <;>
    first
      | (obtain ⟨_, -, rfl⟩ := computed; dsimp only; decide)

/-- Along a run from genesis before Altair, a pending attestation names a proposer of the run.

It is the proposer of a block at a state of the epoch of its list or later.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
private theorem Run.pending_mem_proposersFrom
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {g y : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (run : Run config checks g y) (early : y.fork < .altair) :
    ∀ current, ∀ pending ∈ recentPending y.state early current,
      pending.proposerIndex.toNat ∈ run.proposersFrom
        (if current then getCurrentEpoch y.state else getPreviousEpoch y.state) := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, computed⟩ := genesis
    intro current pending member
    rw [initializeBeaconStateFromEth1_pending computed early current] at member
    simp at member
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      -- An upgrade would reach Altair, so the slot step is one slot.
      have stays : last = ⟨middle.fork, advanced⟩ := by
        rw [processUpgrades] at upgraded
        split at upgraded
        · obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp upgraded
          exact absurd
            (Nat.le_trans (altair_le_of_upgradeNext nextOk) (processUpgrades_fork_le rest))
            (Nat.not_le_of_lt early)
        · cases upgraded
          rfl
      subst stays
      have nothing (epoch : Epoch) :
          (Step.slot (config := config) (checks := checks) ok).proposerFrom epoch = [] := by
        simp [Step.proposerFrom]
      intro current
      simp only [Run.proposersFrom, nothing, List.append_nil]
      obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advancedOk
      obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
      have stateEpoch := getCurrentEpoch_toNat middle.state
      have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
      dsimp only at afterEpoch
      unfold epochIfLast at epochedOk
      split at epochedOk
      · rename_i boundary
        -- The votes of the old current epoch become those of the previous epoch.
        have epochs := nextSlot_epoch_of_boundary sum boundary
        have previousEq : getPreviousEpoch { epoched with slot := next } =
            getCurrentEpoch middle.state := by
          apply UInt64.toNat_inj.mp
          rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
          rfl
        obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation middleEarly epochedOk
        intro pending member
        cases current
        · simp only [recentPending, Bool.false_eq_true, ↓reduceIte] at member ⊢
          rw [previousEq]
          have moved : pending ∈ recentPending middle.state middleEarly true := by
            simpa [recentPending, rotated, cachedEq] using member
          simpa using ih middleEarly true pending moved
        · simp [recentPending, emptied] at member
      · rename_i inside
        simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
        subst epochedOk
        have currentEq : getCurrentEpoch { cached with slot := next } =
            getCurrentEpoch middle.state := by
          apply UInt64.toNat_inj.mp
          rw [afterEpoch, stateEpoch]
          exact nextSlot_epoch_of_inside sum inside
        have previousEq : getPreviousEpoch { cached with slot := next } =
            getPreviousEpoch middle.state := by
          unfold getPreviousEpoch
          rw [currentEq]
        intro pending member
        rw [currentEq, previousEq]
        have kept : pending ∈ recentPending middle.state middleEarly current := by
          cases current <;> simpa [recentPending, cachedEq] using member
        exact ih middleEarly current pending kept
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      have slot := (frame_processBlock processed).slot
      have currentEq : getCurrentEpoch after = getCurrentEpoch before := by
        simp only [getCurrentEpoch, slot]
      have previousEq : getPreviousEpoch after = getPreviousEpoch before := by
        unfold getPreviousEpoch
        rw [currentEq]
      intro current pending member
      simp only at member ⊢
      rw [currentEq, previousEq]
      simp only [Run.proposersFrom, List.mem_append]
      rcases processBlock_pendingProposer early apart processed current pending member with
        old | named
      · exact .inl (ih early current pending old)
      · -- The proposer of the block counts, since its state is in the epoch of the list or later.
        right
        have late : (if current then getCurrentEpoch before else getPreviousEpoch before) ≤
            getCurrentEpoch before := by
          cases current
          · exact getPreviousEpoch_le before
          · exact UInt64.le_refl _
        simp [Step.proposerFrom, late, named]

/-- Before Altair, the proposers that the last epoch boundary can pay number at most two epochs.

The end of an epoch pays the proposer that each pending attestation of the previous epoch names.

That proposer included the attestation in a block of the previous epoch or of the current one.

So one set holds those proposers and those of the blocks of the run in both epochs.

A run has at most one block for each slot, so the set has at most two epochs of slots.

An attestation names the proposer of its block, since the steps before it keep that proposer.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes, and an epoch must have a slot. -/
theorem Run.previousAttestation_proposers {g z : ForkedBeaconState preset}
    (run : Run config checks g z) (genesis : Genesis (config := config) (checks := checks) g)
    (before : z.fork < .altair) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∃ proposers : Finset ℕ, proposers.card ≤ 2 * preset.SLOTS_PER_EPOCH.toNat ∧
      (∀ a ∈ (z.state.previousEpochAttestations before).data.toList,
        a.proposerIndex.toNat ∈ proposers) ∧
      ∀ {f : Fork} {x t : BeaconState preset f} (engine : ExecutionEngine preset f)
        (signed : SignedBeaconBlock preset f) (due : upgradeDue config ⟨f, x⟩ = false)
        (ok : applySignedBlock config checks engine x signed true = .ok t),
        run.Contains (.block engine signed due ok) →
        getPreviousEpoch z.state ≤ getCurrentEpoch x →
        signed.message.proposerIndex.toNat ∈ proposers := by
  refine ⟨(run.proposersFrom (getPreviousEpoch z.state)).toFinset, ?_,
    fun a member => List.mem_toFinset.mpr ?_,
    fun engine signed due ok member late =>
      List.mem_toFinset.mpr (Run.mem_proposersFrom _ member late)⟩
  · -- The blocks from the first slot of the previous epoch to the slot of the state.
    refine (List.toFinset_card_le _).trans ?_
    have current := getCurrentEpoch_toNat z.state
    have previous := getPreviousEpoch_toNat z.state
    have divided := Nat.div_add_mod z.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have remainder := Nat.mod_lt z.state.slot.toNat positive
    generalize z.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = epoch at current divided
    obtain ⟨count, -⟩ := run.proposersFrom_length positive (getPreviousEpoch z.state)
    rw [previous, current] at count
    rcases epoch with _ | epoch
    · have := count (by simp)
      simp only [Nat.zero_sub, Nat.zero_mul, Nat.mul_zero] at this divided
      split at this <;> omega
    · simp only [Nat.add_sub_cancel, Nat.mul_succ] at count divided
      rw [Nat.mul_comm] at count
      have := count (by omega)
      split at this <;> omega
  · have listed := Run.pending_mem_proposersFrom apart genesis run before false a
      (by simpa [recentPending] using member)
    simpa using listed

end EthLib.Consensus
