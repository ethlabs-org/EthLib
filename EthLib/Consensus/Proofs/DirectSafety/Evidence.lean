module

public import EthLib.Consensus.Proofs.DirectSafety.Fields
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Slashed validators come from evidence on the selected history

A slashed flag in a reachable registry must originate in a slashing operation of the run.

The walk follows the state transition operation by operation; no abstract protocol is an input.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Slashing operations carry evidence even when their votes were not included as attestations. -/
def _root_.EthLib.Consensus.Step.SlashingEvidence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (key : BLSPubkey) : Prop :=
  match step with
  | .slot _ => False
  | .block _ signed _ _ =>
    (∃ sl ∈ signed.message.body.proposerSlashings.data.toList, ∃ v,
      x.state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some v ∧
      v.pubkey = key) ∨
    (∃ sl ∈ signed.message.body.attesterSlashings.data.toList, ∃ i ∈ slashingIndices sl, ∃ v,
      x.state.validators.data[i.toNat]? = some v ∧ v.pubkey = key)

def _root_.EthLib.Consensus.Run.SlashingEvidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (key : BLSPubkey) : Prop :=
  ∃ x y, ∃ step : Step config checks x y, run.Contains step ∧ step.SlashingEvidence key

-- The predicate follows public keys, so registry growth does not require a fixed index set.
private def SlashedBacked (evidence : BLSPubkey → Prop) {fork : Fork}
    (state : BeaconState preset fork) : Prop :=
  ∀ v ∈ state.validators.data.toList, v.slashed = true → evidence v.pubkey

-- Ordinary mutators cannot introduce a slashed key that lacked evidence before the mutation.
private def SlashedKept {fork post : Fork} (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ evidence, SlashedBacked evidence state → SlashedBacked evidence after

private theorem SlashedKept.refl {fork : Fork} (state : BeaconState preset fork) :
    SlashedKept state state := fun _ => id

private theorem SlashedKept.trans {f₁ f₂ f₃ : Fork} {s : BeaconState preset f₁}
    {t : BeaconState preset f₂} {u : BeaconState preset f₃}
    (one : SlashedKept s t) (two : SlashedKept t u) : SlashedKept s u :=
  fun evidence backed => two evidence (one evidence backed)

private theorem SlashedKept.of_validators {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (same : after.validators.data = state.validators.data :=
      by rfl) : SlashedKept state after := by
  intro evidence backed
  simpa only [SlashedBacked, same] using backed

private theorem SlashedKept.foldlM {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x t, step s x = .ok t → SlashedKept s t)
    {items : List α} {state after : BeaconState preset fork}
    (ok : items.foldlM step state = .ok after) : SlashedKept state after :=
  foldlM_ok_invariant (SlashedKept state)
    (fun _ _ _ before computed => before.trans (keeps _ _ _ computed)) (.refl state) ok

namespace SlashedKept

variable {fork : Fork} {state after : BeaconState preset fork}

private theorem setValidatorAt {position : Nat} {v old : Validator}
    (found : getValidatorAt state position = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (set : state.setValidatorAt position v = .ok after) : SlashedKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  intro evidence backed current member slashed
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set] at member
  rcases List.mem_or_eq_of_mem_set member with member | equal
  · exact backed current member slashed
  · subst current
    rw [key]
    apply backed old
    · rw [← oldEq]
      simp
    · rwa [flag] at slashed

private theorem setValidator {index : ValidatorIndex} {v old : Validator}
    (found : getValidator state index = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (set : state.setValidator index v = .ok after) : SlashedKept state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) key flag
    (by rwa [← setValidator_eq_setValidatorAt])

private theorem increaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (increaseBalance_validators ok))

private theorem decreaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (decreaseBalance_validators ok))

private theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    SlashedKept state after := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have same := (exitQueue_validators queue).1
    exact (of_validators (congrArg (·.data) same)).trans
      (setValidator (old := v) (v := { v with exitEpoch := epoch, withdrawableEpoch := withdrawal })
        (by rw [getValidator_of_validators_eq same]; exact found)
        rfl rfl set)

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v) (flag : v.slashed = false) :
    SlashedKept state after := by
  intro evidence backed current member slashed
  simp only [added, Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact backed current member slashed
  · simp [flag] at slashed

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    SlashedKept state after := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact append (addValidatorToRegistry_validators_eq_push ok) rfl
    · cases ok; exact refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact increaseBalance ok

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : SlashedKept state after := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (append (addValidatorToRegistry_validators_eq_push added) rfl).trans
          (of_validators (state := middle))
      · cases ok; exact refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact of_validators
  · exact applyPendingDeposit ok

private theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

private theorem genesisDeposit {before : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (ok : Consensus.genesisDeposit config checks before leaves state entry = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.genesisDeposit, bind_ok_iff] at ok
  obtain ⟨root, _, deposited⟩ := ok
  exact (of_validators (state := state)
    (after := { state with
      eth1Data := fun _ => { state.eth1Data before with depositRoot := root } })).trans
    (processDeposit deposited)

private theorem activateAtGenesis {index : Nat}
    (ok : Consensus.activateAtGenesis state index = .ok after) : SlashedKept state after := by
  simp only [Consensus.activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, _, _, set⟩ := ok
  apply setValidatorAt found _ _ set <;> split <;> rfl

private theorem genesis {hash : Hash32} {time : UInt64} {deposits : Array Deposit}
    (ok : initializeBeaconStateFromEth1 config checks hash time deposits = .ok after) :
    SlashedBacked (fun _ => False) after := by
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    rfl⟩ := initializeBeaconStateFromEth1_ok ok
  have first := foldlM (fun _ _ _ ok => genesisDeposit ok) depositedOk
  have second := foldlM (fun _ _ _ ok => activateAtGenesis ok) activatedOk
  exact (first.trans second) (fun _ => False) (by simp [SlashedBacked, emptyGenesisState])

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    SlashedKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [Consensus.processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact of_validators

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {v : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index v amount owed = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure]
    at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact of_validators (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact refl _

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact initiateValidatorExit (liftAccessor_ok.mp ok)
    | exact requestPartialWithdrawal ok

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_validators
  · cases ok; exact refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (setValidator found (by rfl) (by rfl) set).trans (queueExcessActiveBalance queued)

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : SlashedKept state after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawal, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  have first : SlashedKept state churnedState := of_validators (by rw [validators])
  have found' : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  exact first.trans ((setValidator found' (by rfl) (by rfl) set).trans of_validators)

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | exact queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) ok

-- EIP-8282, Consensus Layer Processing: builder requests touch a separate registry.
private theorem builderDeposit {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (ok : processBuilderDepositRequest config checks state gloas request = .ok after) :
    SlashedKept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first | (cases ok; done) | (cases ok; exact of_validators)

private theorem builderExit {gloas : .glamsterdam ≤ fork} {request : BuilderExitRequest}
    (ok : processBuilderExitRequest config state gloas request = .ok after) :
    SlashedKept state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · exact refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_validators

-- EIP-7732, Beacon chain changes: requests move to the parent payload's processing.
private theorem parentPayload {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks state gloas body = .ok after) :
    SlashedKept state after := by
  rcases processParentExecutionPayload_ok ok with ⟨_, _, rfl⟩ |
    ⟨_, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, _, rfl⟩
  · exact refl _
  · have first : SlashedKept state settled := by
      rw [settleParentPayment_eq settledOk]
      exact of_validators
    exact first.trans <|
      (foldlM (fun _ _ _ ok => processDepositRequest ok) depositsOk).trans <|
      (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawalsOk).trans <|
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidationsOk).trans <|
      (foldlM (fun _ _ _ ok => builderDeposit ok) buildersOk).trans <|
      (foldlM (fun _ _ _ ok => builderExit ok) exitsOk).trans of_validators

private theorem executionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact of_validators
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact of_validators

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans
    ((foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations))

private theorem applyWithdrawal {withdrawal : Withdrawal}
    (ok : Consensus.applyWithdrawal state withdrawal = .ok after) : SlashedKept state after := by
  unfold Consensus.applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_validators
  · exact decreaseBalance ok

private theorem applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (ok : Consensus.applyExpectedWithdrawals state capella expected = .ok after) :
    SlashedKept state after := by
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have one : SlashedKept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM (fun _ _ _ ok => applyWithdrawal ok) appliedOk
  have indexedStep : SlashedKept applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact of_validators
    · cases indexedOk; exact refl _
  have queued : ∀ s : BeaconState preset fork,
      SlashedKept s (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals s gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount else s) := by
    intro s
    split <;> exact of_validators
  have partials : ∀ s : BeaconState preset fork,
      SlashedKept s (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals s electra expected.processedPartialWithdrawalsCount
      else s) := by
    intro s
    split <;> exact of_validators
  have swept : ∀ s : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex s gloas expected.processedBuildersSweepCount
      else pure s) = .ok finished → SlashedKept s finished := by
    intro s computed
    split at computed
    · unfold updateNextWithdrawalBuilderIndex at computed
      dsimp only at computed
      split at computed
      · cases computed; exact of_validators
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, rfl⟩ := computed
        exact of_validators
    · cases computed; exact refl _
  have lastStep : SlashedKept finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last; exact of_validators
  exact one.trans (indexedStep.trans ((queued _).trans ((partials _).trans
    ((swept _ sweptOk).trans lastStep))))

private theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact applyExpectedWithdrawals applied
    · cases ok; exact refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact applyExpectedWithdrawals applied

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator found (by rfl) (by rfl) set

private theorem processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : Consensus.processSyncAggregate config checks state altair aggregate = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (increaseBalance raised).trans (increaseBalance paid)
  · exact decreaseBalance (liftAccessor_ok.mp ok)

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit exited

private theorem processRewardsAndPenalties
    (ok : Consensus.processRewardsAndPenalties config state = .ok after) :
    SlashedKept state after := by
  have deltas {s t : BeaconState preset fork} {rewards penalties : Array Gwei} {index : Nat}
      (ok : applyDeltas rewards penalties s index = .ok t) : SlashedKept s t := by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (increaseBalance raised).trans (decreaseBalance lowered)
  have allDeltas {s t : BeaconState preset fork} {ds : Array Gwei × Array Gwei}
      (ok : applyAllDeltas s ds = .ok t) : SlashedKept s t :=
    foldlM (fun _ _ _ ok => deltas ok) ok
  unfold Consensus.processRewardsAndPenalties at ok
  split at ok
  · cases ok; exact refl _
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact foldlM (fun _ _ _ ok => allDeltas ok) applied
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact allDeltas applied

private theorem updateRegistryEntry {index : Nat}
    (ok : Consensus.updateRegistryEntry config state index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have fields : queued.pubkey = v.pubkey ∧ queued.slashed = v.slashed := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨rfl, rfl⟩
    · cases queue; exact ⟨rfl, rfl⟩
  have first := setValidatorAt found fields.1 fields.2 set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans (initiateValidatorExit exited)
  · cases ok; exact first

private theorem activateValidator {index : ValidatorIndex}
    (ok : Consensus.activateValidator state index = .ok after) : SlashedKept state after := by
  simp only [Consensus.activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  exact setValidator found (by rfl) (by rfl) set

private theorem updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (ok : Consensus.updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact setValidatorAt found (by rfl) (by rfl) set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact initiateValidatorExit exited
  split at ok
  · exact setValidatorAt found (by rfl) (by rfl) (liftAccessor_ok.mp ok)
  · cases ok; exact refl _

private theorem processRegistryUpdates
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM (fun _ _ _ ok => updateRegistryEntryElectra ok) ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, updated, activated⟩ := ok
    exact (foldlM (fun _ _ _ ok => updateRegistryEntry ok) updated).trans
      (foldlM (fun _ _ _ ok => activateValidator ok) activated)

private theorem applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (ok : Consensus.applySlashingPenalty state total adjusted index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
      exact decreaseBalance lowered
    · cases ok; exact refl _
  · cases ok; exact refl _

private theorem applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (ok : Consensus.applySlashingPenaltyElectra state perIncrement index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, lowered⟩ := ok
      exact decreaseBalance lowered
    · cases ok; exact refl _
  · cases ok; exact refl _

private theorem processSlashings (ok : Consensus.processSlashings state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact foldlM (fun _ _ _ ok => applySlashingPenaltyElectra ok) applied
  · exact foldlM (fun _ _ _ ok => applySlashingPenalty ok) ok

private theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    SlashedKept state after := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact setValidatorAt found (by rfl) (by rfl) set

private theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass → SlashedKept state pass.1.state
  | [], _, _, _, _, _, ok => by
    cases ok; exact refl _
  | deposit :: rest, state, processed, count, postponed, pass, ok => by
    unfold Consensus.passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; exact refl _
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; exact refl _
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)

private theorem processPendingBalances
    (ok : Consensus.processPendingBalances config checks state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processPendingBalances at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨middle, deposited, consolidated⟩ := ok
    have deposits : SlashedKept state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals exact (passPendingDeposits ‹_›).trans of_validators
    exact deposits.trans
      (of_validators (by rw [(processPendingConsolidations_kept consolidated).1]))
  · cases ok; exact refl _

private theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    SlashedKept state after :=
  of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

private theorem processInactivityUpdates {altair : .altair ≤ fork}
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processInactivityUpdates at ok
  split at ok
  · cases ok; exact refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact of_validators

private theorem processEth1DataReset {before : fork < .hegota}
    (ok : Consensus.processEth1DataReset before state = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact of_validators

private theorem processSlashingsReset (ok : Consensus.processSlashingsReset state = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
  exact of_validators

private theorem processRandaoMixesReset (ok : Consensus.processRandaoMixesReset state = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
  exact of_validators

private theorem processHistoricalRootsUpdate
    (ok : Consensus.processHistoricalRootsUpdate state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact of_validators
  · cases ok; exact refl _

private theorem processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (ok : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact of_validators

private theorem epochTail {altair : .altair ≤ fork} {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : SlashedKept rooted after := by
  have syncedStep : SlashedKept (processParticipationFlagUpdates rooted altair) synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact of_validators
  have lookedStep : SlashedKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact of_validators
    · cases lookedOk; exact refl _
  have windowedStep : SlashedKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact of_validators
    · cases windowed; exact refl _
  exact (of_validators (state := rooted)).trans <| syncedStep.trans <|
    lookedStep.trans windowedStep

private theorem processEpochAltair {altair : .altair ≤ fork}
    (ok : Consensus.processEpochAltair config checks state altair = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processEpochAltair at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, justified, _, scored, _, rewarded, _, registered, slashedState, slashed,
    reset, resetOk, pending, pendingOk, paid, paidOk, _, balanced, _, cleared,
    mixed, mixedOk, ok⟩ := ok
  have resetStep : SlashedKept slashedState reset := by
    split at resetOk
    · exact processEth1DataReset resetOk
    · cases resetOk; exact refl _
  have paidStep : SlashedKept pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact of_validators
    · cases paidOk; exact refl _
  have first : SlashedKept state mixed :=
    (processJustificationAndFinalization justified).trans <|
    (processInactivityUpdates scored).trans <| (processRewardsAndPenalties rewarded).trans <|
    (processRegistryUpdates registered).trans <| (processSlashings slashed).trans <|
    resetStep.trans <| (processPendingBalances pendingOk).trans <| paidStep.trans <|
    (processEffectiveBalanceUpdates balanced).trans <| (processSlashingsReset cleared).trans <|
    processRandaoMixesReset mixedOk
  split at ok <;> simp only [bind_ok_iff] at ok <;>
    obtain ⟨_, rooted, _, synced, _, looked, windowed⟩ := ok
  · exact first.trans ((processHistoricalSummariesUpdate rooted).trans
      (epochTail synced looked windowed))
  · exact first.trans
      ((processHistoricalRootsUpdate rooted).trans (epochTail synced looked windowed))

private theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processEpoch at ok
  split at ok
  · exact processEpochAltair ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, justified, _, rewarded, _, registered, _, slashed, _, reset, _, balanced,
      _, cleared, _, mixed, rooted, rootedOk, rotated⟩ := ok
    have last : SlashedKept rooted after := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; exact of_validators
    exact (processJustificationAndFinalization justified).trans <|
      (processRewardsAndPenalties rewarded).trans <| (processRegistryUpdates registered).trans <|
      (processSlashings slashed).trans <| (processEth1DataReset reset).trans <|
      (processEffectiveBalanceUpdates balanced).trans <| (processSlashingsReset cleared).trans <|
      (processRandaoMixesReset mixed).trans <| (processHistoricalRootsUpdate rootedOk).trans last

private theorem advanceSlot (ok : Consensus.advanceSlot config checks state = .ok after) :
    SlashedKept state after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : SlashedKept state cached := of_validators (by rw [cachedEq])
  have second : SlashedKept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch epochedOk
    · cases epochedOk; exact refl _
  exact (first.trans second).trans of_validators

private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_validators (state := state)).trans <|
    (setValidator (by exact found) (by rfl) (by rfl) set₂).trans of_validators

private theorem queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (ok : Consensus.queueCompoundingExcess state electra index = .ok after) :
    SlashedKept state after := by
  unfold Consensus.queueCompoundingExcess at ok
  split at ok
  · split at ok
    · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
    · cases ok; exact refl _
  · cases ok; exact refl _

private theorem upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra}
    (ok : Consensus.upgradeToElectra config pre = .ok post) : SlashedKept pre post := by
  simp only [Consensus.upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := ok
  exact (of_validators (state := pre)).trans <|
    (foldlM (fun _ _ _ ok => queuePreActivation ok) queued).trans
      (foldlM (fun _ _ _ ok => queueCompoundingExcess ok) compounded)

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    SlashedKept pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToAltair_spec upgraded).1
  case altair | bellatrix | shapella =>
    simp only [Consensus.upgradeNext, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact of_validators
  case dencun =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact upgradeToElectra upgraded
  case pectra =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToFulu_spec upgraded).1
  case fusaka =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToGloas_spec upgraded).1
  case glamsterdam =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact of_validators (upgradeHezeFields_lists _).1
  all_goals simp only [Consensus.upgradeNext] at ok; cases ok

private theorem advanceSlotAcross {pre post : ForkedBeaconState preset}
    (ok : Consensus.advanceSlotAcross config checks pre = .ok post) :
    SlashedKept pre.state post.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  have rest := processUpgrades_induction
    (property := fun post => SlashedKept advanced post.state)
    (fun before ok => before.trans (upgradeNext ok)) (refl advanced) upgrades
  exact (advanceSlot slotOk).trans rest

end SlashedKept

private theorem key_of_same_size {fork : Fork} {state after : BeaconState preset fork}
    (identity : RegistryIdentity state after)
    (size : after.validators.data.size = state.validators.data.size)
    {i : Nat} {v : Validator} (found : after.validators.data[i]? = some v) :
    ∃ old, state.validators.data[i]? = some old ∧ old.pubkey = v.pubkey := by
  obtain ⟨inside, equal⟩ := Array.getElem?_eq_some_iff.mp found
  have before : i < state.validators.data.size := by omega
  refine ⟨state.validators.data[i], by simp [before], ?_⟩
  have keys := identity.kept.getElem (show i < (validatorKeys state).length by
    simpa [validatorKeys] using before)
  simpa [validatorKeys, equal] using keys

private theorem slashValidator_backed {fork : Fork} {state after : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state index whistleblower = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ old, state.validators.data[index.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  obtain ⟨exited, validator, withdrawable, marked, _, _, slashings, lowered, _, _, raised, last,
    exitedOk, found, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok ok
  have oldBacked := SlashedKept.initiateValidatorExit exitedOk evidence backed
  -- Only the selected validator can acquire a flag at this write.
  have markedBacked : SlashedBacked evidence marked := by
    obtain ⟨inside, rfl⟩ := setValidator_ok markedOk
    intro v member flag
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.toList_set] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact oldBacked v member flag
    · obtain ⟨old, atOld, same⟩ := key_of_same_size
        (RegistryIdentity.initiateValidatorExit exitedOk)
        (sameSizes_initiateValidatorExit exitedOk).1 (getValidator_eq_ok_iff.mp found)
      exact same ▸ selected old atOld
  have rest : SlashedKept marked last :=
    (SlashedKept.of_validators (after := { marked with slashings })).trans <|
    (SlashedKept.decreaseBalance loweredOk).trans <|
    (SlashedKept.increaseBalance raisedOk).trans (SlashedKept.increaseBalance lastOk)
  have lastBacked := rest evidence markedBacked
  rw [done]
  split <;> exact lastBacked

private theorem proposerSlashing_backed {fork : Fork} {state after : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ old,
      state.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey) : SlashedBacked evidence after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator_backed slashed evidence backed selected

private theorem attesterSlashing_backed {fork : Fork} {state after : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ i ∈ slashingIndices slashing, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  have traverse (indices : List ValidatorIndex)
      (allowed : ∀ i ∈ indices, ∀ old,
        state.validators.data[i.toNat]? = some old → evidence old.pubkey)
      {start finish : BeaconState preset fork × Bool}
      (identity : RegistryIdentity state start.1)
      (size : start.1.validators.data.size = state.validators.data.size)
      (backed : SlashedBacked evidence start.1)
      (ok : indices.foldlM (slashIfSlashable config) start = .ok finish) :
      SlashedBacked evidence finish.1 := by
    induction indices generalizing start with
    | nil => cases ok; exact backed
    | cons index rest ih =>
      obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
      obtain ⟨s, anySlashed⟩ := start
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
      obtain ⟨_, _, first⟩ := first
      split at first
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at first
        obtain ⟨next, slashed, rfl⟩ := first
        refine ih (fun i member => allowed i (by simp [member]))
          (identity.trans (RegistryIdentity.slashValidator slashed))
          ((sameSizes_slashValidator slashed).1.trans size) ?_ tail
        apply slashValidator_backed slashed evidence backed
        intro old found
        obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
        exact same ▸ allowed index (by simp) original originalAt
      · cases first
        exact ih (fun i member => allowed i (by simp [member])) identity size backed tail
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact traverse _ selected (.refl state) rfl backed folded

private theorem fold_slashings_backed {fork : Fork} {α : Type}
    {step : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (indices : α → List ValidatorIndex)
    (identityStep : ∀ s x t, step s x = .ok t → RegistryIdentity s t)
    (sizeStep : ∀ s x t, step s x = .ok t → SameSizes s t)
    (backedStep : ∀ s x t, step s x = .ok t → ∀ evidence,
      SlashedBacked evidence s →
      (∀ i ∈ indices x, ∀ old, s.validators.data[i.toNat]? = some old → evidence old.pubkey) →
      SlashedBacked evidence t)
    {state start finish : BeaconState preset fork} (items : List α)
    (identity : RegistryIdentity state start)
    (size : start.validators.data.size = state.validators.data.size)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence start)
    (selected : ∀ x ∈ items, ∀ i ∈ indices x, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey)
    (ok : items.foldlM step start = .ok finish) : SlashedBacked evidence finish := by
  induction items generalizing start with
  | nil => cases ok; exact backed
  | cons item rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
    refine ih (identity.trans (identityStep _ _ _ first))
      ((sizeStep _ _ _ first).1.trans size) ?_
      (fun x member => selected x (by simp [member])) tail
    apply backedStep _ _ _ first evidence backed
    intro i member old found
    -- Earlier slashings preserve the index and key used by the block's original evidence.
    obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
    exact same ▸ selected item (by simp) i member original originalAt

private theorem operations_backed {fork : Fork} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (proposers : ∀ sl ∈ body.proposerSlashings.data.toList, ∀ old,
      state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey)
    (attesters : ∀ sl ∈ body.attesterSlashings.data.toList, ∀ i ∈ slashingIndices sl, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  unfold processOperations at ok
  split at ok
  · unfold processOperationsGloas at ok
    simp only [bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, proposed, proposersOk,
      slashed, attestersOk, attested, attestations, exited, exits, changed, changes, paid⟩ := ok
    have proposedBacked : SlashedBacked evidence proposed := by
      refine fold_slashings_backed (fun sl => [sl.signedHeader1.message.proposerIndex])
        (fun _ _ _ ok => RegistryIdentity.processProposerSlashing ok)
        (fun _ _ _ ok => sameSizes_processProposerSlashing ok) ?_ _ (.refl state) rfl
        evidence backed ?_ proposersOk
      · intro s sl t ok evidence backed selected
        exact proposerSlashing_backed ok evidence backed (selected _ (by simp))
      · intro sl member i inIndices
        simp only [List.mem_singleton] at inIndices
        subst i
        exact proposers sl member
    have proposedIdentity := RegistryIdentity.foldlM
      (fun _ _ _ ok => RegistryIdentity.processProposerSlashing ok) proposersOk
    have proposedSize : SameSizes state proposed :=
      (foldlM_ok_steps SameSizes SameSizes.refl SameSizes.trans
        (fun _ _ _ ok => sameSizes_processProposerSlashing ok) proposersOk).1
    have slashedBacked := fold_slashings_backed slashingIndices
      (fun _ _ _ ok => RegistryIdentity.processAttesterSlashing ok)
      (fun _ _ _ ok => sameSizes_processAttesterSlashing ok)
      (fun _ _ _ ok => attesterSlashing_backed ok) _ proposedIdentity proposedSize.1
      evidence proposedBacked attesters attestersOk
    -- Payload attestations change payment weights, not validator slashing flags.
    have rest : SlashedKept slashed after :=
      (SlashedKept.foldlM
        (fun _ _ _ ok => SlashedKept.of_validators (by rw [(processAttestation_registry ok).1]))
        attestations).trans <|
      (SlashedKept.foldlM (fun _ _ _ ok => SlashedKept.processVoluntaryExit ok) exits).trans <|
      (SlashedKept.foldlM
        (fun _ _ _ ok => SlashedKept.processBlsToExecutionChange ok) changes).trans <|
      SlashedKept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]; exact SlashedKept.of_validators) paid
    exact rest evidence slashedBacked
  simp only [bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, proposed, proposersOk, slashed, attestersOk, attested, attestations,
    deposited, deposits, exited, exits, changed, changesOk, requestsOk⟩ := ok
  have proposedBacked : SlashedBacked evidence proposed := by
    refine fold_slashings_backed (fun sl => [sl.signedHeader1.message.proposerIndex])
      (fun _ _ _ ok => RegistryIdentity.processProposerSlashing ok)
      (fun _ _ _ ok => sameSizes_processProposerSlashing ok) ?_ _ (.refl state) rfl
      evidence backed ?_ proposersOk
    · intro s sl t ok evidence backed selected
      exact proposerSlashing_backed ok evidence backed (selected _ (by simp))
    · intro sl member i inIndices
      simp only [List.mem_singleton] at inIndices
      subst i
      exact proposers sl member
  have proposedIdentity := RegistryIdentity.foldlM
    (fun _ _ _ ok => RegistryIdentity.processProposerSlashing ok) proposersOk
  have proposedSize : SameSizes state proposed := by
    exact (foldlM_ok_steps SameSizes SameSizes.refl SameSizes.trans
      (fun _ _ _ ok => sameSizes_processProposerSlashing ok) proposersOk).1
  have slashedBacked := fold_slashings_backed slashingIndices
    (fun _ _ _ ok => RegistryIdentity.processAttesterSlashing ok)
    (fun _ _ _ ok => sameSizes_processAttesterSlashing ok)
    (fun _ _ _ ok => attesterSlashing_backed ok) _ proposedIdentity proposedSize.1
    evidence proposedBacked attesters attestersOk
  have attestedKept : SlashedKept slashed attested := SlashedKept.foldlM
    (fun _ _ _ ok => SlashedKept.of_validators (by rw [(processAttestation_registry ok).1]))
    attestations
  have changes : SlashedKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact SlashedKept.foldlM
        (fun _ _ _ ok => SlashedKept.processBlsToExecutionChange ok) changesOk
    · cases changesOk; exact .refl _
  have requests : SlashedKept changed after := by
    split at requestsOk
    · exact SlashedKept.processExecutionRequests requestsOk
    · cases requestsOk; exact .refl _
  exact (attestedKept.trans <|
    (SlashedKept.foldlM (fun _ _ _ ok => SlashedKept.processDeposit ok) deposits).trans <|
    (SlashedKept.foldlM (fun _ _ _ ok => SlashedKept.processVoluntaryExit ok) exits).trans <|
    changes.trans requests) evidence slashedBacked

private theorem block_backed {fork : Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .hegota)
    (ok : processBlock config checks engine state block = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (proposers : ∀ sl ∈ block.body.proposerSlashings.data.toList, ∀ old,
      state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey)
    (attesters : ∀ sl ∈ block.body.attesterSlashings.data.toList,
      ∀ i ∈ slashingIndices sl, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  have payload {s t : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine s block.body execution = .ok t) :
      SlashedKept s t ∧ t.validators.data = s.validators.data := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    exact ⟨SlashedKept.of_validators, rfl⟩
  have execution {s t : BeaconState preset fork} {bellatrix : .bellatrix ≤ fork}
      (ok : processBlockExecution config checks engine s block.body bellatrix = .ok t) :
      SlashedKept s t ∧ t.validators.data.size = s.validators.data.size := by
    unfold processBlockExecution at ok
    split at ok
    · obtain ⟨middle, withdrawn, executed⟩ := bind_ok_iff.mp ok
      have size : t.validators.data.size = middle.validators.data.size := by
        obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok executed
        by_cases paid : 0 < (block.body.signedExecutionPayloadBid (by assumption)).message.value
        · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
          rfl
        · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure,
            Except.ok.injEq] at recordedOk
          subst recordedOk
          rfl
      exact ⟨(SlashedKept.processWithdrawals withdrawn).trans
        (SlashedKept.executionPayloadBid executed),
        size.trans (sameSizes_processWithdrawals withdrawn).1⟩
    split at ok
    · obtain ⟨middle, withdrawn, executed⟩ := bind_ok_iff.mp ok
      exact ⟨(SlashedKept.processWithdrawals withdrawn).trans (payload executed).1,
        (congrArg Array.size (payload executed).2).trans (sameSizes_processWithdrawals withdrawn).1⟩
    · dsimp only at ok
      split at ok
      · exact ⟨(payload ok).1, congrArg Array.size (payload ok).2⟩
      · cases ok; exact ⟨.refl _, rfl⟩
  have operated {s t : BeaconState preset fork} {parentSlot : Slot}
      (identity : RegistryIdentity state s)
      (size : s.validators.data.size = state.validators.data.size)
      (kept : SlashedKept state s)
      (ok : processOperations config checks s block.body parentSlot = .ok t) :
      SlashedBacked evidence t := by
    apply operations_backed ok evidence (kept evidence backed)
    · intro sl member old found
      obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
      exact same ▸ proposers sl member original originalAt
    · intro sl member i inIndices old found
      obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
      exact same ▸ attesters sl member i inIndices original originalAt
  unfold processBlock at ok
  split at ok
  · simp only [processBlockAltair, early, ↓reduceDIte,
      bind_ok_iff] at ok
    obtain ⟨parent, parentOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operatedState, operatedOk, synced⟩ := ok
    have parentFacts : SlashedKept state parent ∧
        parent.validators.data.size = state.validators.data.size ∧
        RegistryIdentity state parent := by
      split at parentOk
      · refine ⟨SlashedKept.parentPayload parentOk, ?_,
          RegistryIdentity.processParentExecutionPayload parentOk⟩
        rcases processParentExecutionPayload_ok parentOk with ⟨_, _, rfl⟩ |
          ⟨_, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk,
            consolidationsOk, buildersOk, exitsOk, _, rfl⟩
        · rfl
        · have foldSize {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
              (keeps : ∀ s x t, step s x = .ok t → t.validators.data.size = s.validators.data.size)
              {xs : List α} {s t : BeaconState preset fork} (ok : xs.foldlM step s = .ok t) :
              t.validators.data.size = s.validators.data.size :=
            foldlM_ok_invariant (fun t => t.validators.data.size = s.validators.data.size)
              (fun _ _ _ before computed => (keeps _ _ _ computed).trans before) rfl ok
          have depositSize := foldSize (fun _ _ _ ok =>
            congrArg (fun vs => vs.data.size) (processDepositRequest_ok ok).2.1) depositsOk
          have withdrawalSize := foldSize (fun _ _ _ ok =>
            (sameSizes_processWithdrawalRequest ok).1) withdrawalsOk
          have consolidationSize := foldSize (fun _ _ _ ok =>
            (sameSizes_processConsolidationRequest ok).1) consolidationsOk
          have builderSize := foldSize (fun _ _ _ ok => by
            unfold processBuilderDepositRequest addBuilderToRegistry at ok
            simp only [bind, Except.bind, pure, Except.pure] at ok
            repeat' split at ok
            all_goals first | (cases ok; done) | (cases ok; rfl)) buildersOk
          have exitSize := foldSize (fun _ _ _ ok => by
            rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
            · rfl
            · simp only [initiateBuilderExit, bind_ok_iff] at exited
              obtain ⟨_, _, _, _, set⟩ := exited
              obtain ⟨_, rfl⟩ := setBuilder_ok set
              rfl) exitsOk
          exact exitSize.trans <| builderSize.trans <| consolidationSize.trans <|
            withdrawalSize.trans <| depositSize.trans (by rw [settleParentPayment_eq settledOk])
      · cases parentOk; exact ⟨.refl _, rfl, .refl _⟩
    have headKept : SlashedKept parent headed := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact SlashedKept.of_validators
    have executionFacts : SlashedKept headed executed ∧
        executed.validators.data.size = headed.validators.data.size ∧
        RegistryIdentity headed executed := by
      split at executedOk
      · exact ⟨(execution executedOk).1, (execution executedOk).2,
          RegistryIdentity.processBlockExecution executedOk⟩
      · cases executedOk; exact ⟨.refl _, rfl, .refl _⟩
    have randaoKept : SlashedKept executed revealed := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      exact SlashedKept.of_validators
    have voteKept : SlashedKept revealed voted := by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      rw [← rest]
      exact SlashedKept.of_validators
    apply SlashedKept.processSyncAggregate synced evidence
    exact operated
      (parentFacts.2.2.trans <| (RegistryIdentity.processBlockHeader headedOk).trans <|
        executionFacts.2.2.trans <|
        (RegistryIdentity.processRandao revealedOk).trans
          (RegistryIdentity.processEth1Data votedOk))
      ((sameSizes_processEth1Data votedOk).1.trans <|
        (sameSizes_processRandao revealedOk).1.trans <|
        executionFacts.2.1.trans <| (sameSizes_processBlockHeader headedOk).1.trans parentFacts.2.1)
      (parentFacts.1.trans <| headKept.trans
        (executionFacts.1.trans (randaoKept.trans voteKept))) operatedOk
  · simp only [bind_ok_iff] at ok
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := ok
    have headKept : SlashedKept state headed := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact SlashedKept.of_validators
    have randaoKept : SlashedKept headed revealed := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      exact SlashedKept.of_validators
    have voteKept : SlashedKept revealed voted := by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      rw [← rest]
      exact SlashedKept.of_validators
    exact operated
      ((RegistryIdentity.processBlockHeader headedOk).trans <|
        (RegistryIdentity.processRandao revealedOk).trans
          (RegistryIdentity.processEth1Data votedOk))
      ((sameSizes_processEth1Data votedOk).1.trans <|
        (sameSizes_processRandao revealedOk).1.trans (sameSizes_processBlockHeader headedOk).1)
      (headKept.trans (randaoKept.trans voteKept)) operatedOk

/-- A slashed flag in a reachable registry must originate in evidence on the selected history. -/
theorem _root_.EthLib.Consensus.Run.slashed_evidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .hegota) (v : Validator)
    (member : v ∈ a.state.validators.data.toList) (slashed : v.slashed = true) :
    run.SlashingEvidence v.pubkey := by
  have backed : SlashedBacked run.SlashingEvidence a.state := by
    clear member slashed v
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      intro current member flag
      exact False.elim (SlashedKept.genesis ok current member flag)
    | snoc pre step ih =>
      rename_i middle last
      have prefixEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
      have inherited : SlashedBacked (pre.snoc step).SlashingEvidence middle.state := by
        intro current member flag
        obtain ⟨x, y, occurrence, contained, evidence⟩ := ih prefixEarly current member flag
        exact ⟨x, y, occurrence, .earlier contained step, evidence⟩
      cases step with
      | slot ok => exact SlashedKept.advanceSlotAcross ok _ inherited
      | block engine signed due ok =>
        apply block_backed early (applySignedBlock_ok ok).2.1 _ inherited
        · intro sl member old found
          exact ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inl ⟨sl, member, old, found, rfl⟩⟩
        · intro sl member i inIndices old found
          exact ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inr ⟨sl, member, i, inIndices, old, found, rfl⟩⟩
  exact backed v member slashed

end EthLib.Consensus.DirectSafety
