module

public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Registry identity through transitions

Existing public keys remain at their positions, and a deposit appends only a fresh key.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

def validatorKeys {fork : Fork} (s : BeaconState preset fork) : List BLSPubkey :=
  s.validators.data.toList.map (·.pubkey)

/-- Keys form an unchanged prefix, and new keys do not duplicate earlier ones. -/
structure RegistryIdentity {fork fork' : Fork} (s : BeaconState preset fork)
    (t : BeaconState preset fork') : Prop where
  kept : validatorKeys s <+: validatorKeys t
  unique : (validatorKeys s).Nodup → (validatorKeys t).Nodup

namespace RegistryIdentity

theorem refl (s : BeaconState preset fork) : RegistryIdentity s s :=
  ⟨List.prefix_refl _, id⟩

theorem trans {f₁ f₂ f₃ : Fork} {s : BeaconState preset f₁}
    {t : BeaconState preset f₂} {u : BeaconState preset f₃}
    (one : RegistryIdentity s t) (two : RegistryIdentity t u) : RegistryIdentity s u :=
  ⟨one.kept.trans two.kept, two.unique ∘ one.unique⟩

theorem of_keys {fork' : Fork} {s : BeaconState preset fork} {t : BeaconState preset fork'}
    (same : validatorKeys t = validatorKeys s) : RegistryIdentity s t := by
  constructor <;> rw [same]
  · exact List.prefix_refl _
  · exact id

theorem of_validators {fork' : Fork} {s : BeaconState preset fork}
    {t : BeaconState preset fork'} (same : t.validators.data = s.validators.data := by rfl) :
    RegistryIdentity s t := of_keys (by simp only [validatorKeys, same])

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x t, step s x = .ok t → RegistryIdentity s t) {items : List α}
    (ok : items.foldlM step state = .ok after) : RegistryIdentity state after :=
  foldlM_ok_invariant (RegistryIdentity state)
    (fun _ _ _ before computed => before.trans (keeps _ _ _ computed)) (refl state) ok

theorem setValidatorAt {position : Nat} {v old : Validator}
    (found : getValidatorAt state position = .ok old) (key : v.pubkey = old.pubkey)
    (set : state.setValidatorAt position v = .ok after) : RegistryIdentity state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  apply of_keys
  simp only [validatorKeys, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set, List.map_set]
  rw [key, ← oldEq]
  have atKey : (state.validators.data.toList.map (·.pubkey))[position]'(by simpa using inside) =
      state.validators.data[position].pubkey := by simp
  rw [← atKey]
  exact List.set_getElem_self _

theorem setValidator {index : ValidatorIndex} {v old : Validator}
    (found : getValidator state index = .ok old) (key : v.pubkey = old.pubkey)
    (set : state.setValidator index v = .ok after) : RegistryIdentity state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) key
    (by rwa [← setValidator_eq_setValidatorAt])

theorem increaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state index amount = .ok after) :
    RegistryIdentity state after :=
  of_validators (congrArg (·.data) (increaseBalance_validators ok))

theorem decreaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state index amount = .ok after) :
    RegistryIdentity state after :=
  of_validators (congrArg (·.data) (decreaseBalance_validators ok))

theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have same := (exitQueue_validators queue).1
    exact (of_validators (congrArg (·.data) same)).trans
      (setValidator (by rw [getValidator_of_validators_eq same]; exact found) (by rfl) set)

theorem slashValidator {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : Consensus.slashValidator config state index whistleblower = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (initiateValidatorExit exited).trans (setValidator found (by rfl) set)
  have second := (of_validators (s := marked) (t := { marked with slashings })).trans
    ((decreaseBalance lowered).trans ((increaseBalance raised).trans (increaseBalance paid)))
  apply (first.trans second).trans
  split <;> exact of_validators

theorem append {v : Validator} (added : after.validators.data = state.validators.data.push v)
    (fresh : v.pubkey ∉ validatorKeys state) : RegistryIdentity state after := by
  have keys : validatorKeys after = validatorKeys state ++ [v.pubkey] := by
    simp [validatorKeys, added]
  constructor
  · rw [keys]
    exact List.prefix_append _ _
  · intro unique
    simp only [keys, List.nodup_append]
    refine ⟨unique, by simp, ?_⟩
    intro a member b equal same
    have eq : b = v.pubkey := List.mem_singleton.mp equal
    exact fresh (eq ▸ same ▸ member)

theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · rename_i absent
    split at ok
    · cases ok; exact refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · apply append (addValidatorToRegistry_validators_eq_push ok)
      -- The failed lookup supplies freshness; the append helper alone does not.
      simp only [Array.findIdx?_eq_none_iff, beq_eq_false_iff_ne] at absent
      simpa [validatorKeys, List.mem_map, getValidatorFromDeposit] using absent
    · cases ok; exact refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact increaseBalance ok

theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : RegistryIdentity state after := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · rename_i absent
      simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        apply (append (addValidatorToRegistry_validators_eq_push added) ?_).trans
          (of_validators (s := middle))
        simp only [Array.findIdx?_eq_none_iff, beq_eq_false_iff_ne] at absent
        simpa [validatorKeys, List.mem_map, getValidatorFromDeposit] using absent
      · cases ok; exact refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact of_validators
  · exact applyPendingDeposit ok

theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_validators (s := state)
    (t := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

theorem genesisDeposit {before : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (ok : Consensus.genesisDeposit config checks before leaves state entry = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.genesisDeposit, bind_ok_iff] at ok
  obtain ⟨root, _, deposited⟩ := ok
  exact (of_validators (s := state)
    (t := { state with
      eth1Data := fun _ => { state.eth1Data before with depositRoot := root } })).trans
    (processDeposit deposited)

theorem activateAtGenesis {index : Nat}
    (ok : Consensus.activateAtGenesis state index = .ok after) : RegistryIdentity state after := by
  simp only [Consensus.activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, _, _, set⟩ := ok
  apply setValidatorAt found _ set
  split <;> rfl

theorem genesis {hash : Hash32} {time : UInt64} {deposits : Array Deposit}
    (ok : initializeBeaconStateFromEth1 config checks hash time deposits = .ok after) :
    (validatorKeys after).Nodup := by
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    rfl⟩ := initializeBeaconStateFromEth1_ok ok
  have first := foldlM (fun _ _ _ ok => genesisDeposit ok) depositedOk
  have second := foldlM (fun _ _ _ ok => activateAtGenesis ok) activatedOk
  exact (first.trans second).unique (by simp [validatorKeys, emptyGenesisState])

theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [Consensus.processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact of_validators

theorem requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {v : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index v amount owed = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure]
    at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact of_validators (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact refl _

theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact initiateValidatorExit (liftAccessor_ok.mp ok)
    | exact requestPartialWithdrawal ok

theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_validators
  · cases ok; exact refl _

theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (setValidator found (by rfl) set).trans (queueExcessActiveBalance queued)

theorem queueConsolidation {electra : .pectra ≤ fork} {sourceIndex targetIndex : ValidatorIndex}
    {source : Validator} (found : state.validators.data[sourceIndex.toNat]? = some source)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : RegistryIdentity state after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawal, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  have first : RegistryIdentity state churnedState := of_validators (by rw [validators])
  have found' : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  exact first.trans ((setValidator found' (by rfl) set).trans of_validators)

theorem processConsolidationRequest {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | exact queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) ok

theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans
    ((foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations))

theorem applyWithdrawal {withdrawal : Withdrawal}
    (ok : Consensus.applyWithdrawal state withdrawal = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_validators
  · exact decreaseBalance ok

theorem applyExpectedWithdrawals {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (ok : Consensus.applyExpectedWithdrawals state capella expected = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have one : RegistryIdentity state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM (fun _ _ _ ok => applyWithdrawal ok) appliedOk
  have indexedStep : RegistryIdentity applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact of_validators
    · cases indexedOk; exact refl _
  have queued : ∀ s : BeaconState preset fork,
      RegistryIdentity s (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals s gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount else s) := by
    intro s
    split <;> exact of_validators
  have partials : ∀ s : BeaconState preset fork,
      RegistryIdentity s (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals s electra expected.processedPartialWithdrawalsCount
      else s) := by
    intro s
    split <;> exact of_validators
  have swept : ∀ s : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex s gloas expected.processedBuildersSweepCount
      else pure s) = .ok finished → RegistryIdentity s finished := by
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
  have lastStep : RegistryIdentity finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last; exact of_validators
  exact one.trans (indexedStep.trans ((queued _).trans ((partials _).trans
    ((swept _ sweptOk).trans lastStep))))

theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    RegistryIdentity state after := by
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

theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator found (by rfl) set

theorem processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionPayload config engine state body bellatrix = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact of_validators

theorem processBuilderDepositRequest {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (ok : Consensus.processBuilderDepositRequest config checks state gloas request = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processBuilderDepositRequest addBuilderToRegistry at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first | (cases ok; done) | (cases ok; exact of_validators)

theorem processBuilderExitRequest {gloas : .glamsterdam ≤ fork} {request : BuilderExitRequest}
    (ok : Consensus.processBuilderExitRequest config state gloas request = .ok after) :
    RegistryIdentity state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · exact refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_validators

theorem processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (ok : Consensus.processParentExecutionPayload config checks state gloas body = .ok after) :
    RegistryIdentity state after := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact refl _
  · have first : RegistryIdentity state settled := by
      rw [settleParentPayment_eq settledOk]
      exact of_validators
    exact first.trans <|
      (foldlM (fun _ _ _ ok => processDepositRequest ok) depositsOk).trans <|
      (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawalsOk).trans <|
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidationsOk).trans <|
      (foldlM (fun _ _ _ ok => processBuilderDepositRequest ok) buildersOk).trans <|
      (foldlM (fun _ _ _ ok => processBuilderExitRequest ok) exitsOk).trans of_validators

theorem processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : Consensus.processExecutionPayloadBid config checks state gloas signed = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact of_validators
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact of_validators

theorem processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : Consensus.processBlockExecution config checks engine state body bellatrix = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    exact (processWithdrawals withdrawn).trans (processExecutionPayloadBid bid)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (processWithdrawals withdrawn).trans (processExecutionPayload paid)
  · dsimp only at ok
    split at ok
    · exact processExecutionPayload ok
    · cases ok; exact refl _

theorem processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : Consensus.processSyncAggregate config checks state altair aggregate = .ok after) :
    RegistryIdentity state after := by
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

theorem processBlockHeader {block : BeaconBlock preset fork}
    (ok : Consensus.processBlockHeader state block = .ok after) : RegistryIdentity state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact of_validators

theorem processRandao {body : BeaconBlockBody preset fork}
    (ok : Consensus.processRandao config checks state body = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact of_validators

theorem processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : Consensus.processEth1Data before state body = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  rw [← rest]
  exact of_validators

theorem processProposerSlashing {slashing : ProposerSlashing}
    (ok : Consensus.processProposerSlashing config checks state slashing = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator slashed

theorem processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (ok : Consensus.processAttesterSlashing config checks state slashing = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => RegistryIdentity state step.1)
    (fun step _ next before ok => before.trans ?_)
    (show RegistryIdentity state (state, false).1 from refl state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slashValidator slashed
  · cases ok; exact refl _

theorem processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : Consensus.processAttestation config checks state parentSlot attestation = .ok after) :
    RegistryIdentity state after :=
  of_validators (by rw [(processAttestation_registry ok).1])

theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit exited

theorem processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : Consensus.processOperations config checks state body parentSlot = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processOperations at ok
  split at ok
  · unfold processOperationsGloas at ok
    simp only [bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, _, attesters, _,
      attestations, _, exits, _, changes, paid⟩ := ok
    exact (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposers).trans <|
      (foldlM (fun _ _ _ ok => processAttesterSlashing ok) attesters).trans <|
      (foldlM (fun _ _ _ ok => processAttestation ok) attestations).trans <|
      (foldlM (fun _ _ _ ok => processVoluntaryExit ok) exits).trans <|
      (foldlM (fun _ _ _ ok => processBlsToExecutionChange ok) changes).trans <|
      foldlM (fun _ _ _ ok => by rw [processPayloadAttestation_eq ok]; exact refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changesOk, requestsOk⟩ := ok
  have changes : RegistryIdentity exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact foldlM (fun _ _ _ ok => processBlsToExecutionChange ok) changesOk
    · cases changesOk; exact refl _
  have requests : RegistryIdentity changed after := by
    split at requestsOk
    · exact processExecutionRequests requestsOk
    · cases requestsOk; exact refl _
  exact (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposers).trans <|
    (foldlM (fun _ _ _ ok => processAttesterSlashing ok) attesters).trans <|
    (foldlM (fun _ _ _ ok => processAttestation ok) attestations).trans <|
    (foldlM (fun _ _ _ ok => processDeposit ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processVoluntaryExit ok) exits).trans <| changes.trans requests

theorem processBlock {block : BeaconBlock preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := ok
    have paidStep : RegistryIdentity state paid := by
      split at paidOk
      · exact processParentExecutionPayload paidOk
      · cases paidOk; exact refl _
    have execution : RegistryIdentity headed executed := by
      split at executedOk
      · exact processBlockExecution executedOk
      · cases executedOk; exact refl _
    have vote : RegistryIdentity revealed voted := by
      split at votedOk
      · exact processEth1Data votedOk
      · cases votedOk; exact refl _
    exact paidStep.trans <| (processBlockHeader headedOk).trans <| execution.trans <|
      (processRandao revealedOk).trans <| vote.trans <|
      (processOperations operatedOk).trans (processSyncAggregate synced)
  simp only [bind_ok_iff] at ok
  obtain ⟨_, header, _, randao, _, eth1, operations⟩ := ok
  exact (processBlockHeader header).trans <| (processRandao randao).trans <|
    (processEth1Data eth1).trans (processOperations operations)

theorem processRewardsAndPenalties
    (ok : Consensus.processRewardsAndPenalties config state = .ok after) :
    RegistryIdentity state after := by
  have deltas {s t : BeaconState preset fork} {rewards penalties : Array Gwei} {index : Nat}
      (ok : applyDeltas rewards penalties s index = .ok t) : RegistryIdentity s t := by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (increaseBalance raised).trans (decreaseBalance lowered)
  have allDeltas {s t : BeaconState preset fork} {ds : Array Gwei × Array Gwei}
      (ok : applyAllDeltas s ds = .ok t) : RegistryIdentity s t :=
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

theorem updateRegistryEntry {index : Nat}
    (ok : Consensus.updateRegistryEntry config state index = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have key : queued.pubkey = v.pubkey := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      rfl
    · cases queue; rfl
  have first := setValidatorAt found key set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans (initiateValidatorExit exited)
  · cases ok; exact first

theorem activateValidator {index : ValidatorIndex}
    (ok : Consensus.activateValidator state index = .ok after) : RegistryIdentity state after := by
  simp only [Consensus.activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  exact setValidator found (by rfl) set

theorem updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (ok : Consensus.updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact setValidatorAt found (by rfl) set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact initiateValidatorExit exited
  split at ok
  · exact setValidatorAt found (by rfl) (liftAccessor_ok.mp ok)
  · cases ok; exact refl _

theorem processRegistryUpdates
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM (fun _ _ _ ok => updateRegistryEntryElectra ok) ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, updated, activated⟩ := ok
    exact (foldlM (fun _ _ _ ok => updateRegistryEntry ok) updated).trans
      (foldlM (fun _ _ _ ok => activateValidator ok) activated)

theorem applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (ok : Consensus.applySlashingPenalty state total adjusted index = .ok after) :
    RegistryIdentity state after := by
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

theorem applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (ok : Consensus.applySlashingPenaltyElectra state perIncrement index = .ok after) :
    RegistryIdentity state after := by
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

theorem processSlashings (ok : Consensus.processSlashings state = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact foldlM (fun _ _ _ ok => applySlashingPenaltyElectra ok) applied
  · exact foldlM (fun _ _ _ ok => applySlashingPenalty ok) ok

theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    RegistryIdentity state after := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact setValidatorAt found (by rfl) set

theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass → RegistryIdentity state pass.1.state
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

theorem processPendingBalances
    (ok : Consensus.processPendingBalances config checks state = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processPendingBalances at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨middle, deposited, consolidated⟩ := ok
    have deposits : RegistryIdentity state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals exact (passPendingDeposits ‹_›).trans of_validators
    exact deposits.trans
      (of_validators (by rw [(processPendingConsolidations_kept consolidated).1]))
  · cases ok; exact refl _

theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    RegistryIdentity state after :=
  of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

theorem processInactivityUpdates {altair : .altair ≤ fork}
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processInactivityUpdates at ok
  split at ok
  · cases ok; exact refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact of_validators

theorem processEth1DataReset {before : fork < .hegota}
    (ok : Consensus.processEth1DataReset before state = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact of_validators

theorem processSlashingsReset (ok : Consensus.processSlashingsReset state = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
  exact of_validators

theorem processRandaoMixesReset (ok : Consensus.processRandaoMixesReset state = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
  exact of_validators

theorem processHistoricalRootsUpdate
    (ok : Consensus.processHistoricalRootsUpdate state = .ok after) :
    RegistryIdentity state after := by
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

theorem processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (ok : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact of_validators

theorem epochTail {altair : .altair ≤ fork} {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : RegistryIdentity rooted after := by
  have syncedStep : RegistryIdentity (processParticipationFlagUpdates rooted altair) synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact of_validators
  have lookedStep : RegistryIdentity synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact of_validators
    · cases lookedOk; exact refl _
  have windowedStep : RegistryIdentity looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact of_validators
    · cases windowed; exact refl _
  exact (of_validators (s := rooted)).trans <| syncedStep.trans <| lookedStep.trans windowedStep

theorem processEpochAltair {altair : .altair ≤ fork}
    (ok : Consensus.processEpochAltair config checks state altair = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processEpochAltair at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, justified, _, scored, _, rewarded, _, registered, slashedState, slashed,
    reset, resetOk, pending, pendingOk, paid, paidOk, _, balanced, _, cleared,
    mixed, mixedOk, ok⟩ := ok
  have resetStep : RegistryIdentity slashedState reset := by
    split at resetOk
    · exact processEth1DataReset resetOk
    · cases resetOk; exact refl _
  have paidStep : RegistryIdentity pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact of_validators
    · cases paidOk; exact refl _
  have first : RegistryIdentity state mixed :=
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

theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.processEpoch at ok
  split at ok
  · exact processEpochAltair ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, justified, _, rewarded, _, registered, _, slashed, _, reset, _, balanced,
      _, cleared, _, mixed, rooted, rootedOk, rotated⟩ := ok
    have last : RegistryIdentity rooted after := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; exact of_validators
    exact (processJustificationAndFinalization justified).trans <|
      (processRewardsAndPenalties rewarded).trans <| (processRegistryUpdates registered).trans <|
      (processSlashings slashed).trans <| (processEth1DataReset reset).trans <|
      (processEffectiveBalanceUpdates balanced).trans <| (processSlashingsReset cleared).trans <|
      (processRandaoMixesReset mixed).trans <| (processHistoricalRootsUpdate rootedOk).trans last

theorem advanceSlot (ok : Consensus.advanceSlot config checks state = .ok after) :
    RegistryIdentity state after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : RegistryIdentity state cached := of_validators (by rw [cachedEq])
  have second : RegistryIdentity cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch epochedOk
    · cases epochedOk; exact refl _
  exact (first.trans second).trans of_validators

theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    RegistryIdentity state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_validators (s := state)).trans <|
    (setValidator (by exact found) (by rfl) set₂).trans of_validators

theorem queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (ok : Consensus.queueCompoundingExcess state electra index = .ok after) :
    RegistryIdentity state after := by
  unfold Consensus.queueCompoundingExcess at ok
  split at ok
  · split at ok
    · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
    · cases ok; exact refl _
  · cases ok; exact refl _

theorem upgradeToElectra {pre : BeaconState preset .dencun} {post : BeaconState preset .pectra}
    (ok : Consensus.upgradeToElectra config pre = .ok post) : RegistryIdentity pre post := by
  simp only [Consensus.upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := ok
  exact (of_validators (s := pre)).trans <|
    (foldlM (fun _ _ _ ok => queuePreActivation ok) queued).trans
      (foldlM (fun _ _ _ ok => queueCompoundingExcess ok) compounded)

theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    RegistryIdentity pre.state post.val.state := by
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

theorem chainStep {first last : ForkedBeaconState preset}
    (step : ChainStep config checks first last) :
    RegistryIdentity first.state last.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have rest := processUpgrades_induction
      (property := fun post => RegistryIdentity advanced post.state)
      (fun before ok => before.trans (upgradeNext ok)) (refl advanced) upgrades
    exact (advanceSlot slotOk).trans rest
  | block engine signed validate ok =>
    exact processBlock (applySignedBlock_ok ok).2.1

end RegistryIdentity
end EthLib.Consensus
