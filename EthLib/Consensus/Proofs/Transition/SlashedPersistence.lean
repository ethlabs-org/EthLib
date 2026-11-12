module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Persistence of slashing at a validator's registry index

Before Gloas, a successful transition cannot clear a slashed flag or remove its registry entry.

Each result follows from the frame of its step, through `of_frame` and `of_upgradeFrame`.

The frame lemmas hold at every fork.

The theorems keep an unused `fork < .glamsterdam` hypothesis, so their readers need no change.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}

/-- Each slashed validator remains slashed at the same registry index. -/
def SlashedPersistence {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v → v.slashed = true →
    ∃ w, t.validators.data[i]? = some w ∧ w.slashed = true

namespace SlashedPersistence

-- Every operation has the same fork bound, including operations that preserve all validators.
set_option linter.unusedVariables false

theorem refl (s : BeaconState preset fork) : SlashedPersistence s s :=
  fun _ v found flag => ⟨v, found, flag⟩

theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : SlashedPersistence s t) (two : SlashedPersistence t u) :
    SlashedPersistence s u := by
  intro i v found flag
  obtain ⟨w, read, slashed⟩ := one i v found flag
  exact two i w read slashed

theorem of_data {f h : Fork} {s : BeaconState preset f} {t : BeaconState preset h}
    (same : t.validators.data = s.validators.data := by rfl) : SlashedPersistence s t := by
  intro i v found flag
  exact ⟨v, same.symm ▸ found, flag⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → SlashedPersistence s t) {xs : List α}
    (ok : xs.foldlM step s = .ok t) : SlashedPersistence s t :=
  foldlM_ok_invariant (SlashedPersistence s)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl s) ok


/-- A frame never clears a slashed flag or removes a registry entry. -/
theorem of_frame (frame : Frame s t) : SlashedPersistence s t := by
  intro i v found flag
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have grown : i < t.validators.data.size := Nat.lt_of_lt_of_le inside frame.registryGrows
  have read := Array.getElem?_eq_getElem grown
  exact ⟨_, read, frame.slashed i v _ found read flag⟩

/-- An upgrade frame never clears a slashed flag or removes a registry entry. -/
theorem of_upgradeFrame {f h : Fork} {s : BeaconState preset f} {t : BeaconState preset h}
    (frame : UpgradeFrame config s t) : SlashedPersistence s t := by
  intro i v found flag
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have grown : i < t.validators.data.size := Nat.lt_of_lt_of_le inside frame.registryGrows
  have read := Array.getElem?_eq_getElem grown
  exact ⟨_, read, frame.slashed i v _ found read flag⟩

theorem increaseBalance {i : ValidatorIndex} {amount : Gwei} (early : fork < .glamsterdam)
    (ok : Consensus.increaseBalance s i amount = .ok t) : SlashedPersistence s t :=
  of_frame (frame_increaseBalance ok).toFrame

theorem decreaseBalance {i : ValidatorIndex} {amount : Gwei} (early : fork < .glamsterdam)
    (ok : Consensus.decreaseBalance s i amount = .ok t) : SlashedPersistence s t :=
  of_frame (frame_decreaseBalance ok).toFrame

theorem processProposerSlashing {slashing : ProposerSlashing} (early : fork < .glamsterdam)
    (ok : Consensus.processProposerSlashing config checks s slashing = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processProposerSlashing ok).toFrame

theorem processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (early : fork < .glamsterdam)
    (ok : Consensus.processAttesterSlashing config checks s slashing = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processAttesterSlashing ok).toFrame

theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (early : fork < .glamsterdam)
    (ok : Consensus.processDeposit config checks before s deposit = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processDeposit ok).toFrame

theorem processVoluntaryExit {signed : SignedVoluntaryExit} (early : fork < .glamsterdam)
    (ok : Consensus.processVoluntaryExit config checks s signed = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processVoluntaryExit ok).toFrame

theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (early : fork < .glamsterdam)
    (ok : Consensus.processBlsToExecutionChange config checks s signed = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processBlsToExecutionChange ok).toFrame

theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (early : fork < .glamsterdam)
    (ok : Consensus.processDepositRequest s electra request = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processDepositRequest ok).toFrame

theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (early : fork < .glamsterdam)
    (ok : Consensus.processWithdrawalRequest config s electra request = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processWithdrawalRequest ok).toFrame

theorem processConsolidationRequest {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (early : fork < .glamsterdam)
    (ok : Consensus.processConsolidationRequest config s electra request = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processConsolidationRequest ok).toFrame

theorem processRegistryUpdates (early : fork < .glamsterdam)
    (ok : Consensus.processRegistryUpdates config s = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processRegistryUpdates ok).toFrame

theorem processPendingDeposits {electra : .pectra ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processPendingDeposits config checks s electra = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processPendingDeposits ok).toFrame

theorem processPendingConsolidations {electra : .pectra ≤ fork}
    (early : fork < .glamsterdam)
    (ok : Consensus.processPendingConsolidations s electra = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processPendingConsolidations ok).toFrame

theorem processEffectiveBalanceUpdates (early : fork < .glamsterdam)
    (ok : Consensus.processEffectiveBalanceUpdates s = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processEffectiveBalanceUpdates ok).toFrame

theorem processJustificationAndFinalization (early : fork < .glamsterdam)
    (ok : Consensus.processJustificationAndFinalization s = .ok t) : SlashedPersistence s t :=
  of_data (congrArg (·.data) (processJustificationAndFinalization_keeps ok).2.2.2.2.2.1)

theorem processInactivityUpdates {altair : .altair ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processInactivityUpdates config s altair = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processInactivityUpdates ok).toFrame

theorem processEth1DataReset {before : fork < .hegota} (early : fork < .glamsterdam)
    (ok : Consensus.processEth1DataReset before s = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processEth1DataReset ok).toFrame

theorem processSlashings (early : fork < .glamsterdam)
    (ok : Consensus.processSlashings s = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processSlashings ok).toFrame

theorem processEpoch (early : fork < .glamsterdam)
    (ok : Consensus.processEpoch config checks s = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, justified, frame⟩ := processEpoch_frame ok
  exact (processJustificationAndFinalization early justified).trans (of_frame frame.toFrame)

theorem processSlot (early : fork < .glamsterdam)
    (ok : Consensus.processSlot s = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processSlot ok)

theorem advanceSlot (early : fork < .glamsterdam)
    (ok : Consensus.advanceSlot config checks s = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have second : SlashedPersistence cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch early epochedOk
    · cases epochedOk; exact refl _
  exact (processSlot early cachedOk).trans (second.trans of_data)

theorem processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processBlockExecution config checks engine s body bellatrix = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processBlockExecution ok).toFrame

theorem processBlockHeader {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    (ok : Consensus.processBlockHeader s block = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processBlockHeader ok).toFrame

theorem processRandao {body : BeaconBlockBody preset fork} (early : fork < .glamsterdam)
    (ok : Consensus.processRandao config checks s body = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processRandao ok).toFrame

theorem processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (early : fork < .glamsterdam)
    (ok : Consensus.processEth1Data before s body = .ok t) : SlashedPersistence s t :=
  of_frame (frame_processEth1Data ok).toFrame

theorem processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (early : fork < .glamsterdam)
    (ok : Consensus.processAttestation config checks s parentSlot attestation = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processAttestation ok)

theorem processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (early : fork < .glamsterdam)
    (ok : Consensus.processSyncAggregate config checks s altair aggregate = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processSyncAggregate ok).toFrame

theorem processBlock {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    (ok : Consensus.processBlock config checks engine s block = .ok t) :
    SlashedPersistence s t :=
  of_frame (frame_processBlock ok)

theorem upgradeNext {s : ForkedBeaconState preset}
    {result : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (early : result.val.fork < .glamsterdam)
    (ok : Consensus.upgradeNext config checks s = .ok result) :
    SlashedPersistence s.state result.val.state :=
  of_upgradeFrame (upgradeFrame_upgradeNext ok)

theorem processUpgrades {s t : ForkedBeaconState preset} (early : t.fork < .glamsterdam)
    (ok : Consensus.processUpgrades config checks s = .ok t) :
    SlashedPersistence s.state t.state :=
  processUpgrades_induction (property := fun x => SlashedPersistence s.state x.state)
    (fun held ok => held.trans (of_upgradeFrame (upgradeFrame_upgradeNext ok))) (refl _) ok

end SlashedPersistence

theorem Step.slashedPersistence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam) :
    SlashedPersistence x.state y.state := by
  cases step with
  | block engine signed due ok =>
    exact SlashedPersistence.processBlock early (applySignedBlock_ok ok).2.1
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (SlashedPersistence.advanceSlot
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le upgrades) early) slotOk).trans
      (SlashedPersistence.processUpgrades early upgrades)

theorem Run.slashedPersistence {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (early : y.fork < .glamsterdam) :
    SlashedPersistence x.state y.state := by
  induction run with
  | nil => exact SlashedPersistence.refl _
  | snoc pre step ih =>
    exact (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)).trans
      (step.slashedPersistence early)

end EthLib.Consensus
