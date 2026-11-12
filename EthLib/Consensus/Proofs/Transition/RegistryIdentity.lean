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

/-- Keys form an unchanged prefix, and new keys do not duplicate earlier ones. -/
structure RegistryIdentity {fork fork' : Fork} (s : BeaconState preset fork)
    (t : BeaconState preset fork') : Prop where
  kept : validatorKeys s <+: validatorKeys t
  unique : (validatorKeys s).Nodup → (validatorKeys t).Nodup

theorem Frame.registryIdentity (frame : Frame state after) : RegistryIdentity state after :=
  ⟨frame.pubkeysPrefix, frame.pubkeysDistinct⟩

theorem UpgradeFrame.registryIdentity {post : Fork}
    {pre : BeaconState preset fork} {after : BeaconState preset post}
    (frame : UpgradeFrame config pre after) : RegistryIdentity pre after :=
  ⟨frame.pubkeysPrefix, frame.pubkeysDistinct⟩

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

theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    RegistryIdentity state after :=
  (frame_initiateValidatorExit ok).toFrame.registryIdentity

theorem slashValidator {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : Consensus.slashValidator config state index whistleblower = .ok after) :
    RegistryIdentity state after :=
  (frame_slashValidator ok).toFrame.registryIdentity

theorem processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (ok : Consensus.processParentExecutionPayload config checks state gloas body = .ok after) :
    RegistryIdentity state after :=
  (frame_processParentExecutionPayload ok).toFrame.registryIdentity

theorem processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : Consensus.processBlockExecution config checks engine state body bellatrix = .ok after) :
    RegistryIdentity state after :=
  (frame_processBlockExecution ok).toFrame.registryIdentity

theorem processBlockHeader {block : BeaconBlock preset fork}
    (ok : Consensus.processBlockHeader state block = .ok after) : RegistryIdentity state after :=
  (frame_processBlockHeader ok).toFrame.registryIdentity

theorem processRandao {body : BeaconBlockBody preset fork}
    (ok : Consensus.processRandao config checks state body = .ok after) :
    RegistryIdentity state after :=
  (frame_processRandao ok).toFrame.registryIdentity

theorem processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : Consensus.processEth1Data before state body = .ok after) :
    RegistryIdentity state after :=
  (frame_processEth1Data ok).toFrame.registryIdentity

theorem processProposerSlashing {slashing : ProposerSlashing}
    (ok : Consensus.processProposerSlashing config checks state slashing = .ok after) :
    RegistryIdentity state after :=
  (frame_processProposerSlashing ok).toFrame.registryIdentity

theorem processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (ok : Consensus.processAttesterSlashing config checks state slashing = .ok after) :
    RegistryIdentity state after :=
  (frame_processAttesterSlashing ok).toFrame.registryIdentity

theorem processBlock {block : BeaconBlock preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    RegistryIdentity state after :=
  (frame_processBlock ok).registryIdentity

theorem processRewardsAndPenalties
    (ok : Consensus.processRewardsAndPenalties config state = .ok after) :
    RegistryIdentity state after :=
  (frame_processRewardsAndPenalties ok).toFrame.registryIdentity

theorem processRegistryUpdates
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    RegistryIdentity state after :=
  (frame_processRegistryUpdates ok).toFrame.registryIdentity

theorem processSlashings (ok : Consensus.processSlashings state = .ok after) :
    RegistryIdentity state after :=
  (frame_processSlashings ok).toFrame.registryIdentity

theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    RegistryIdentity state after :=
  (frame_processEffectiveBalanceUpdates ok).toFrame.registryIdentity

theorem processPendingBalances
    (ok : Consensus.processPendingBalances config checks state = .ok after) :
    RegistryIdentity state after :=
  (frame_processPendingBalances ok).toFrame.registryIdentity

theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    RegistryIdentity state after :=
  of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

theorem processInactivityUpdates {altair : .altair ≤ fork}
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    RegistryIdentity state after :=
  (frame_processInactivityUpdates ok).toFrame.registryIdentity

theorem processEth1DataReset {before : fork < .hegota}
    (ok : Consensus.processEth1DataReset before state = .ok after) :
    RegistryIdentity state after :=
  (frame_processEth1DataReset ok).toFrame.registryIdentity

theorem processSlashingsReset (ok : Consensus.processSlashingsReset state = .ok after) :
    RegistryIdentity state after :=
  (frame_processSlashingsReset ok).toFrame.registryIdentity

theorem processRandaoMixesReset (ok : Consensus.processRandaoMixesReset state = .ok after) :
    RegistryIdentity state after :=
  (frame_processRandaoMixesReset ok).toFrame.registryIdentity

theorem processHistoricalRootsUpdate
    (ok : Consensus.processHistoricalRootsUpdate state = .ok after) :
    RegistryIdentity state after :=
  (frame_processHistoricalRootsUpdate ok).toFrame.registryIdentity

theorem processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (ok : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    RegistryIdentity state after :=
  (frame_processHistoricalSummariesUpdate ok).toFrame.registryIdentity

theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    RegistryIdentity state after :=
  (frame_queuePreActivation ok).toFrame.registryIdentity

theorem queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (ok : Consensus.queueCompoundingExcess state electra index = .ok after) :
    RegistryIdentity state after :=
  (frame_queueCompoundingExcess ok).toFrame.registryIdentity

end RegistryIdentity

end EthLib.Consensus
