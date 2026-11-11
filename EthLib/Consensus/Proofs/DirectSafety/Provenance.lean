module

public import EthLib.Consensus.Proofs.DirectSafety.Identity

/-!
# Participation backed by attestations of the selected run

Pending records retain their full data; participation flags retain a source and target.

The epoch rotation and Altair upgrade must preserve the same accepted witnesses.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def PendingBacked {g a : ForkedBeaconState preset} (run : Run config checks g a)
    {fork : Fork} (state : BeaconState preset fork) : Prop :=
  ∀ (early : fork < .altair) (current : Bool),
    ∀ pending ∈ (if current then state.currentEpochAttestations early
      else state.previousEpochAttestations early).data,
      pending.data.target.epoch =
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      pending.data.source = (if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint) ∧
      ∀ indices, getPendingAttestingIndices state pending = .ok indices →
        ∀ key ∈ keysAt state indices, run.Accepted key pending.data

def FlagsBacked {g a : ForkedBeaconState preset} (run : Run config checks g a)
    {fork : Fork} (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (current : Bool) (i : Nat) (flags : ParticipationFlags),
    (if current then state.currentEpochParticipation altair
      else state.previousEpochParticipation altair).data[i]? = some flags →
    hasFlag flags TIMELY_TARGET_FLAG_INDEX = true →
    ∀ validator, state.validators.data[i]? = some validator →
      ∃ data, run.Accepted validator.pubkey data ∧
        data.source = (if current then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint) ∧
        data.target.epoch = (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
        getBlockRoot state data.target.epoch = .ok data.target.root

def ParticipationBacked {g a : ForkedBeaconState preset} (run : Run config checks g a)
    {fork : Fork} (state : BeaconState preset fork) : Prop :=
  PendingBacked run state ∧ FlagsBacked run state

theorem genesis_participation {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ParticipationBacked (Run.nil : Run config checks g g) g.state := by
  sorry

/-- This includes epoch rotation and every due upgrade, in particular pending-to-flag conversion. -/
theorem slot_participation {g a b : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (ok : advanceSlotAcross config checks a = .ok b) (early : b.fork < .glamsterdam)
    (backed : ParticipationBacked run a.state) :
    ParticipationBacked (run.snoc (.slot ok)) b.state := by
  sorry

theorem block_participation {g : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} (run : Run config checks g ⟨fork, a⟩)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork) (due : upgradeDue config ⟨fork, a⟩ = false)
    (ok : applySignedBlock config checks engine a signed true = .ok b)
    (backed : ParticipationBacked run a) :
    ParticipationBacked (run.snoc (.block engine signed due ok)) b := by
  sorry

theorem run_participation {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) : ParticipationBacked run a.state := by
  sorry

/-- Inherited participation belongs to the shared prefix, not to an arbitrary reachable run. -/
theorem inherited_participation {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) :
    ParticipationBacked (shared.append tail) x.state := by
  sorry

end EthLib.Consensus.DirectSafety
