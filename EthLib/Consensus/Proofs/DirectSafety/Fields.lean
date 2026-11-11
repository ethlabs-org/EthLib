module

public import EthLib.Consensus.Proofs.DirectSafety.Provenance
public import EthLib.Consensus.Proofs.DirectSafety.Hashes

/-!
# Concrete justification calls and checkpoint fields

Every call below is at an epoch boundary of the supplied run, on the state that processSlot returns.

The witnesses describe executions of the four bit rules, not an abstract finality relation.

Gasper §4 describes justification and finalization: https://arxiv.org/abs/2003.03052v3.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def targetIndices {fork : Fork} (state : BeaconState preset fork) (epoch : Epoch) :
    Except TransitionError (List ValidatorIndex) := do
  if altair : .altair ≤ fork then
    liftAccessor (getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch)
  else
    let pending ← getMatchingTargetAttestations state (Nat.lt_of_not_le altair) epoch
    liftAccessor (getUnslashedAttestingIndices state pending)

structure EpochCall {g a : ForkedBeaconState preset} (run : Run config checks g a) where
  before : ForkedBeaconState preset
  after : ForkedBeaconState preset
  advanced : advanceSlotAcross config checks before = .ok after
  member : run.Contains (.slot advanced)
  boundary : (before.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0
  cached : BeaconState preset before.fork
  weighed : BeaconState preset before.fork
  cachedOk : processSlot before.state = .ok cached
  weighedOk : processJustificationAndFinalization cached = .ok weighed
  later : GENESIS_EPOCH + 1 < getCurrentEpoch cached

/-- An actual successful justification test inside an epoch call. -/
structure QuorumCall {g a : ForkedBeaconState preset} (run : Run config checks g a)
    extends EpochCall run where
  current : Bool
  target : Checkpoint
  targetEpoch : target.epoch =
    if current then getCurrentEpoch cached else getPreviousEpoch cached
  targetRoot : getBlockRoot cached target.epoch = .ok target.root
  indices : List ValidatorIndex
  counted : targetIndices cached target.epoch = .ok indices
  total : Gwei
  part : Gwei
  threshold : Gwei
  weighted : Gwei
  totalOk : getTotalActiveBalance cached = .ok total
  partOk : getTotalBalance cached indices = .ok part
  thresholdOk : Uint64.mulChecked total 2 = .ok threshold
  weightedOk : Uint64.mulChecked part 3 = .ok weighted
  passes : threshold ≤ weighted

def QuorumCall.source {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : QuorumCall run) : Checkpoint :=
  if call.current then call.cached.currentJustifiedCheckpoint
    else call.cached.previousJustifiedCheckpoint

noncomputable def QuorumCall.voters {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : QuorumCall run) : Finset BLSPubkey :=
  keysAt call.cached call.indices

/-- The lower bound excludes the one-increment floor from manufacturing a quorum. -/
def EnoughStake {g a : ForkedBeaconState preset} (run : Run config checks g a) : Prop :=
  ∀ call : EpochCall run, 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
    2 * Quorum.weight (effectiveWeight call.cached) (activeKeys call.cached)

structure JustificationHistory {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (checkpoint : Checkpoint) where
  calls : List (QuorumCall run)
  nonempty : calls ≠ []
  start : ∀ c, calls.head? = some c → c.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  finish : ∀ c, calls.getLast? = some c → c.target = checkpoint
  consecutive : ∀ i left right, calls[i]? = some left → calls[i + 1]? = some right →
    left.target = right.source

/-- The four actual boolean branches read by weighJustificationAndFinalization. -/
def FinalizationRule {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) (checkpoint : Checkpoint) : Prop :=
  let bits := call.weighed.justificationBits.bits
  let e := (getCurrentEpoch call.cached).toNat
  (checkpoint = call.cached.previousJustifiedCheckpoint ∧
    ((bits[1] = true ∧ bits[2] = true ∧ bits[3] = true ∧ checkpoint.epoch.toNat + 3 = e) ∨
      (bits[1] = true ∧ bits[2] = true ∧ checkpoint.epoch.toNat + 2 = e))) ∨
  (checkpoint = call.cached.currentJustifiedCheckpoint ∧
    ((bits[0] = true ∧ bits[1] = true ∧ bits[2] = true ∧ checkpoint.epoch.toNat + 2 = e) ∨
      (bits[0] = true ∧ bits[1] = true ∧ checkpoint.epoch.toNat + 1 = e)))

theorem quorum_count {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (enough : EnoughStake run) (call : QuorumCall run) :
    2 * Quorum.weight (effectiveWeight call.cached) (activeKeys call.cached) ≤
      3 * Quorum.weight (effectiveWeight call.cached) call.voters := by
  sorry

theorem quorum_attestations {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (call : QuorumCall run) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target := by
  sorry

/-- A set bit identifies a successful test on this run, not merely an epoch number. -/
theorem justification_bit_call {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : EpochCall run) (i : Fin 4) (set : call.weighed.justificationBits.bits[i] = true) :
    ∃ witness : QuorumCall run,
      witness.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat := by
  sorry

/-- Caching a slot must retain the participation evidence used by its epoch call. -/
theorem cached_participation {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (call : EpochCall run) :
    ParticipationBacked run call.cached := by
  sorry

theorem justified_fields {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (c : Checkpoint)
    (field : c = a.state.previousJustifiedCheckpoint ∨ c = a.state.currentJustifiedCheckpoint) :
    c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ Nonempty (JustificationHistory run c) := by
  sorry

theorem quorum_source_history {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : QuorumCall run) :
    call.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run call.source) := by
  sorry

theorem finalized_field {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) :
    a.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      ∃ call : EpochCall run, call.weighed.finalizedCheckpoint = a.state.finalizedCheckpoint ∧
        FinalizationRule call a.state.finalizedCheckpoint := by
  sorry

/-- The rule supplies its outgoing quorum and all intervening concrete justification histories. -/
theorem finalization_rule_quorums {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : EpochCall run) (c : Checkpoint) (rule : FinalizationRule call c) :
    ∃ outgoing : QuorumCall run, outgoing.source = c ∧
      (outgoing.target.epoch.toNat = c.epoch.toNat + 1 ∨
        outgoing.target.epoch.toNat = c.epoch.toNat + 2) ∧
      (c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        Nonempty (JustificationHistory run c)) ∧
      (outgoing.target.epoch.toNat = c.epoch.toNat + 2 →
        ∃ middle : Checkpoint, middle.epoch.toNat = c.epoch.toNat + 1 ∧
          Nonempty (JustificationHistory run middle)) := by
  sorry

/-- Finalization retains a justification history even after both justified fields move on. -/
theorem finalized_history {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g) :
    a.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run a.state.finalizedCheckpoint) := by
  sorry

/-- Calls retain their target's path even when the endpoint's root ring has overwritten it. -/
theorem call_target_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (one : QuorumCall left) (two : QuorumCall right) (same : one.target = two.target) :
    left.checkpointPath one.target = right.checkpointPath two.target ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  sorry

end EthLib.Consensus.DirectSafety
