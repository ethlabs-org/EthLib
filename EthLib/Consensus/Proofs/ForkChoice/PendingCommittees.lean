module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints

/-!
# Committee agreement for pending attestations

A run through the epoch after a pending attestation keeps its committee read.

The run may start in the attestation's epoch or in the next epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- A run through the next epoch keeps the indices decoded from a pending attestation. -/
theorem RunKept.pendingAttestingIndices_eq_through_next_epoch
    {state after : BeaconState preset fork} (run : RunKept state after)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {pending : PendingAttestation preset}
    (starts : computeEpochAtSlot preset pending.data.slot ≤ getCurrentEpoch state)
    (ends : (getCurrentEpoch after).toNat ≤
      (computeEpochAtSlot preset pending.data.slot).toNat + 1) :
    getPendingAttestingIndices after pending = getPendingAttestingIndices state pending := by
  have startsNat := UInt64.le_iff_toNat_le.mp starts
  have committees : CommitteesKept (computeEpochAtSlot preset pending.data.slot) state after :=
    run.committeesKept (by omega)
      (UInt64.le_trans starts (getCurrentEpoch_le_activityFixedEpoch state)) (by omega)
  -- Only the committee read depends on the state, including when that read fails.
  unfold getPendingAttestingIndices
  rw [committees pending.data.slot pending.data.index rfl]

end EthLib.Consensus
