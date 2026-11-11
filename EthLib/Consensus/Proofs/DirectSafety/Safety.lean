module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds

/-!
# Direct accountable safety: proposed public statements

All checkpoints are the fields of the endpoints of actual executions.

All attestation witnesses come from the supplied shared prefix or one of its two tails.

All proofs are placeholders pending statement review; no security theorem is proved here yet.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable def accountableKeys {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (reference : ForkedBeaconState preset) : Finset BLSPubkey := by
  classical
  exact (activeKeys reference.state).filter (Accountable left right)

/-- Retain the two witness costs instead of replacing both by the larger branch budget. -/
theorem accountable_safety_at_calls {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint ∨
      j = b.state.finalizedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j) :
    (∃ one two : EitherCall (shared.append left) (shared.append right),
      a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
      a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
      Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
        3 * Quorum.weight (effectiveWeight x.state)
          (accountableKeys (shared.append left) (shared.append right) x) +
        stateDrift x one.state + stateDrift x two.state) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  sorry

/-- Order the finalized fields by epoch, with weights measured at their shared state. -/
theorem accountable_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint)
    (starts : x.state.slot.toNat ≤
      min a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat *
        preset.SLOTS_PER_EPOCH.toNat) :
    let high := max a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat
    (Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Quorum.weight (effectiveWeight x.state)
        (accountableKeys (shared.append left) (shared.append right) x) +
        2 * max (derivedDrift high left) (derivedDrift high right)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  sorry

/-- A finalized field versus either justified field at an equal or later epoch. -/
theorem accountable_safety_justified {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j)
    (starts : x.state.slot.toNat ≤
      a.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Quorum.weight (effectiveWeight x.state)
        (accountableKeys (shared.append left) (shared.append right) x) +
        2 * max (derivedDrift j.epoch.toNat left) (derivedDrift j.epoch.toNat right)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  sorry

/-- The signer interpretation is conditional, with no probability or sampling theorem. -/
theorem accepted_evidence_is_signed {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (signed : BLSPubkey → AttestationData → Prop)
    (authA : Authenticated left signed) (authB : Authenticated right signed)
    (key : BLSPubkey) (slashable : Slashable left right key) :
    ∃ d₁ d₂, signed key d₁ ∧ signed key d₂ ∧ isSlashableAttestationData d₁ d₂ = true := by
  sorry

end EthLib.Consensus.DirectSafety
