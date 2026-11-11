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

noncomputable def slashableKeys {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (reference : ForkedBeaconState preset) : Finset BLSPubkey := by
  classical
  exact (activeKeys reference.state).filter (Slashable left right)

/-- Two finalized endpoint fields, with weights measured at their shared state. -/
theorem accountable_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint)
    (starts : x.state.slot.toNat ≤
      min a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat *
        preset.SLOTS_PER_EPOCH.toNat) :
    let high := max a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat
    (∃ eventsA eventsB, left.balanceEvents high = .ok eventsA ∧
      right.balanceEvents high = .ok eventsB ∧
      Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Quorum.weight (effectiveWeight x.state)
        (slashableKeys (shared.append left) (shared.append right) x) +
        2 * max (derivedDrift (config := config) x a high eventsA)
          (derivedDrift (config := config) x b high eventsB)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  sorry

/-- A finalized field versus either justified field at an equal or later epoch. -/
theorem accountable_safety_justified {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j)
    (starts : x.state.slot.toNat ≤
      a.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (∃ eventsA eventsB, left.balanceEvents j.epoch.toNat = .ok eventsA ∧
      right.balanceEvents j.epoch.toNat = .ok eventsB ∧
      Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Quorum.weight (effectiveWeight x.state)
        (slashableKeys (shared.append left) (shared.append right) x) +
        2 * max (derivedDrift (config := config) x a j.epoch.toNat eventsA)
          (derivedDrift (config := config) x b j.epoch.toNat eventsB)) ∨
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
