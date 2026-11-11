module

public import EthLib.Consensus.Proofs.DirectSafety.Conflict

/-!
# Accountable safety without a drift assumption

Each quorum uses its own balances; shared slashable keys use the lesser balance.

The union uses the greater balance, with zero outside each support.

Previous-epoch voters may have exited the current active set, so the support includes them.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable def recentKeys {fork : Fork} (s : BeaconState preset fork) : Finset BLSPubkey :=
  activeKeys s ∪ keysAt s (getActiveValidatorIndices s (getPreviousEpoch s))

noncomputable def unionStake {g a b : ForkedBeaconState preset}
    {left : Run config checks g a} {right : Run config checks g b}
    (one two : EitherCall left right) : Nat :=
  Quorum.weight (fun k => max
    (Quorum.supported (recentKeys one.state.state) (effectiveWeight one.state.state) k)
    (Quorum.supported (recentKeys two.state.state) (effectiveWeight two.state.state) k))
    (recentKeys one.state.state ∪ recentKeys two.state.state)

noncomputable def commonSlashable {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (one two : EitherCall left right) : Finset BLSPubkey := by
  classical
  exact (one.voters ∩ two.voters).filter (Slashable left right)

theorem quorum_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (call : QuorumCall run) :
    call.voters ⊆ recentKeys call.cached := by
  sorry

/-- There is no bound on changes of membership or balances in this statement. -/
theorem accountable_safety_core {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake left) (enoughB : EnoughStake right)
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint ∨
      j = b.state.finalizedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict left right a.state.finalizedCheckpoint j) :
    (∃ one two : EitherCall left right,
      a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
      a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
      2 * (Quorum.weight (effectiveWeight one.state.state) (activeKeys one.state.state) +
        Quorum.weight (effectiveWeight two.state.state) (activeKeys two.state.state)) ≤
        3 * Quorum.weight (fun k => min (effectiveWeight one.state.state k)
          (effectiveWeight two.state.state k)) (commonSlashable left right one two) +
        3 * unionStake one two) ∨ HashEvidence (left.hashObjects ++ right.hashObjects) := by
  sorry

end EthLib.Consensus.DirectSafety
