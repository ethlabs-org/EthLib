module

public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Proofs.Transition.Trace

/-!
# Proofs: before Altair, each pending attestation lies in the epoch of its list

A block accepts an attestation only when its target epoch is the current or the previous epoch.

That target epoch must also be the epoch of its slot.

The block records it in the list of the current epoch or of the previous one, by its target.

At the end of an epoch the list of the current epoch becomes that of the previous one.

The other steps keep both lists, and genesis starts with both empty.

An upgrade moves the state to Altair, where no pending attestation remains.

So along a run from genesis, each pending attestation of the previous epoch has its slot in it.

Its committee is cut from the validators active in that epoch.

This is `PendingVoted` for the set of all votes, whose votes then say nothing.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- Along a run from genesis, the pending attestations lie in the epochs of their lists.

Their target epoch is the epoch of their list, and the epoch of their slot.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem Run.pendingVoted_univ {g x : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (run : Run config checks g x)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    PendingVoted Set.univ x.state := by
  -- The two justified checkpoints are equal in the first two epochs, which the slots need.
  suffices both : JustifiedEarly x.state ∧ PendingVoted Set.univ x.state from both.2
  induction run with
  | nil =>
    obtain ⟨_, _, _, computed⟩ := genesis
    refine ⟨JustifiedEarly.of_initializeBeaconStateFromEth1 computed,
      fun before current pending member => ?_⟩
    rw [initializeBeaconStateFromEth1_pending computed before current] at member
    simp at member
  | @snoc middle last pre step ih =>
    obtain ⟨early, holds⟩ := ih
    cases step with
    | slot computed =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
      have pending : PendingVoted Set.univ advanced := by
        by_cases before : middle.fork < .altair
        · exact holds.of_advanceSlot before apart early advancedOk
        · exact fun before' => absurd before' before
      exact ⟨(early.of_advanceSlot advancedOk).of_processUpgrades upgraded,
        pending.of_processUpgrades upgraded⟩
    | block engine signed due applied =>
      obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
      exact ⟨early.of_frame (frame_processBlock blockOk), fun before =>
        (PendingVoted.of_processBlock before apart holds blockOk).mono
          (fun _ _ => trivial) before⟩

/-- Before Altair, the attestations that match the source of the previous epoch lie in it.

Each has its slot in the previous epoch.

At genesis the previous epoch is the current one, and the list of the current epoch is read. -/
theorem PendingVoted.matchingSource_slot {votes : Set (ValidatorIndex × AttestationData)}
    {state : BeaconState preset fork} (holds : PendingVoted votes state) (before : fork < .altair)
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingSourceAttestations state before (getPreviousEpoch state) =
      .ok attestations) :
    ∀ pending ∈ attestations,
      computeEpochAtSlot preset pending.data.slot = getPreviousEpoch state := by
  intro pending member
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at matching
  obtain ⟨_, _, rfl⟩ := matching
  by_cases here : getPreviousEpoch state = getCurrentEpoch state
  · simp only [here, ↓reduceIte] at member
    obtain ⟨epoch, slot, -⟩ := holds before true pending member
    simp only [↓reduceIte] at epoch
    rw [slot, epoch, here]
  · simp only [here, ↓reduceIte] at member
    obtain ⟨epoch, slot, -⟩ := holds before false pending member
    simp only [Bool.false_eq_true, ↓reduceIte] at epoch
    rw [slot, epoch]

end EthLib.Consensus
