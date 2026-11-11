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

noncomputable def commonAccountable {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (one two : EitherCall left right) : Finset BLSPubkey := by
  classical
  exact (one.voters ∩ two.voters).filter (Accountable left right)

theorem quorum_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (call : QuorumCall run) :
    call.voters ⊆ recentKeys call.cached := by
  classical
  -- Both participation flags and pending votes select validators active at the target epoch.
  have active : ∀ i ∈ call.indices, i ∈ getActiveValidatorIndices call.cached
      (if call.current then getCurrentEpoch call.cached else getPreviousEpoch call.cached) := by
    intro i member
    have counted := call.counted
    rw [call.targetEpoch] at counted
    unfold targetIndices at counted
    split at counted
    · exact (mem_getUnslashedParticipatingIndices (liftAccessor_ok.mp counted) i member).1
    · rename_i before
      simp only [bind_ok_iff] at counted
      obtain ⟨pending, matching, counted⟩ := counted
      have backed := (cached_participation run parameters genesis early call.toEpochCall).1
      -- A quorum call is after the two epochs where equal justified fields are required.
      have notEarly : JustifiedEarly call.cached := by
        intro small
        have smallNat := UInt64.le_iff_toNat_le.mp small
        have laterNat := UInt64.lt_iff_toNat_lt.mp call.later
        omega
      exact (backed.attester (Nat.lt_of_not_le before) notEarly call.current matching
        (liftAccessor_ok.mp counted) member).1
  intro key member
  simp only [QuorumCall.voters, keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨i, member, found⟩ := member
  have present : key ∈ keysAt call.cached (getActiveValidatorIndices call.cached
      (if call.current then getCurrentEpoch call.cached else getPreviousEpoch call.cached)) := by
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, active i member, found⟩
  cases current : call.current
  · exact Finset.mem_union_right _ (by simpa [current] using present)
  · exact Finset.mem_union_left _ (by simpa [current, activeKeys] using present)

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
      (∀ key ∈ one.voters ∩ two.voters, Accountable left right key) ∧
      2 * (Quorum.weight (effectiveWeight one.state.state) (activeKeys one.state.state) +
        Quorum.weight (effectiveWeight two.state.state) (activeKeys two.state.state)) ≤
        3 * Quorum.weight (fun k => min (effectiveWeight one.state.state k)
          (effectiveWeight two.state.state k)) (commonAccountable left right one two) +
        3 * unionStake one two) ∨ HashEvidence (left.hashObjects ++ right.hashObjects) := by
  classical
  rcases conflicting_fields_quorums left right parameters genesis earlyA earlyB j field
    ordered conflict with ⟨one, two, loOne, hiOne, loTwo, hiTwo, slashable⟩ | hashes
  · have accountable : ∀ key ∈ one.voters ∩ two.voters, Accountable left right key :=
      fun key member => Or.inl (slashable key member)
    -- Every common voter is accountable, so the filter removes none of the overlap.
    have common : commonAccountable left right one two = one.voters ∩ two.voters := by
      exact Finset.filter_eq_self.mpr accountable
    have inside : ∀ call : EitherCall left right,
        call.voters ⊆ recentKeys call.state.state := by
      intro call
      cases call with
      | inl call => exact quorum_voters_recent left parameters genesis earlyA call
      | inr call => exact quorum_voters_recent right parameters genesis earlyB call
    have counted : ∀ call : EitherCall left right,
        2 * Quorum.weight (effectiveWeight call.state.state) (activeKeys call.state.state) ≤
          3 * Quorum.weight (effectiveWeight call.state.state) call.voters := by
      intro call
      cases call with
      | inl call => exact quorum_count left genesis enoughA call
      | inr call => exact quorum_count right genesis enoughB call
    refine Or.inl ⟨one, two, loOne, hiOne, loTwo, hiTwo, accountable, ?_⟩
    -- The arithmetic allows distinct supports and weights, including two calls on one run.
    rw [common]
    exact Quorum.heterogeneous_intersection _ _ _ _ _ _ (inside one) (inside two)
      _ _ (counted one) (counted two)
  · exact Or.inr hashes

end EthLib.Consensus.DirectSafety
