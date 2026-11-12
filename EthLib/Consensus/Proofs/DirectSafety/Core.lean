module

public import EthLib.Consensus.Proofs.DirectSafety.Conflict

/-!
# Support of the voters of a quorum call

Previous-epoch voters may have exited the current active set, so the support includes them.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable def recentKeys {fork : Fork} (s : BeaconState preset fork) : Finset BLSPubkey :=
  activeKeys s ∪ keysAt s (getActiveValidatorIndices s (getPreviousEpoch s))

theorem quorum_voters_recent_gloas {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .hegota) (call : QuorumCall run) :
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
      have backed := (cached_participation_gloas run parameters genesis early call.toEpochCall).1
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

/-- The pre-Gloas interface for the recent-voter support bound. -/
theorem quorum_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (call : QuorumCall run) :
    call.voters ⊆ recentKeys call.cached :=
  quorum_voters_recent_gloas run parameters genesis (Nat.lt_trans early (by decide)) call

end EthLib.Consensus.DirectSafety
