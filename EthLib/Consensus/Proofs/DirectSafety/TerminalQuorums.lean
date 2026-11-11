module

public import EthLib.Consensus.Proofs.DirectSafety.Terminal

/-!
# Quorums from a terminal justification projection

The terminal input is reachable, so its participation evidence comes from the real run.

The projection supplies checked balance reads without requiring a future epoch transition.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

theorem terminal_quorum_count {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (enough : view.enough) (call : TerminalQuorum view) :
    2 * Quorum.weight (effectiveWeight a.state) (activeKeys a.state) ≤
      3 * Quorum.weight (effectiveWeight a.state) call.voters := by
  have unique := run.unique (genesis_unique genesis)
  have active := getTotalActiveBalance_ok call.totalOk
  have activeWeight := keys_weight a.state _ unique
    (getTotalBalance_ok_iff_stake.mp active).1
  have partWeight := keys_weight a.state _ unique
    (getTotalBalance_ok_iff_stake.mp call.partOk).1
  rw [call.selected] at enough
  have large := enough call.later
  simp only [activeKeys, activeWeight] at large ⊢
  simp only [TerminalQuorum.voters, partWeight]
  exact (justificationTest_iff_stake active call.partOk call.thresholdOk call.weightedOk
    large).mp call.passes

theorem terminal_quorum_attestations {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (view : TerminalView a) (call : TerminalQuorum view) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target := by
  have backed := run_participation run parameters genesis early
  have late := UInt64.not_le.mpr call.later
  intro key member
  simp only [TerminalQuorum.voters, keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨index, inside, found⟩ := member
  obtain ⟨validator, validatorFound, keyEq⟩ := Option.map_eq_some_iff.mp found
  have voted : ∃ vote, LinkVote a.state call.current index.toNat vote ∧
      vote ∈ run.votes := by
    have counted := call.counted
    rw [call.targetEpoch] at counted
    unfold targetIndices at counted
    split at counted
    · exact (backed.2.attester ‹_› late call.current
        (liftAccessor_ok.mp counted) inside).2
    · simp only [bind_ok_iff, liftAccessor_ok] at counted
      obtain ⟨pending, matching, indicesOk⟩ := counted
      obtain ⟨_, data, link, cast⟩ := backed.1.attester (Nat.lt_of_not_le ‹_›)
        (fun first => False.elim (late first)) call.current matching indicesOk inside
      exact ⟨(index, data), link, cast⟩
  obtain ⟨vote, link, cast⟩ := voted
  obtain ⟨position, epoch, source, root⟩ := link
  have indexEq : vote.1 = index := UInt64.toNat_inj.mp position
  refine ⟨vote.2, ?_, source, ?_⟩
  · rw [← keyEq]
    exact selected_vote_key run (genesis_unique genesis) index vote.2 validator validatorFound
      (by simpa [← indexEq] using cast)
  · have epochEq := epoch.trans call.targetEpoch.symm
    have rootEq : vote.2.target.root = call.target.root := by
      rw [epochEq, call.targetRoot, Except.ok.injEq] at root
      exact root.symm
    cases h₁ : vote.2.target
    cases h₂ : call.target
    simp_all

theorem terminal_quorum_recent {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (view : TerminalView a) (call : TerminalQuorum view) :
    call.voters ⊆ recentKeys a.state := by
  classical
  have active : ∀ i ∈ call.indices, i ∈ getActiveValidatorIndices a.state
      (if call.current then getCurrentEpoch a.state else getPreviousEpoch a.state) := by
    intro i member
    have counted := call.counted
    rw [call.targetEpoch] at counted
    unfold targetIndices at counted
    split at counted
    · exact (mem_getUnslashedParticipatingIndices (liftAccessor_ok.mp counted) i member).1
    · rename_i before
      simp only [bind_ok_iff] at counted
      obtain ⟨pending, matching, counted⟩ := counted
      have backed := (run_participation run parameters genesis early).1
      have notEarly : JustifiedEarly a.state := by
        intro small
        have smallNat := UInt64.le_iff_toNat_le.mp small
        have laterNat := UInt64.lt_iff_toNat_lt.mp call.later
        omega
      exact (backed.attester (Nat.lt_of_not_le before) notEarly call.current matching
        (liftAccessor_ok.mp counted) member).1
  intro key member
  simp only [TerminalQuorum.voters, keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨i, member, found⟩ := member
  have present : key ∈ keysAt a.state (getActiveValidatorIndices a.state
      (if call.current then getCurrentEpoch a.state else getPreviousEpoch a.state)) := by
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, active i member, found⟩
  cases current : call.current
  · exact Finset.mem_union_right _ (by simpa [current] using present)
  · exact Finset.mem_union_left _ (by simpa [current, activeKeys] using present)

theorem terminal_quorum_epochs {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (call : TerminalQuorum view) :
    call.source.epoch < call.target.epoch := by
  have _ := parameters
  have invariants {a : ForkedBeaconState preset} (pre : Run config checks g a) :
      Invariant a.state ∧ JustifiedEarly a.state ∧ JustifiedSeparated a.state := by
    induction pre with
    | nil =>
      obtain ⟨hash, time, deposits, ok⟩ := genesis
      refine ⟨(initializeBeaconStateFromEth1_invariant ok).2,
        JustifiedEarly.of_initializeBeaconStateFromEth1 ok, ?_⟩
      obtain ⟨_, _, _, _, _, frame, equal⟩ := initializeBeaconStateFromEth1_frame ok
      rw [equal]
      intro later
      have slot := frame.slot
      simp only [getCurrentEpoch, slot, emptyGenesisState] at later
      simp [GENESIS_SLOT, GENESIS_EPOCH, computeEpochAtSlot, UInt64.lt_iff_toNat_lt] at later
    | snoc pre step ih =>
      rcases ih with ⟨holds, early, separated⟩
      cases step with
      | slot ok =>
        obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
        exact ⟨(advanceSlotAcross_invariant holds ok).1,
          (early.of_advanceSlot advancedOk).of_processUpgrades upgraded,
          (separated.of_advanceSlot early holds.settled advancedOk).of_processUpgrades upgraded⟩
      | block engine signed due ok =>
        obtain ⟨_, blockOk, _⟩ := applySignedBlock_ok ok
        have frame := frame_processBlock blockOk
        exact ⟨frame.invariant holds, early.of_frame frame, separated.of_frame frame⟩
  obtain ⟨holds, _, separated⟩ := invariants run
  have settled := holds.settled
  have previous := separated call.later
  rw [TerminalQuorum.source, call.targetEpoch]
  cases call.current
  · exact previous
  · have settledNat := UInt64.le_iff_toNat_le.mp settled
    have later := UInt64.lt_iff_toNat_lt.mp call.later
    apply UInt64.lt_iff_toNat_lt.mpr
    simp only [getPreviousEpoch_toNat] at settledNat
    have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
    rw [one] at later
    simp only [↓reduceIte]
    omega

end EthLib.Consensus.DirectSafety
