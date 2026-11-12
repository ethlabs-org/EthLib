module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Steps

/-! Honest sends and processing completeness for the six candidate votes. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness

open Base

/-- A vote cannot change a store until its duty slot has ended. -/
theorem running_vote_not_yet (time : UInt64) (count : Nat) (v : ValidatorIndex)
    (early : time / 1000 ≤ v / 2) (after : Store preset .phase0) :
    (running time count).onAttestation config .acceptAll (vote v) false ≠ .ok after := by
  intro accepted
  simp only [Store.onAttestation, bind_ok_iff] at accepted
  obtain ⟨result, valid, _⟩ := accepted
  cases result
  obtain ⟨current, clock, later⟩ := (Store.validateOnAttestation_ok valid).2.2.2
  rw [running_clock, Except.ok.injEq] at clock
  subst current
  exact (UInt64.not_lt.mpr early) later

/-- Every received message is already processed or is a vote whose slot has not ended. -/
def ReadyView (time : UInt64) (count : Nat) (view : Set (Message preset .phase0)) : Prop :=
  ∀ message ∈ view, message = .block signedBlock ∨
    ∃ v, Voter v ∧ message = .attestation (vote v) ∧
      (v.toNat ≤ count + 1 ∨ time / 1000 ≤ v / 2)

set_option maxRecDepth 10000 in
/-- These views contain no message that could change the candidate store at its current time. -/
theorem running_up_to_date (time : UInt64) {count : Nat} (bound : count ≤ 6)
    {view : Set (Message preset .phase0)} (ready : ReadyView time count view) :
    UpToDate config .acceptAll sources time.toNat view (running time count) := by
  refine ⟨rfl, fun after handles => ?_⟩
  cases handles with
  | tick _ _ step =>
    have tick := onTick_timeMs (running_clock time count)
    change (running time count).onTick config time = .ok _ at tick
    simpa [tick] using step.symm
  | block member step =>
    rcases ready _ member with equal | ⟨v, _, equal, _⟩
    · cases equal
      rw [running_block_repeat] at step
      exact (Except.ok.inj step).symm
    · cases equal
  | attestation member step =>
    rcases ready _ member with equal | ⟨v, within, equal, old | early⟩
    · cases equal
    · cases equal
      exact running_vote_repeat time bound within old step
    · cases equal
      exact False.elim (running_vote_not_yet time count v early after step)
  | attesterSlashing member _ =>
    rcases ready _ member with equal | ⟨v, _, equal, _⟩ <;> cases equal
  | payloadAttestation _ _ => contradiction
  | envelope _ _ => contradiction
  | inclusionList _ _ => contradiction

/-- The first epoch assigns validators `2 s` and `2 s + 1` to slot `s`.

The short witness ends before any second-epoch attestation deadline. -/
def assignment : Assignment preset where
  committee v slot := if v < 8 ∧ slot = v / 2 then some 0 else none
  once v first second _ _ isFirst isSecond _ := by
    split at isFirst <;> split at isSecond <;> simp_all

/-- The empty block carries no attestation or attester-slashing statement. -/
theorem block_statements :
    statements config .acceptAll (state bodyRoot) (anchorBlock stateRoot)
      (.block signedBlock) = ∅ := by
  ext x
  simp [statements, signedBlock, firstBlock, body, emptyBody]

set_option maxRecDepth 10000 in
/-- At its deadline, each assigned honest signer can sign the child's vote without slashing. -/
theorem running_may_sign {v : ValidatorIndex} (within : Voter v)
    {count : Nat} (bound : count ≤ 6) {view : Set (Message preset .phase0)}
    (ready : ReadyView (v / 2 * 1000 + 333) count view) :
    MaySign config .acceptAll sources (state bodyRoot) (anchorBlock stateRoot) assignment 0
      v (v / 2 * 1000 + 333).toNat view
      (running (v / 2 * 1000 + 333) count) (voteData (v / 2)) := by
  have clock : (running (v / 2 * 1000 + 333) count).getCurrentStoreEpoch config = .ok 0 := by
    rw [Store.getCurrentStoreEpoch, running_clock]
    rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨0, ?_, ?_, rfl, running_up_to_date _ bound ready,
    running_vote_data _ count bound within clock (.inl rfl), ?_⟩
  · rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨v / 2 * 1000, 333, ?_, rfl, ?_⟩ <;>
      rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro m member y statement own
    rcases ready m member with rfl | ⟨other, otherWithin, rfl, _⟩
    · rw [block_statements] at statement
      exact False.elim statement
    · have eq := running_vote_statements otherWithin statement
      subst y
      have same : other = v := own
      subst other
      simp [isSlashableAttestationData]

/-- The six singleton attestations are legal honest sends at their deadlines. -/
theorem running_vote_sends {v : ValidatorIndex} (within : Voter v)
    {count : Nat} (bound : count ≤ 6) {view : Set (Message preset .phase0)}
    (ready : ReadyView (v / 2 * 1000 + 333) count view) :
    HonestSends config .acceptAll sources (state bodyRoot) (anchorBlock stateRoot) assignment 0
      v (v / 2 * 1000 + 333).toNat view
      (running (v / 2 * 1000 + 333) count) (.attestation (vote v)) := by
  intro x statement _
  rw [running_vote_statements within statement]
  exact .inr (running_may_sign within bound ready)

set_option maxRecDepth 10000 in
/-- Accepting the next vote at a boundary advances the candidate's recorded-vote count. -/
theorem running_vote_step {v : ValidatorIndex} (within : Voter v) :
    (running ((v / 2 + 1) * 1000) (v.toNat - 2)).onAttestation config .acceptAll
      (vote v) false = .ok (running ((v / 2 + 1) * 1000) (v.toNat - 1)) := by
  have clock : (running ((v / 2 + 1) * 1000) (v.toNat - 2)).getCurrentSlot config =
      .ok (v / 2 + 1) := by
    rw [running_clock]
    rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [running_vote_accepted _ _ within clock]
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Store.updateLatestMessages, running, recordVote,
      LatestMessage.ofAttestation, vote, voteData, admitted, ticked, anchor]

end EthLib.Consensus.Models.Network.EightValidatorWitness
