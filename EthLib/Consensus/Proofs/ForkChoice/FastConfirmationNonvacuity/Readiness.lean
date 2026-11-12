module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Steps

/-! Honest sends and processing completeness for the three candidate votes. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base

/-- A vote cannot change a store until its duty slot has ended. -/
theorem running_vote_not_yet (time : UInt64) (count : Nat) (slot : Slot)
    (early : time / 1000 ≤ slot) (after : Store preset .phase0) :
    (running time count).onAttestation config .acceptAll (vote slot) false ≠ .ok after := by
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
    ∃ slot, (slot = 1 ∨ slot = 2 ∨ slot = 3) ∧ message = .attestation (vote slot) ∧
      (slot.toNat ≤ count ∨ time / 1000 ≤ slot)

set_option maxRecDepth 10000 in
/-- These views contain no message that could change the candidate store at its current time. -/
theorem running_up_to_date (time : UInt64) {count : Nat} (bound : count ≤ 3)
    {view : Set (Message preset .phase0)} (ready : ReadyView time count view) :
    UpToDate config .acceptAll sources time.toNat view (running time count) := by
  refine ⟨rfl, fun after handles => ?_⟩
  cases handles with
  | tick _ _ step =>
    have tick := onTick_timeMs (running_clock time count)
    change (running time count).onTick config time = .ok _ at tick
    simpa [tick] using step.symm
  | block member step =>
    rcases ready _ member with equal | ⟨slot, _, equal, _⟩
    · cases equal
      rw [running_block_repeat] at step
      exact (Except.ok.inj step).symm
    · cases equal
  | attestation member step =>
    rcases ready _ member with equal | ⟨slot, within, equal, old | early⟩
    · cases equal
    · cases equal
      exact running_vote_repeat time bound within old step
    · cases equal
      exact False.elim (running_vote_not_yet time count slot early after step)
  | attesterSlashing member _ =>
    rcases ready _ member with equal | ⟨slot, _, equal, _⟩ <;> cases equal
  | payloadAttestation _ _ => contradiction
  | envelope _ _ => contradiction
  | inclusionList _ _ => contradiction

/-- The first epoch assigns one slot to each validator, with validators 3 and 4 sharing slot 3.

The short witness ends before any second-epoch attestation deadline. -/
def assignment : Assignment preset where
  committee v slot := if v < 5 ∧ slot = min v 3 then some 0 else none
  once v first second _ _ isFirst isSecond _ := by
    split at isFirst <;> split at isSecond <;> simp_all

/-- The empty block carries no attestation or attester-slashing statement. -/
theorem block_statements :
    statements config .acceptAll (state bodyRoot) (anchorBlock stateRoot)
      (.block signedBlock) = ∅ := by
  ext x
  simp [statements, signedBlock, firstBlock, body, emptyBody]

/-- The three votes have different signers. -/
theorem voter_inj {first second : Slot}
    (hfirst : first = 1 ∨ first = 2 ∨ first = 3)
    (hsecond : second = 1 ∨ second = 2 ∨ second = 3)
    (same : voter first = voter second) : first = second := by
  rcases hfirst with rfl | rfl | rfl <;>
    rcases hsecond with rfl | rfl | rfl <;> simp_all [voter]

set_option maxRecDepth 10000 in
/-- At its deadline, each assigned honest signer can sign the child's vote without slashing. -/
theorem running_may_sign {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3)
    {count : Nat} (bound : count ≤ 3) {view : Set (Message preset .phase0)}
    (ready : ReadyView (slot * 1000 + 333) count view) :
    MaySign config .acceptAll sources (state bodyRoot) (anchorBlock stateRoot) assignment 0
      (voter slot) (slot * 1000 + 333).toNat view
      (running (slot * 1000 + 333) count) (voteData slot) := by
  have clock : (running (slot * 1000 + 333) count).getCurrentStoreEpoch config = .ok 0 := by
    rw [Store.getCurrentStoreEpoch, running_clock]
    rcases within with rfl | rfl | rfl <;> rfl
  refine ⟨0, ?_, ?_, rfl, running_up_to_date _ bound ready,
    running_vote_data _ count bound within clock (.inl rfl), ?_⟩
  · rcases within with rfl | rfl | rfl <;> rfl
  · refine ⟨slot * 1000, 333, ?_, rfl, ?_⟩ <;>
      rcases within with rfl | rfl | rfl <;> rfl
  · intro m member y statement own
    rcases ready m member with rfl | ⟨other, otherWithin, rfl, _⟩
    · rw [block_statements] at statement
      exact False.elim statement
    · have eq := running_vote_statements otherWithin statement
      subst y
      have same := voter_inj otherWithin within own
      subst other
      simp [isSlashableAttestationData]

/-- The three singleton attestations are legal honest sends at their deadlines. -/
theorem running_vote_sends {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3)
    {count : Nat} (bound : count ≤ 3) {view : Set (Message preset .phase0)}
    (ready : ReadyView (slot * 1000 + 333) count view) :
    HonestSends config .acceptAll sources (state bodyRoot) (anchorBlock stateRoot) assignment 0
      (voter slot) (slot * 1000 + 333).toNat view
      (running (slot * 1000 + 333) count) (.attestation (vote slot)) := by
  intro x statement _
  rw [running_vote_statements within statement]
  exact .inr (running_may_sign within bound ready)

set_option maxRecDepth 10000 in
/-- Accepting the next vote at a boundary advances the candidate's recorded-vote count. -/
theorem running_vote_step {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    (running ((slot + 1) * 1000) (slot.toNat - 1)).onAttestation config .acceptAll
      (vote slot) false = .ok (running ((slot + 1) * 1000) slot.toNat) := by
  have clock : (running ((slot + 1) * 1000) (slot.toNat - 1)).getCurrentSlot config =
      .ok (slot + 1) := by
    rw [running_clock]
    rcases within with rfl | rfl | rfl <;> rfl
  rw [running_vote_accepted _ _ within clock]
  rcases within with rfl | rfl | rfl <;>
    simp [Store.updateLatestMessages, running, voter, recordVote,
      LatestMessage.ofAttestation, vote, voteData, admitted, ticked, anchor]

end EthLib.Consensus.Models.Network.FiveValidatorWitness
