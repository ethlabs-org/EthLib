module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Admission

/-! The six honest votes for the witness's slot-one block. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness

open Base Serialization.Ssz

/-- The source stays at genesis and the target is the anchor throughout the first epoch. -/
def voteData (slot : Slot) : AttestationData :=
  ⟨slot, 0, blockRoot, ⟨0, Vector.replicate 32 0⟩, ⟨0, anchorRoot⟩⟩

/-- The six validators of slots one to three each vote once; slot zero precedes the execution. -/
def Voter (v : ValidatorIndex) : Prop := v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7

/-- A voter's slot is one of the three slots of the execution with a duty deadline. -/
theorem voter_slot {v : ValidatorIndex} (within : Voter v) :
    v / 2 = 1 ∨ v / 2 = 2 ∨ v / 2 = 3 := by
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Each voter signs its own attestation: the bit of its position in its slot's committee. -/
def vote (v : ValidatorIndex) : Attestation preset .phase0 where
  data := voteData (v / 2)
  signature := default
  aggregationBits :=
    if v % 2 = 0 then ⟨#[true, false], by decide⟩ else ⟨#[false, true], by decide⟩
  committeeBits := fun h => nomatch h

/-- The indexed form lists just the voter. -/
def indexedVote (v : ValidatorIndex) : IndexedAttestation preset .phase0 :=
  ⟨⟨#[v], by intro; change 1 ≤ maxAttesters preset .phase0; decide⟩, voteData (v / 2), default⟩

/-- The committee of a voter's slot holds the voter and its slot-mate. -/
theorem voter_committee {v : ValidatorIndex} (within : Voter v) :
    getBeaconCommittee (state bodyRoot) (v / 2) 0 = .ok #[2 * (v / 2), 2 * (v / 2) + 1] := by
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (committees bodyRoot).2.1
  · exact (committees bodyRoot).2.1
  · exact (committees bodyRoot).2.2.1
  · exact (committees bodyRoot).2.2.1
  · exact (committees bodyRoot).2.2.2
  · exact (committees bodyRoot).2.2.2

set_option maxRecDepth 10000 in
/-- The bits of each of the six votes identify exactly its sender. -/
theorem vote_indices {v : ValidatorIndex} (within : Voter v) :
    getAttestingIndices (state bodyRoot) (vote v) = .ok [v] := by
  rw [getAttestingIndices_of_lt_electra (by decide)]
  change (do
    let committee ← getBeaconCommittee (state bodyRoot) (v / 2) 0
    return sortedSet (← committeeAttesters (vote v).aggregationBits.bits 0 committee)) =
      .ok [v]
  rw [voter_committee within]
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> cbv <;> simp [keepNew]

set_option maxRecDepth 10000 in
/-- Indexing each vote preserves its data and lists only its sender. -/
theorem vote_indexed {v : ValidatorIndex} (within : Voter v) :
    getIndexedAttestation (state bodyRoot) (vote v) = .ok (indexedVote v) := by
  simp only [getIndexedAttestation, vote_indices within, bind, Except.bind]
  simp only [indexedAttestationOf, List.length_singleton]
  rfl

set_option maxRecDepth 10000 in
/-- Each vote has precisely one bit per seat of its named committee. -/
theorem vote_committees {v : ValidatorIndex} (within : Voter v) :
    checkAttestationCommittees (state bodyRoot) (vote v) = .ok () := by
  have countOk : getCommitteeCountPerSlotChecked (state bodyRoot) 0 = .ok 1 := rfl
  simp only [checkAttestationCommittees, show ¬ Fork.pectra ≤ Fork.phase0 by decide, ↓reduceDIte,
    show (vote v).data.target.epoch = 0 from rfl,
    show (vote v).data.index = 0 from rfl, show (vote v).data.slot = v / 2 from rfl,
    countOk, liftAccessor, Except.mapError, bind, Except.bind]
  rw [voter_committee within]
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 10000 in
/-- Signature acceptance still checks the singleton index and constructs both signing hashes. -/
theorem vote_signature {v : ValidatorIndex} (within : Voter v) :
    isValidIndexedAttestation config .acceptAll (state bodyRoot) (indexedVote v) = .ok true := by
  obtain ⟨domain, domainOk⟩ := getDomain_total config (state bodyRoot) DOMAIN_BEACON_ATTESTER
    (some (voteData (v / 2)).target.epoch)
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total (voteData (v / 2)) domain
  have found : getValidator (state bodyRoot) v = .ok (validator 200) := by
    rcases within with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have sortedOne : sortedSet [v] = [v] := by simp [sortedSet, keepNew]
  simp [isValidIndexedAttestation, indexedVote, sortedOne, found, domainOk, rootOk,
    liftAccessor, liftSsz, SignatureChecks.acceptAll, bind, Except.bind, pure,
    Except.pure, Except.mapError]
  decide

end EthLib.Consensus.Models.Network.EightValidatorWitness
