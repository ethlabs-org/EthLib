module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Admission

/-! The three honest votes for the witness's slot-one block. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz

/-- The source stays at genesis and the target is the anchor throughout the first epoch. -/
def voteData (slot : Slot) : AttestationData :=
  ⟨slot, 0, blockRoot, ⟨0, Vector.replicate 32 0⟩, ⟨0, anchorRoot⟩⟩

/-- The last committee's first bit is unset: Byzantine validator 3 sends no vote. -/
def vote (slot : Slot) : Attestation preset .phase0 where
  data := voteData slot
  signature := default
  aggregationBits := if slot = 3 then ⟨#[false, true], by decide⟩ else ⟨#[true], by decide⟩
  committeeBits := fun h => nomatch h

/-- Slots one and two have one signer each; slot three has only honest validator 4. -/
def voter (slot : Slot) : ValidatorIndex := if slot = 3 then 4 else slot

/-- The indexed form lists just the honest sender. -/
def indexedVote (slot : Slot) : IndexedAttestation preset .phase0 :=
  ⟨⟨#[voter slot], by intro; change 1 ≤ maxAttesters preset .phase0; decide⟩,
    voteData slot, default⟩

set_option maxRecDepth 10000 in
/-- The bits of each of the three votes identify exactly its honest sender. -/
theorem vote_indices {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    getAttestingIndices (state bodyRoot) (vote slot) = .ok [voter slot] := by
  rw [getAttestingIndices_of_lt_electra (by decide)]
  change (do
    let committee ← getBeaconCommittee (state bodyRoot) slot 0
    return sortedSet (← committeeAttesters (vote slot).aggregationBits.bits 0 committee)) =
      .ok [voter slot]
  rcases within with rfl | rfl | rfl
  · rw [(committees bodyRoot).2.1]
    cbv
    simp [keepNew]
  · rw [(committees bodyRoot).2.2.1]
    cbv
    simp [keepNew]
  · rw [(committees bodyRoot).2.2.2]
    cbv
    simp [keepNew]

set_option maxRecDepth 10000 in
/-- Indexing the votes preserves their data and excludes the silent Byzantine validator. -/
theorem vote_indexed {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    getIndexedAttestation (state bodyRoot) (vote slot) = .ok (indexedVote slot) := by
  simp only [getIndexedAttestation, vote_indices within, bind, Except.bind]
  simp only [indexedAttestationOf, List.length_singleton]
  rfl

set_option maxRecDepth 10000 in
/-- Each vote has precisely one bit per seat of its named committee. -/
theorem vote_committees {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    checkAttestationCommittees (state bodyRoot) (vote slot) = .ok () := by
  have countOk : getCommitteeCountPerSlotChecked (state bodyRoot) 0 = .ok 1 := rfl
  simp only [checkAttestationCommittees, show ¬ Fork.pectra ≤ Fork.phase0 by decide, ↓reduceDIte,
    show (vote slot).data.target.epoch = 0 from rfl,
    show (vote slot).data.index = 0 from rfl, show (vote slot).data.slot = slot from rfl,
    countOk, liftAccessor, Except.mapError, bind, Except.bind]
  rcases within with rfl | rfl | rfl
  · rw [(committees bodyRoot).2.1]
    rfl
  · rw [(committees bodyRoot).2.2.1]
    rfl
  · rw [(committees bodyRoot).2.2.2]
    rfl

set_option maxRecDepth 10000 in
/-- Signature acceptance still checks the singleton index and constructs both signing hashes. -/
theorem vote_signature {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    isValidIndexedAttestation config .acceptAll (state bodyRoot) (indexedVote slot) = .ok true := by
  obtain ⟨domain, domainOk⟩ := getDomain_total config (state bodyRoot) DOMAIN_BEACON_ATTESTER
    (some (voteData slot).target.epoch)
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total (voteData slot) domain
  have found : getValidator (state bodyRoot) (voter slot) = .ok (validator 200) := by
    rcases within with rfl | rfl | rfl <;> rfl
  have sortedOne : sortedSet [voter slot] = [voter slot] := by simp [sortedSet, keepNew]
  simp [isValidIndexedAttestation, indexedVote, sortedOne, found, domainOk, rootOk,
    liftAccessor, liftSsz, SignatureChecks.acceptAll, bind, Except.bind, pure,
    Except.pure, Except.mapError]
  decide

end EthLib.Consensus.Models.Network.FiveValidatorWitness
