module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.PostState
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates
-- These equations expose SSZ's mutual recursion to the certificate evaluator.
import all EthLib.Serialization.Ssz.Merkle.Merkleize
import all EthLib.Serialization.Ssz.Codec.Root
import all EthLib.Serialization.Ssz.Codec.Serialize

/-! The slot-one block has a distinct root and passes the validated state transition. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

attribute [local cbv_eval] hashTreeRootAtM.eq_def depthFor.eq_def SszType.hashTreeRoot_eq
  zeroSubtree_eq layoutChunksAtM.eq_def serialize.eq_def serializeSequence.eq_def
  serializeStruct.eq_def serializeEach.eq_def serializeEachFrom.eq_def serializeFields.eq_def
  serializeFieldsFrom.eq_def

/-- The first block commits to the certified post-state. -/
def signedBlock : SignedBeaconBlock preset .phase0 := ⟨firstBlock postRoot, default⟩

/-- The first block's root, certified by `first_block_root`. -/
def blockRoot : Root := ⟨#[187, 106, 2, 157, 164, 174, 50, 94, 64, 86, 77, 165, 90, 179, 115, 121,
  58, 239, 85, 142, 153, 254, 40, 14, 161, 247, 10, 126, 170, 172, 58, 203], by decide⟩

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option cbv.maxSteps 1000000 in
/-- The header and the previously certified body determine the first block's root. -/
theorem first_block_root : SszType.hashTreeRoot signedBlock.message = .ok blockRoot := by
  rw [← BeaconBlock.hashTreeRoot_header (block := signedBlock.message) body_root,
    SszType.hashTreeRoot_eq]
  cbv

/-- The first block cannot collide with the initialized anchor entry. -/
theorem blockRoot_ne_anchorRoot : blockRoot ≠ anchorRoot := by decide

/-- The first block does not occupy the anchor's excluded zero parent root. -/
theorem blockRoot_ne_zero : blockRoot ≠ Vector.replicate 32 0 := by decide

set_option maxRecDepth 10000 in
/-- The chosen signature checker accepts once the domain and signing root exist. -/
theorem first_signature : verifyBlockSignature config .acceptAll advanced signedBlock =
    .ok true := by
  let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
  let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  obtain ⟨domain, domainOk⟩ := getDomain_total config advanced DOMAIN_BEACON_PROPOSER none
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total signedBlock.message domain
  have found : getValidator advanced signedBlock.message.proposerIndex =
      .ok (validator 200) := rfl
  simp only [verifyBlockSignature, found, domainOk, rootOk,
    liftAccessor, liftSsz, Except.mapError, bind, Except.bind]
  rfl

set_option maxRecDepth 10000 in
/-- The complete state transition accepts the block with result validation enabled.

The state-root check uses `post_root`; no equality of hash outputs is assumed. -/
theorem first_transition :
    stateTransition config .acceptAll (.constant true) (state bodyRoot) signedBlock true =
      .ok postState := by
  have processed : processBlock config .acceptAll (.constant true) advanced signedBlock.message =
      .ok postState := first_block postRoot
  simp only [stateTransition, show signedBlock.message.slot = 1 from rfl, first_slot,
    applySignedBlock, checkBlockSignature, checkStateRoot, ↓reduceIte,
    first_signature, processed, post_root, liftSsz, Except.mapError,
    bind, Except.bind]
  rfl

end EthLib.Consensus.Models.Network.FiveValidatorWitness
