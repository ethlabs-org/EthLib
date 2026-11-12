module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Basic
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates
-- These equations expose SSZ's mutual recursion to the certificate evaluator.
import all EthLib.Serialization.Ssz.Merkle.Merkleize
import all EthLib.Serialization.Ssz.Codec.Root
import all EthLib.Serialization.Ssz.Codec.Serialize

/-! Kernel certificate for the witness's empty phase0 block body. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

attribute [local cbv_eval] hashTreeRootAtM.eq_def depthFor.eq_def SszType.hashTreeRoot_eq
  zeroSubtree_eq layoutChunksAtM.eq_def serialize.eq_def serializeSequence.eq_def
  serializeStruct.eq_def serializeEach.eq_def serializeEachFrom.eq_def serializeFields.eq_def
  serializeFieldsFrom.eq_def

/-- The root certified below for the witness's empty phase0 body. -/
def bodyRoot : Root := ⟨#[204, 182, 36, 96, 105, 43, 224, 236, 129, 59, 86, 190,
  151, 246, 138, 130, 207, 87, 171, 193, 2, 226, 123, 244, 158, 191, 65, 144, 255, 34, 238, 221],
  by decide⟩

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
set_option cbv.maxSteps 10000000 in
/-- The displayed body root agrees with the SSZ definition, checked by the kernel. -/
theorem body_root : SszType.hashTreeRoot body = .ok bodyRoot := by
  let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
  let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  rw [SszType.hashTreeRoot_eq]
  cbv

end EthLib.Consensus.Models.Network.FiveValidatorWitness
