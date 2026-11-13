module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.FirstSlot
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates

/-! The empty slot-one block changes the header, one RANDAO mix and the deposit-contract votes. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

/-- The slot-one block extends the anchor, with its resulting state root supplied separately. -/
def firstBlock (root : Root) : BeaconBlock preset .phase0 := ⟨1, 0, anchorRoot, root, body⟩

/-- Header processing replaces the anchor header, leaving the new state root unfilled. -/
def headed : BeaconState preset .phase0 :=
  { advanced with latestBlockHeader := ⟨1, 0, anchorRoot, Vector.replicate 32 0, bodyRoot⟩ }

set_option maxRecDepth 10000 in
/-- The first block has the selected proposer, the anchor parent and the certified body. -/
theorem first_header (root : Root) :
    processBlockHeader advanced (firstBlock root) = .ok headed := by
  have header : SszType.hashTreeRoot advanced.latestBlockHeader = .ok anchorRoot :=
    initial_header_root
  have bodyHash : SszType.hashTreeRoot (firstBlock root).body = .ok bodyRoot := body_root
  simp only [processBlockHeader, first_proposer, header, bodyHash,
    liftAccessor, liftSsz, Except.mapError, bind, Except.bind]
  rfl

/-- The hash of the empty body's zero RANDAO reveal, certified below. -/
def revealMix : Root := ⟨#[46, 169, 171, 145, 152, 209, 99, 128, 7, 64, 12, 210, 195, 190, 241, 204,
  116, 91, 134, 75, 118, 1, 26, 14, 27, 197, 33, 128, 172, 100, 82, 212], by decide⟩

set_option Elab.async false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
/-- The RANDAO mix is computed by SHA-256, not assumed. -/
theorem reveal_hash : Cryptography.Hash.Sha256.hash32 (packBytes body.randaoReveal) =
    revealMix := by
  cbv

/-- The initial epoch's zero RANDAO mix is replaced by the reveal's hash. -/
def mixed : BeaconState preset .phase0 :=
  { headed with randaoMixes := headed.randaoMixes.set 0 revealMix (by decide) }

set_option maxRecDepth 10000 in
/-- The accepting signature checker still requires the domain and signing root to exist. -/
theorem first_randao : processRandao config .acceptAll headed body = .ok mixed := by
  obtain ⟨domain, domainOk⟩ := getDomain_total config headed DOMAIN_RANDAO none
  obtain ⟨signingRoot, signingOk⟩ := computeSigningRoot_total (getCurrentEpoch headed) domain
  have proposer : getBeaconProposerIndex headed = .ok 0 := first_proposer
  have zeroMix : getRandaoMix headed (getCurrentEpoch headed) =
      .ok (Vector.replicate 32 0) := rfl
  have xor : Vector.zipWith (· ^^^ ·) (Vector.replicate 32 (0 : UInt8)) revealMix =
      revealMix := by ext i; simp
  simp only [processRandao, proposer, domainOk, signingOk, reveal_hash, zeroMix, xor,
    liftAccessor, liftSsz, Except.mapError, bind, Except.bind]
  rfl

/-- The post-state holds one deposit-contract vote and no attestations or operations. -/
def postState : BeaconState preset .phase0 :=
  { mixed with eth1DataVotes := fun _ => ⟨#[body.eth1Data (by decide)], by decide⟩ }

set_option maxRecDepth 10000 in
/-- Empty operations leave the balances, registry and checkpoints unchanged. -/
theorem first_block (root : Root) :
    processBlock config .acceptAll (.constant true) advanced (firstBlock root) = .ok postState := by
  simp only [processBlock, show ¬ Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    first_header, bind, Except.bind]
  change (do
    let state ← processRandao config .acceptAll headed body
    let state ← processEth1Data (by decide) state body
    processOperations config .acceptAll state body 0) = .ok postState
  rw [first_randao]
  rfl

end EthLib.Consensus.Models.Network.EightValidatorWitness
