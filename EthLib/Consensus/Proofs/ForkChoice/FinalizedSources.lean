module

public import EthLib.Consensus.Proofs.ForkChoice.FinalizedOrigins

/-!
# Source votes behind realized finalization

Timed store origins connect historical count evidence to the finalizing source vote.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A finalized checkpoint after the anchor is the source of a vote from the chosen set.

The finalizing link's target is before the store's current epoch.

The four finalization cases use the current or previous target count.

The source is the old current or old previous justified checkpoint that the case finalizes.

Inherited anchor bits cannot finalize a checkpoint after the anchor epoch.

This is the signer part of Gasper Definition 4.9, arXiv 2003.03052v3.

It corresponds to the finalizing-link witness in VFC's
`acceptedGlobalFinalized_anchor_or_timedCertificate`.

The target epoch bound permits same-slot admission without an early-signer stake assumption. -/
theorem Execution.exists_signsSource_of_finalized {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (slotsPositive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {epoch : Epoch}
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (after : anchor.justifiedCheckpoint.epoch < ((e.world k).state w).finalizedCheckpoint.epoch)
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (large : ∀ (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ epoch →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (few : ∀ (state : BeaconState preset fork) (total : Gwei),
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ epoch →
      getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat) :
    ∃ v, p v ∧ ∃ n, ∃ m ∈ (e.world n).sent, ∃ data,
      (v, data) ∈ statements config checks anchorState anchorBlock m ∧
      data.source = ((e.world k).state w).finalizedCheckpoint ∧
      data.source.epoch < data.target.epoch ∧ data.target.epoch < epoch := by
  sorry

end EthLib.Consensus.Models.Network
