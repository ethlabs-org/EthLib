module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Statements: honest stores agree on the blocks of an honest chain

This file states part of step 3 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

A block of an honest store is a block of its start, or came in a signed block of its view.

Its state is then the state transition of that signed block, from the state of its parent.

So two honest stores with the same start hold the same state at a root that both hold.

That needs the two stores to hold the same block wherever both hold one.

`OneBlockPerRoot` excludes conflicting held blocks at one root, without assuming hash injectivity.

Under synchrony, a block of an honest store reaches the view of each honest validator.

It is there one delay later.

An up-to-date honest store then holds it, when its checks of a new block pass.

The parent comes first, so the statement asks for the chain of the block down to the start.

The finalized checkpoint of the receiver must sit on that chain.

From Gloas the receiver must have verified each payload that the first store has verified.

The receiver must admit a delayed block held by an honest source when its block validation passes.

That last hypothesis covers the steps of the handler after the checks, and the votes of the block.

In the model here a vote that the store rejects makes the store reject its block.

The agreement follows two lemmas of [verified-fast-confirmation][vfc].

They are `WellFormedExecution.blocks_agree` and `WalkCoveredBy.receiver_walk`.

There a root names one block by construction, and a rejected event leaves the store as it is.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

section ForkChoice

variable {ν κ : Type*} [DecidableEq ν] {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
  {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
  {J : Set ν}

/-- A block of an honest store is a block of its start, or came in a signed block of its view.

In the second case the store holds the state of the parent of the block.

The state of the block is the state transition of the signed block from that state. -/
theorem Execution.exists_signed_of_blocks
    (e : Execution (forkChoice config checks sources signed sends) J) {u : ν} (honest : u ∈ J)
    {n : ℕ} {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state u).blocks[root]? = some block) :
    ((e.start u).blocks[root]? = some block ∧
        ((e.world n).state u).blockStates[root]? = (e.start u).blockStates[root]?) ∨
      ∃ signedBlock : SignedBeaconBlock preset fork, ∃ pre state,
        .block signedBlock ∈ (e.world n).view u ∧ signedBlock.message = block ∧
        SszType.hashTreeRoot signedBlock.message = .ok root ∧
        ((e.world n).state u).blockStates[block.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signedBlock true = .ok state ∧
        ((e.world n).state u).blockStates[root]? = some state := by
  sorry

/-- Two honest stores with one start hold the same state at a root that both hold.

The two stores must hold the same block wherever both hold one.

Both validators start from a store built from an anchor. -/
theorem Execution.blockStates_eq (e : Execution (forkChoice config checks sources signed sends) J)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {u w : ν} (first : u ∈ J) (second : w ∈ J) (startFirst : e.start u = anchor)
    (startSecond : e.start w = anchor) {n k : ℕ}
    (sameBlocks : ∀ (root : Root) left right, ((e.world n).state u).blocks[root]? = some left →
      ((e.world k).state w).blocks[root]? = some right → left = right)
    {root : Root} {left right : BeaconState preset fork}
    (leftFound : ((e.world n).state u).blockStates[root]? = some left)
    (rightFound : ((e.world k).state w).blockStates[root]? = some right) :
    left = right := by
  sorry

end ForkChoice

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Honest stores agree on blocks at shared roots.

This is a collision-exclusion hypothesis on held blocks, not hash injectivity. -/
def OneBlockPerRoot
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k (root : Root) left right,
    ((e.world n).state v).blocks[root]? = some left →
    ((e.world k).state u).blocks[root]? = some right → left = right

/-- A delayed block of an honest view passes the remaining handler checks when block validation passes.

Partial synchrony supplies view membership, not successful `onBlockWithVotes`.

The latter can fail on a carried vote even when the block transition succeeds.

This hypothesis isolates that admission gap at the receiver and at the delivery deadline. -/
def BlocksAdmitted
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (GST Δ : ℕ) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k signedBlock blockRoot state,
    .block signedBlock ∈ (e.world n).view v →
    ((e.world n).state v).blocks[blockRoot]? = some signedBlock.message →
    max (e.world n).time GST + Δ ≤ (e.world k).time →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    SszType.hashTreeRoot signedBlock.message = .ok blockRoot →
    ((e.world k).state u).validateOnBlock config checks sources signedBlock blockRoot =
      .ok state →
    ∃ after, ((e.world k).state u).onBlockWithVotes config checks sources signedBlock = .ok after

/-- Under synchrony, an up-to-date honest store holds a block that an honest store held before.

The first store holds the block at an event, and the receiver is up to date one delay later.

Both validators start from a store built from the anchor.

The two stores hold the same block wherever both hold one.

The receiver takes each signed block of its view that passes its checks of a new block.

From Gloas the receiver has verified each payload that the first store has verified.

In the first store, the chain of the block holds the finalized checkpoint of the receiver.

The receiver then holds the block.

It also finds each checkpoint block of the chain that the first store finds. -/
theorem Execution.blocks_of_partiallySynchronous {GST Δ : ℕ}
    (sync : e.PartiallySynchronous GST Δ)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e GST Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {n k : ℕ}
    (late : max (e.world n).time GST + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    (payloads : ∀ gloas : .glamsterdam ≤ fork, ∀ parent,
      ((e.world n).state v).isPayloadVerified gloas parent = true →
      ((e.world k).state u).isPayloadVerified gloas parent = true)
    {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state v).blocks[root]? = some block)
    (final : ((e.world n).state v).getCheckpointBlock root
      ((e.world k).state u).finalizedCheckpoint.epoch =
        .ok ((e.world k).state u).finalizedCheckpoint.root) :
    ((e.world k).state u).blocks[root]? = some block ∧
      ∀ epoch checkpointRoot,
        ((e.world n).state v).getCheckpointBlock root epoch = .ok checkpointRoot →
        ((e.world k).state u).getCheckpointBlock root epoch = .ok checkpointRoot := by
  sorry

/-- Admission at an earlier event gives knownness at every later event.

Finalized-chain compatibility is checked at admission, not at the later observation.

The caller can choose a pre-boundary admission event supplied by prompt processing.

This is the persistence step of the delivery argument in arXiv 2405.00549v4, Section 2. -/
theorem Execution.blocks_after_partiallySynchronous {GST Δ : ℕ}
    (sync : e.PartiallySynchronous GST Δ)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e GST Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {n arrival k : ℕ}
    (late : max (e.world n).time GST + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view u) ((e.world arrival).state u))
    (payloads : ∀ gloas : .glamsterdam ≤ fork, ∀ parent,
      ((e.world n).state v).isPayloadVerified gloas parent = true →
      ((e.world arrival).state u).isPayloadVerified gloas parent = true)
    {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state v).blocks[root]? = some block)
    (final : ((e.world n).state v).getCheckpointBlock root
      ((e.world arrival).state u).finalizedCheckpoint.epoch =
        .ok ((e.world arrival).state u).finalizedCheckpoint.root)
    (later : arrival ≤ k) : ((e.world k).state u).blocks[root]? = some block := by
  have held := (e.blocks_of_partiallySynchronous sync oneBlock admitted anchored start
    honest receiver late upToDate payloads found final).1
  exact e.blocks_of_le later held

end EthLib.Consensus.Models.Network
