module

public import EthLib.Consensus.Proofs.ForkChoice.Network

/-!
# Statements: the latest vote of a validator never goes back

This file states step 2 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

A store keeps one latest vote for each validator.

A vote replaces it only with a later rank: the target epoch before Gloas, the slot from Gloas.

So no handler removes a latest vote, and none lowers its rank.

An attester slashing adds equivocators, and leaves the latest votes as they are.

Along an execution of the network model, the same holds for each honest validator.

The statements follow two declarations of [verified-fast-confirmation][vfc].

They are `StoreLE` and `Execution.store_latest_message_ge_mono`.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store after : Store preset fork}

/-- One more vote keeps each latest vote, or replaces it with a vote of a later rank. -/
theorem recordVote_rank {equivocating : List ValidatorIndex} {message : LatestMessage fork}
    {messages : Std.TreeMap ValidatorIndex (LatestMessage fork)} {i j : ValidatorIndex}
    {old : LatestMessage fork} (found : messages[j]? = some old) :
    ∃ m, (recordVote equivocating message messages i)[j]? = some m ∧ old.rank ≤ m.rank := by
  sorry

/-- A run of votes keeps each latest vote, or replaces it with a vote of a later rank. -/
theorem foldl_recordVote_rank {equivocating : List ValidatorIndex} {message : LatestMessage fork}
    (indices : List ValidatorIndex) {messages : Std.TreeMap ValidatorIndex (LatestMessage fork)}
    {j : ValidatorIndex} {old : LatestMessage fork} (found : messages[j]? = some old) :
    ∃ m, (indices.foldl (recordVote equivocating message) messages)[j]? = some m ∧
      old.rank ≤ m.rank := by
  sorry

/-- An attestation keeps each latest vote, or replaces it with a vote of a later rank. -/
theorem onAttestation_latestMessages_rank {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool} {j : ValidatorIndex}
    {old : LatestMessage fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after)
    (found : store.latestMessages[j]? = some old) :
    ∃ m, after.latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  sorry

/-- A block with its votes keeps each latest vote, or replaces it with a vote of a later rank. -/
theorem onBlockWithVotes_latestMessages_rank {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {j : ValidatorIndex} {old : LatestMessage fork}
    (added : store.onBlockWithVotes config checks sources signed = .ok after)
    (found : store.latestMessages[j]? = some old) :
    ∃ m, after.latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  sorry

end Store

namespace Models.Network

/-- A move of an honest store keeps each latest vote, or replaces it with one of a later rank. -/
theorem Handles.latestMessages_rank {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork} {j : ValidatorIndex} {old : LatestMessage fork}
    (handles : Handles config checks sources time view store after)
    (found : store.latestMessages[j]? = some old) :
    ∃ m, after.latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  sorry

/-- Along an execution, an honest store keeps each latest vote, or holds one of a later rank.

The store at a later event holds a vote of that validator, at the same rank or later. -/
theorem Execution.latestMessages_rank {ν κ : Type*} [DecidableEq ν] {config : Config}
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J) {u : ν}
    (honest : u ∈ J) {n k : ℕ} (le : n ≤ k) {j : ValidatorIndex} {old : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[j]? = some old) :
    ∃ m, ((e.world k).state u).latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  sorry

end Models.Network

end EthLib.Consensus
