module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSets
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.Transition.FfgJustification
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# Statements: what the fast confirmation rule asks of the checkpoints of honest stores

This file names the facts of Casper FFG that the safety of the fast confirmation rule uses.

The rule is that of [arXiv 2405.00549v4][fcr].

The first two facts are definitions, and no theorem here proves them.

The theorems on the rule take them as hypotheses, and each definition may still change.

Each fact speaks of the stores of the honest validators along one execution.

A store counts a checkpoint as justified when it holds it, or a block of the store does.

The first two facts are the ones that accountable safety gives.

The finalized checkpoint of an honest store is on the chain of each later justified checkpoint.

Two justified checkpoints of one epoch are the same.

Neither names a quorum or a balance, and each holds up to a horizon, an epoch.

When one of them fails, two vote counts conflict.

A proof of accountable safety can then show that a third of the stake is slashable.

The third is less the change of balances up to the horizon.

So a theorem with the two facts as hypotheses gives one with that alternative in its conclusion.

The last two facts are not of that kind, since their failure makes no validator slashable.

Each justified checkpoint after the anchor is the target of the vote of an honest validator.

Take an honest third of the stake at one epoch.

Each justified checkpoint of that epoch is the target of the vote of one of them.

Both follow from one count, `Execution.exists_signsTarget_of_justified`.

The proof of that count is a placeholder.

A justified checkpoint has the votes of two thirds of an active balance.

The balance is that of the state that counts the votes.

So a set of validators signs it when the validators outside the set hold less than two thirds.

For the first fact the set is the honest validators, and the bound is Assumption 2 of the paper.

For the second it is the honest third, and the bound is the count that the rule makes.

H reads the Byzantine bound directly in the state that counts the votes.

N transports a particular honest subset from the pulled-up head state.

`DriftAtMost` bounds that subset's adverse weight shift by a number of Gwei.

Four lemmas of [verified-fast-confirmation][vfc] state these facts.

Two are `certified_finalized_prefix` and `certified_justified_unique`.

Two are `globalJustified_honestTarget` and `one_third_honest_intersects_two_thirds`.

There the set of validators is fixed, and the proofs count the stake of one registry.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A checkpoint that a store counts as justified.

It is the justified checkpoint of the store, realized or not, or that of a block of the store.

A block has the justified checkpoint of its state and its unrealized justification.

A checkpoint that a block gives counts only after the genesis epoch.

At the genesis epoch a state names no justified block: the genesis state has a zero root there.

Justification and finalization change nothing in the first two epochs.

So a state reaches a genesis-epoch checkpoint only from the genesis state, never from votes.

The store's own checkpoints still count at every epoch: at genesis they name the anchor. -/
def Store.Justified (store : Store preset fork) (checkpoint : Checkpoint) : Prop :=
  checkpoint = store.justifiedCheckpoint ∨ checkpoint = store.unrealizedJustifiedCheckpoint ∨
    GENESIS_EPOCH < checkpoint.epoch ∧
      ((∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.currentJustifiedCheckpoint) ∨
      ∃ root : Root, store.unrealizedJustifications[root]? = some checkpoint)

/-- A state where a store can count votes: the state of one of its blocks, maybe at a later slot.

The state transition counts the votes for a target at the end of an epoch, after empty slots.

The rule and the fork choice count them in the state of a block, as it is or at a later slot. -/
def Store.Counts (store : Store preset fork) (config : Config)
    (state : BeaconState preset fork) : Prop :=
  ∃ (root : Root) (blockState : BeaconState preset fork),
    store.blockStates[root]? = some blockState ∧
      (state = blockState ∨
        ∃ (checks : SignatureChecks) (slot : Slot) (childRoot : Root)
          (child : BeaconBlock preset fork),
          store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
          slot ≤ child.slot ∧
          processSlots config checks blockState slot = .ok state)

/-- The validators whose votes a state can count for a target.

Each is active in the epoch of the state or in the one before, and is not slashed. -/
def quorumVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  {v ∈ (getActiveValidatorIndices state (getCurrentEpoch state) ++
      getActiveValidatorIndices state (getPreviousEpoch state)).toFinset |
    (state.validators.data[v.toNat]?.map (·.slashed)).getD true = false}

/-- A validator is not slashed in a state.

A validator that the state does not hold is not slashed in it. -/
def NotSlashed (state : BeaconState preset fork) (v : ValidatorIndex) : Prop :=
  (state.validators.data[v.toNat]?.map (·.slashed)).getD false = false

/-- The validators that are active in the epoch of a state. -/
def activeVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

/-- The balances of a state have drifted from those of a reference by at most a number of Gwei.

The reference is the state where a bound on some validators is known.

The state is one that counts votes for a checkpoint.

Take any set of validators that holds no validator slashed in the state, and those outside it.

So the stake that a slashed validator loses is no drift.

In the state, those outside whose votes can count hold some share of the active balance.

Three times their stake less twice the active balance is the excess over two thirds.

That excess is at most the same excess in the reference plus the drift.

In the reference, the stake is that of the active validators.

The drift is the least number that moves a bound of two thirds from the reference to the state.

A count for each validator gives a bound on the drift, as a sum of three terms.

Each term counts only validators that are not slashed in the state.

The first is twice the active stake of the reference that is no longer active stake of the state.

The second is the stake that the active validators of the state have gained since the reference.

The third is three times such a gain of a voter that is active only in the epoch before.

With fixed balances the third is zero for each validator that is active in the reference.

No theorem here proves that bound. -/
def DriftAtMost (reference state : BeaconState preset fork) (drift : ℕ) : Prop :=
  ∀ (p : ValidatorIndex → Prop) [DecidablePred p] (total : Gwei),
    (∀ v, p v → NotSlashed state v) →
    getTotalActiveBalance state = .ok total →
    3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} +
        2 * stake (fun v => balanceAt reference v.toNat) (activeVoters reference) ≤
      3 * stake (fun v => balanceAt reference v.toNat) {v ∈ activeVoters reference | ¬p v} +
        2 * total.toNat + drift

/-- The validators outside a set hold less than two thirds of a state, from a reference.

No validator of the set is slashed in the state.

In the reference they hold less than two thirds of the active stake, by more than the drift. -/
theorem DriftAtMost.lt_two_mul_total {reference state : BeaconState preset fork} {drift : ℕ}
    (bound : DriftAtMost reference state drift) (p : ValidatorIndex → Prop) [DecidablePred p]
    (clean : ∀ v, p v → NotSlashed state v)
    (margin : 3 * stake (fun v => balanceAt reference v.toNat)
        {v ∈ activeVoters reference | ¬p v} + drift <
      2 * stake (fun v => balanceAt reference v.toNat) (activeVoters reference))
    {total : Gwei} (totalOk : getTotalActiveBalance state = .ok total) :
    3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
      2 * total.toNat := by
  have moved := bound p total clean totalOk
  omega

/-- A passing justification test includes a voter of a set whose complement is too small.

The vote retains both its source and target through `LinkVote`.

The active stake bound excludes a test that passes only because of the minimum balance. -/
theorem exists_linkVote_of_justificationTest {state : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)} {current : Bool}
    {attesting : List ValidatorIndex} {total balance threshold weight : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state attesting = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (counted : ∀ v ∈ attesting, v ∈ quorumVoters state ∧
      ∃ data, (v, data) ∈ attested ∧ LinkVote state current v.toNat (v, data))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat) :
    ∃ v data, p v ∧ (v, data) ∈ attested ∧ LinkVote state current v.toNat (v, data) := by
  classical
  by_contra missing
  have subset : attesting.toFinset ⊆ {v ∈ quorumVoters state | ¬p v} := by
    intro v member
    obtain ⟨quorum, data, signed, link⟩ := counted v (List.mem_toFinset.mp member)
    exact Finset.mem_filter.mpr ⟨quorum, fun good => missing ⟨v, data, good, signed, link⟩⟩
  have bounded := stake_mono (w := fun v => balanceAt state v.toNat) subset
  have tested := (justificationTest_iff_stake (getTotalActiveBalance_ok totalOk)
    balanceOk thresholdOk weightOk large).mp passed
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  have floor : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun v => balanceAt state v.toNat) (activeVoters state) := by omega
  change total.toNat = max _ (stake (fun v => balanceAt state v.toNat) (activeVoters state))
    at totalEq
  rw [Nat.max_eq_right floor] at totalEq
  change 2 * stake (fun v => balanceAt state v.toNat) (activeVoters state) ≤ _ at tested
  omega

/-- An active, unslashed validator of either recent epoch belongs to the counting quorum. -/
theorem mem_quorumVoters_of_active {state : BeaconState preset fork} {current : Bool}
    {v : ValidatorIndex} {validator : Validator}
    (active : v ∈ getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state))
    (found : getValidator state v = .ok validator) (clean : validator.slashed = false) :
    v ∈ quorumVoters state := by
  have read : state.validators.data[v.toNat]? = some validator := by
    unfold getValidator at found
    split at found
    · cases found
      assumption
    · cases found
  apply Finset.mem_filter.mpr
  constructor
  · apply List.mem_toFinset.mpr
    cases current
    · exact List.mem_append_right _ active
    · exact List.mem_append_left _ active
  · simp [read, clean]

/-- A counted target flag supplies a quorum member and its vote, including the source. -/
theorem TargetFlagsVoted.quorum_attester {state : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)} (altair : .altair ≤ fork)
    (holds : TargetFlagsVoted attested state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (current : Bool)
    {indices : List ValidatorIndex}
    (counted : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices) :
    v ∈ quorumVoters state ∧
      ∃ data, (v, data) ∈ attested ∧ LinkVote state current v.toNat (v, data) := by
  obtain ⟨active, ⟨validator, found, clean⟩, -⟩ :=
    mem_getUnslashedParticipatingIndices counted v member
  refine ⟨mem_quorumVoters_of_active active found clean, ?_⟩
  obtain ⟨-, ⟨index, data⟩, link, signed⟩ := holds.attester altair late current counted member
  have same : index = v := UInt64.toNat_inj.mp link.1
  subst index
  exact ⟨data, signed, link⟩

/-- A counted pending attestation supplies a quorum member and its source and target vote. -/
theorem PendingVoted.quorum_attester {state : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)} (before : fork < .altair)
    (holds : PendingVoted attested state) (early : JustifiedEarly state) (current : Bool)
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingTargetAttestations state before
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    {indices : List ValidatorIndex}
    (counted : getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices) :
    v ∈ quorumVoters state ∧
      ∃ data, (v, data) ∈ attested ∧ LinkVote state current v.toNat (v, data) := by
  obtain ⟨active, data, link, signed⟩ := holds.attester before early current matching counted member
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at counted
  obtain ⟨signers, -, filtered⟩ := counted
  have passes := passes_of_mem_filterM_ok filtered member
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passes
  obtain ⟨validator, found, clean⟩ := passes
  exact ⟨mem_quorumVoters_of_active active found (by simpa using clean), data, signed, link⟩

/-- A changed justified checkpoint has a counted vote from a set with a small complement.

The source is retained as the checkpoint used by the successful justification test. -/
theorem exists_linkVote_of_weighJustification {state after : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)}
    {previous current : List ValidatorIndex} {total previousBalance currentBalance : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (previousOk : getTotalBalance state previous = .ok previousBalance)
    (currentOk : getTotalBalance state current = .ok currentBalance)
    (counted : ∀ (recent : Bool), ∀ v ∈ (if recent then current else previous),
      v ∈ quorumVoters state ∧
        ∃ data, (v, data) ∈ attested ∧ LinkVote state recent v.toNat (v, data))
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat)
    (computed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      ∃ recent v data, p v ∧ (v, data) ∈ attested ∧
        LinkVote state recent v.toNat (v, data) ∧
          data.target = after.currentJustifiedCheckpoint := by
  rcases weighJustificationAndFinalization_currentJustified computed with
    ⟨same, -⟩ | ⟨recent, threshold, weight, thresholdOk, weightOk, passed, epoch, rootOk⟩
  · exact .inl same
  have balanceOk : getTotalBalance state (if recent then current else previous) =
      .ok (if recent then currentBalance else previousBalance) := by
    cases recent <;> assumption
  obtain ⟨v, data, good, signed, link⟩ := exists_linkVote_of_justificationTest totalOk
    balanceOk thresholdOk weightOk passed large (counted recent) p few
  refine .inr ⟨recent, v, data, good, signed, link, ?_⟩
  have targetEpoch := link.2.1.trans epoch.symm
  have targetRoot := link.2.2.2
  rw [targetEpoch, rootOk, Except.ok.injEq] at targetRoot
  cases h : data.target
  cases h' : after.currentJustifiedCheckpoint
  simp_all

/-- A justification step either keeps its checkpoint or supplies a vote for its new link. -/
private theorem exists_linkVote_of_processJustification {state after : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)}
    (flags : TargetFlagsVoted attested state) (pending : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : ∀ total, getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat)
        {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat)
    (computed : processJustificationAndFinalization state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      ∃ recent v data, p v ∧ (v, data) ∈ attested ∧
        LinkVote state recent v.toNat (v, data) ∧
          data.target = after.currentJustifiedCheckpoint := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl (computed ▸ rfl)
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
    apply exists_linkVote_of_weighJustification totalOk previousBalanceOk currentBalanceOk
      (fun recent v member => ?_) large p (few total totalOk) weighed
    cases recent
    · exact flags.quorum_attester altair late false previousOk member
    · exact flags.quorum_attester altair late true currentOk member
  · rename_i notAltair
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl (computed ▸ rfl)
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩,
      currentBalance, ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    apply exists_linkVote_of_weighJustification totalOk previousBalanceOk currentBalanceOk
      (fun recent v member => ?_) large p (few total totalOk) weighed
    have early : JustifiedEarly state := fun h => absurd h late
    cases recent
    · exact pending.quorum_attester (Nat.lt_of_not_le notAltair) early false
        previousOk previousIndicesOk member
    · exact pending.quorum_attester (Nat.lt_of_not_le notAltair) early true
        currentOk currentIndicesOk member

/-- A set bit zero records a source vote for the current epoch of the counting state.

The previous justified checkpoint after the count is the source of that vote.

Keeping this witness across the epoch boundary supplies the old-bit case of finalization. -/
private theorem exists_sourceVote_of_weighJustification_bit_zero
    {state after : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)}
    {current : List ValidatorIndex} {total previousBalance currentBalance : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (currentOk : getTotalBalance state current = .ok currentBalance)
    (counted : ∀ v ∈ current, v ∈ quorumVoters state ∧
      ∃ data, (v, data) ∈ attested ∧ LinkVote state true v.toNat (v, data))
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat)
    (computed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after)
    (set : after.justificationBits.bits[0] = true) :
    ∃ v data, p v ∧ (v, data) ∈ attested ∧
      data.source = after.previousJustifiedCheckpoint ∧
      data.target.epoch = getCurrentEpoch state := by
  obtain ⟨threshold, _, currentWeight, thresholdOk, _, currentWeightOk, newCurrent, _⟩ :=
    weighJustificationAndFinalization_bits computed
  obtain ⟨passed, -⟩ := newCurrent set
  obtain ⟨v, data, good, signed, link⟩ := exists_linkVote_of_justificationTest totalOk
    currentOk thresholdOk currentWeightOk passed large counted p few
  obtain ⟨previous, -⟩ := weighJustificationAndFinalization_checkpoints computed
  exact ⟨v, data, good, signed, link.2.2.1.trans previous.symm, link.2.1⟩

/-- A changed finalized checkpoint has a source vote from a passing count or the old bit zero.

The old-bit witness retains its original vote and may come from an earlier counting state.

The vote set must therefore contain both the current counts and that earlier witness. -/
theorem exists_sourceVote_of_weighJustification {state after : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)}
    {previous current : List ValidatorIndex} {total previousBalance currentBalance : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (previousOk : getTotalBalance state previous = .ok previousBalance)
    (currentOk : getTotalBalance state current = .ok currentBalance)
    (counted : ∀ (recent : Bool), ∀ v ∈ (if recent then current else previous),
      v ∈ quorumVoters state ∧
        ∃ data, (v, data) ∈ attested ∧ LinkVote state recent v.toNat (v, data))
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat)
    (oldBit : state.justificationBits.bits[0] = true →
      ∃ v data, p v ∧ (v, data) ∈ attested ∧
        data.source = state.previousJustifiedCheckpoint ∧
        data.target.epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (computed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint ∨
      ∃ v data, p v ∧ (v, data) ∈ attested ∧
        data.source = after.finalizedCheckpoint ∧ data.source.epoch < data.target.epoch ∧
        data.target.epoch ≤ getCurrentEpoch state := by
  obtain ⟨threshold, previousWeight, currentWeight, thresholdOk, previousWeightOk,
    currentWeightOk, newCurrent, newPrevious, -, -, finalized⟩ :=
    weighJustificationAndFinalization_bits computed
  rcases finalized with same | ⟨same, set, distance⟩ | ⟨same, set, distance⟩
  · exact .inl same
  · obtain ⟨passed, -⟩ := newCurrent set
    obtain ⟨v, data, good, signed, link⟩ := exists_linkVote_of_justificationTest totalOk
      currentOk thresholdOk currentWeightOk passed large (counted true) p few
    have target : data.target.epoch = getCurrentEpoch state := link.2.1
    have source : data.source = state.currentJustifiedCheckpoint := link.2.2.1
    refine .inr ⟨v, data, good, signed, source.trans same.symm, ?_, ?_⟩
    · rw [source, target, UInt64.lt_iff_toNat_lt]
      rcases distance with one | ⟨-, two⟩ <;> omega
    · exact UInt64.le_of_eq target
  · have witness : ∃ v data, p v ∧ (v, data) ∈ attested ∧
        data.source = state.previousJustifiedCheckpoint ∧
        data.target.epoch.toNat = (getCurrentEpoch state).toNat - 1 := by
      rcases newPrevious set with ⟨passed, -⟩ | old
      · obtain ⟨v, data, good, signed, link⟩ := exists_linkVote_of_justificationTest totalOk
          previousOk thresholdOk previousWeightOk passed large (counted false) p few
        refine ⟨v, data, good, signed, link.2.2.1, ?_⟩
        rw [link.2.1]
        exact getPreviousEpoch_toNat state
      · obtain ⟨v, data, good, signed, source, target⟩ := oldBit old
        exact ⟨v, data, good, signed, source, by omega⟩
    obtain ⟨v, data, good, signed, source, target⟩ := witness
    refine .inr ⟨v, data, good, signed, source.trans same.symm, ?_, ?_⟩
    · rw [source, UInt64.lt_iff_toNat_lt]
      rcases distance with two | ⟨-, three⟩ <;> omega
    · rw [UInt64.le_iff_toNat_le]
      omega

/-- A finalization step retains its checkpoint or supplies a source vote from the chosen set.

An inherited bit zero supplies its earlier vote rather than a fresh count in this state. -/
private theorem exists_sourceVote_of_processJustification {state after : BeaconState preset fork}
    {attested : Set (ValidatorIndex × AttestationData)}
    (flags : TargetFlagsVoted attested state) (pending : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : ∀ total, getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat)
        {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat)
    (oldBit : state.justificationBits.bits[0] = true →
      ∃ v data, p v ∧ (v, data) ∈ attested ∧
        data.source = state.previousJustifiedCheckpoint ∧
        data.target.epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (computed : processJustificationAndFinalization state = .ok after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint ∨
      ∃ v data, p v ∧ (v, data) ∈ attested ∧
        data.source = after.finalizedCheckpoint ∧ data.source.epoch < data.target.epoch ∧
        data.target.epoch ≤ getCurrentEpoch state := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl (computed ▸ rfl)
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
    apply exists_sourceVote_of_weighJustification totalOk previousBalanceOk currentBalanceOk
      (fun recent v member => ?_) large p (few total totalOk) oldBit weighed
    cases recent
    · exact flags.quorum_attester altair late false previousOk member
    · exact flags.quorum_attester altair late true currentOk member
  · rename_i notAltair
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl (computed ▸ rfl)
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩,
      currentBalance, ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    apply exists_sourceVote_of_weighJustification totalOk previousBalanceOk currentBalanceOk
      (fun recent v member => ?_) large p (few total totalOk) oldBit weighed
    have early : JustifiedEarly state := fun h => absurd h late
    cases recent
    · exact pending.quorum_attester (Nat.lt_of_not_le notAltair) early false
        previousOk previousIndicesOk member
    · exact pending.quorum_attester (Nat.lt_of_not_le notAltair) early true
        currentOk currentIndicesOk member

/-- Source-link evidence carried by bit zero and the finalized checkpoint.

The relation retains the evidence of the original count, including its counting state.

Checkpoints at or before the anchor need no such evidence.

The epoch is the current epoch between steps, and the next epoch just after a count. -/
structure FinalizationSources (link : Checkpoint → Epoch → Prop) (anchorEpoch : Epoch)
    (epoch : Nat) (state : BeaconState preset fork) : Prop where
  bitZero : state.justificationBits.bits[0] = true →
    state.previousJustifiedCheckpoint.epoch ≤ anchorEpoch ∨
      ∃ target, target.toNat + 1 = epoch ∧ link state.previousJustifiedCheckpoint target
  finalized : state.finalizedCheckpoint.epoch ≤ anchorEpoch ∨
    ∃ target, state.finalizedCheckpoint.epoch < target ∧ target.toNat < epoch ∧
      link state.finalizedCheckpoint target

/-- A frame retains the source evidence without changing its epoch. -/
theorem FinalizationSources.of_frame {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {epoch : Nat} {state after : BeaconState preset fork}
    (holds : FinalizationSources link anchorEpoch epoch state) (frame : Frame state after) :
    FinalizationSources link anchorEpoch epoch after := by
  constructor
  · rw [frame.justificationBits, frame.previousJustified]
    exact holds.bitZero
  · rw [frame.finalized]
    exact holds.finalized

/-- An anchor whose checkpoints are bounded by its epoch needs no source-link evidence. -/
theorem FinalizationSources.anchor {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {epoch : Nat} {state : BeaconState preset fork}
    (previous : state.previousJustifiedCheckpoint.epoch ≤ anchorEpoch)
    (finalized : state.finalizedCheckpoint.epoch ≤ anchorEpoch) :
    FinalizationSources link anchorEpoch epoch state :=
  ⟨fun _ => .inl previous, .inl finalized⟩

/-- The four finalization cases carry source evidence into the next epoch.

An old bit zero reuses its original link, even when the previous-target count fails. -/
theorem FinalizationSources.weigh {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {state after : BeaconState preset fork}
    {total previousBalance currentBalance : Gwei}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (counts : ∀ (recent : Bool) (threshold weight : Gwei),
      mulChecked total 2 = .ok threshold →
      mulChecked (if recent then currentBalance else previousBalance) 3 = .ok weight →
      threshold ≤ weight →
      anchorEpoch <
        (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint).epoch →
      link (if recent then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint)
        (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (computed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after) :
    FinalizationSources link anchorEpoch ((getCurrentEpoch state).toNat + 1) after := by
  obtain ⟨threshold, previousWeight, currentWeight, thresholdOk, previousOk, currentOk,
    newCurrent, newPrevious, -, -, finalized⟩ := weighJustificationAndFinalization_bits computed
  obtain ⟨previous, -⟩ := weighJustificationAndFinalization_checkpoints computed
  have previousNat := getPreviousEpoch_toNat state
  constructor
  · intro set
    obtain ⟨passed, -⟩ := newCurrent set
    rw [previous]
    by_cases low : state.currentJustifiedCheckpoint.epoch ≤ anchorEpoch
    · exact .inl low
    · exact .inr ⟨getCurrentEpoch state, rfl,
        counts true _ _ thresholdOk currentOk passed (UInt64.not_le.mp low)⟩
  · rcases finalized with same | ⟨same, set, distance⟩ | ⟨same, set, distance⟩
    · rw [same]
      rcases holds.finalized with low | ⟨target, later, before, counted⟩
      · exact .inl low
      · exact .inr ⟨target, later, by omega, counted⟩
    · rw [same]
      obtain ⟨passed, -⟩ := newCurrent set
      by_cases low : state.currentJustifiedCheckpoint.epoch ≤ anchorEpoch
      · exact .inl low
      refine .inr ⟨getCurrentEpoch state, ?_, by omega,
        counts true _ _ thresholdOk currentOk passed (UInt64.not_le.mp low)⟩
      rw [UInt64.lt_iff_toNat_lt]
      rcases distance with one | ⟨-, two⟩ <;> omega
    · rw [same]
      by_cases low : state.previousJustifiedCheckpoint.epoch ≤ anchorEpoch
      · exact .inl low
      rcases newPrevious set with ⟨passed, -⟩ | old
      · refine .inr ⟨getPreviousEpoch state, ?_, by omega,
          counts false _ _ thresholdOk previousOk passed (UInt64.not_le.mp low)⟩
        rw [UInt64.lt_iff_toNat_lt]
        rcases distance with two | ⟨-, three⟩ <;> omega
      · rcases holds.bitZero old with low | ⟨target, epoch, counted⟩
        · exact .inl low
        · refine .inr ⟨target, ?_, by omega, counted⟩
          rw [UInt64.lt_iff_toNat_lt]
          rcases distance with two | ⟨-, three⟩ <;> omega

/-- Justification carries the source evidence, with counts needed only above the anchor. -/
theorem FinalizationSources.process {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {state after : BeaconState preset fork}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (counts : ∀ total previous current,
      weighJustificationAndFinalization state total previous current = .ok after →
      ∀ (recent : Bool) (threshold weight : Gwei),
        mulChecked total 2 = .ok threshold →
        mulChecked (if recent then current else previous) 3 = .ok weight →
        threshold ≤ weight →
        anchorEpoch <
          (if recent then state.currentJustifiedCheckpoint
            else state.previousJustifiedCheckpoint).epoch →
        link (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint)
          (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (computed : processJustificationAndFinalization state = .ok after) :
    FinalizationSources link anchorEpoch ((getCurrentEpoch state).toNat + 1) after := by
  have early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 → after = state →
      FinalizationSources link anchorEpoch ((getCurrentEpoch state).toNat + 1) after := by
    intro small same
    subst after
    have smallNat := UInt64.le_iff_toNat_le.mp small
    have settledNat := UInt64.le_iff_toNat_le.mp settled
    rw [getPreviousEpoch_toNat] at settledNat
    have previous := UInt64.le_iff_toNat_le.mp ordered.2
    have finalized := UInt64.le_iff_toNat_le.mp ordered.1
    have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
    rw [one] at smallNat
    apply FinalizationSources.anchor <;> rw [UInt64.le_iff_toNat_le] <;> omega
  have weighed : ∀ total previous current,
      weighJustificationAndFinalization state total previous current = .ok after →
      FinalizationSources link anchorEpoch ((getCurrentEpoch state).toNat + 1) after := by
    intro total previous current ok
    exact holds.weigh (counts total previous current ok) ok
  unfold processJustificationAndFinalization at computed
  split at computed
  · unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · exact early ‹_› (Except.ok.inj computed).symm
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, total, _, previous, _, current, _, ok⟩ := computed
      exact weighed total previous current ok
  · split at computed
    · exact early ‹_› (Except.ok.inj computed).symm
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, total, _, previous, _, current, _, ok⟩ := computed
      exact weighed total previous current ok

/-- The source invariant uses the actual participating indices and balances of each count. -/
theorem FinalizationSources.process_of_counts {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {state after : BeaconState preset fork}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (counts : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ (recent : Bool) (indices : List ValidatorIndex) (total balance threshold weight : Gwei),
      ((∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations = .ok indices) →
      getTotalActiveBalance state = .ok total → getTotalBalance state indices = .ok balance →
      mulChecked total 2 = .ok threshold → mulChecked balance 3 = .ok weight →
      threshold ≤ weight →
      anchorEpoch < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
      link (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint)
        (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (computed : processJustificationAndFinalization state = .ok after) :
    FinalizationSources link anchorEpoch ((getCurrentEpoch state).toNat + 1) after := by
  have early (small : getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (same : after = state) :
      FinalizationSources link anchorEpoch ((getCurrentEpoch state).toNat + 1) after := by
    subst after
    have smallNat := UInt64.le_iff_toNat_le.mp small
    have settledNat := UInt64.le_iff_toNat_le.mp settled
    have orderedNat := UInt64.le_iff_toNat_le.mp ordered.2
    have finalizedNat := UInt64.le_iff_toNat_le.mp ordered.1
    rw [getPreviousEpoch_toNat] at settledNat
    have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
    rw [one] at smallNat
    apply FinalizationSources.anchor <;> rw [UInt64.le_iff_toNat_le] <;> omega
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · exact early ‹_› (Except.ok.inj computed).symm
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
    apply holds.weigh ?_ weighed
    intro recent threshold weight thresholdOk weightOk passed above
    cases recent
    · exact counts late false previous total previousBalance threshold weight
        (.inl ⟨altair, previousOk⟩) totalOk previousBalanceOk thresholdOk weightOk passed above
    · exact counts late true current total currentBalance threshold weight
        (.inl ⟨altair, currentOk⟩) totalOk currentBalanceOk thresholdOk weightOk passed above
  · rename_i notAltair
    split at computed
    · exact early ‹_› (Except.ok.inj computed).symm
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩,
      currentBalance, ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    apply holds.weigh ?_ weighed
    intro recent threshold weight thresholdOk weightOk passed above
    cases recent
    · exact counts late false previousIndices total previousBalance threshold weight
        (.inr ⟨Nat.lt_of_not_le notAltair, previous, previousOk, previousIndicesOk⟩)
        totalOk previousBalanceOk thresholdOk weightOk passed above
    · exact counts late true currentIndices total currentBalance threshold weight
        (.inr ⟨Nat.lt_of_not_le notAltair, current, currentOk, currentIndicesOk⟩)
        totalOk currentBalanceOk thresholdOk weightOk passed above

/-- A slot step carries historical source links and makes new finalizing targets strictly older.

Only an epoch boundary needs count evidence, in the state after slot caching. -/
theorem FinalizationSources.advanceSlot {config : Config} {checks : SignatureChecks}
    {link : Checkpoint → Epoch → Prop} {anchorEpoch : Epoch}
    {state after : BeaconState preset fork}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (counts : ∀ cached justified, processSlot state = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      FinalizationSources link anchorEpoch (getCurrentEpoch cached).toNat cached →
      FinalizationSources link anchorEpoch ((getCurrentEpoch cached).toNat + 1) justified)
    (computed : advanceSlot config checks state = .ok after) :
    FinalizationSources link anchorEpoch (getCurrentEpoch after).toNat after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok computed
  have frame := frame_processSlot cachedOk
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have cachedHolds :
      FinalizationSources link anchorEpoch (getCurrentEpoch cached).toNat cached := by
    rw [cachedEpoch]
    exact holds.of_frame frame
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨justified, justifiedOk, epochFrame⟩ := processEpoch_frame epochedOk
    have newHolds := (counts cached justified cachedOk justifiedOk cachedHolds).of_frame
      epochFrame.toFrame
    have epoch : (getCurrentEpoch after).toNat = (getCurrentEpoch cached).toNat + 1 := by
      rw [cachedEpoch, getCurrentEpoch_toNat, getCurrentEpoch_toNat, afterEq]
      exact nextSlot_epoch_of_boundary sum boundary
    rw [epoch]
    rw [afterEq]
    exact ⟨newHolds.bitZero, newHolds.finalized⟩
  · rename_i inside
    have same : epoched = cached := (Except.ok.inj epochedOk).symm
    have epoch : getCurrentEpoch after = getCurrentEpoch cached := by
      apply UInt64.toNat_inj.mp
      rw [cachedEpoch, getCurrentEpoch_toNat, getCurrentEpoch_toNat, afterEq]
      exact nextSlot_epoch_of_inside sum inside
    rw [epoch]
    rw [afterEq, same]
    exact ⟨cachedHolds.bitZero, cachedHolds.finalized⟩

/-- A slot run carries source evidence from the anchor through every epoch boundary. -/
theorem FinalizationSources.advanceSlots {config : Config} {checks : SignatureChecks}
    {link : Checkpoint → Epoch → Prop} {anchorEpoch : Epoch}
    {state after : BeaconState preset fork} {count : Nat}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (counts : ∀ n, n < count → ∀ middle cached justified,
      advanceSlots config checks n state = .ok middle → processSlot middle = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      FinalizationSources link anchorEpoch (getCurrentEpoch cached).toNat cached →
      FinalizationSources link anchorEpoch ((getCurrentEpoch cached).toNat + 1) justified)
    (computed : advanceSlots config checks count state = .ok after) :
    FinalizationSources link anchorEpoch (getCurrentEpoch after).toNat after := by
  induction count generalizing state with
  | zero =>
    have same : state = after := Except.ok.inj computed
    exact same ▸ holds
  | succ count ih =>
    rw [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    apply ih (holds.advanceSlot (fun cached justified =>
      counts 0 (by omega) state cached justified rfl) nextOk) ?_ rest
    intro n bound middle cached justified ran cachedOk justifiedOk old
    apply counts (n + 1) (by omega) middle cached justified ?_ cachedOk justifiedOk old
    simp only [EthLib.Consensus.advanceSlots, nextOk, bind, Except.bind]
    exact ran

/-- A successful slot run carries source evidence using counts at its visited states. -/
theorem FinalizationSources.processSlots {config : Config} {checks : SignatureChecks}
    {link : Checkpoint → Epoch → Prop} {anchorEpoch : Epoch}
    {state after : BeaconState preset fork} {slot : Slot}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (counts : ∀ middle cached justified,
      (middle = state ∨ processSlots config checks state middle.slot = .ok middle) →
      middle.slot < slot → processSlot middle = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      FinalizationSources link anchorEpoch (getCurrentEpoch cached).toNat cached →
      FinalizationSources link anchorEpoch ((getCurrentEpoch cached).toNat + 1) justified)
    (computed : processSlots config checks state slot = .ok after) :
    FinalizationSources link anchorEpoch (getCurrentEpoch after).toNat after := by
  simp only [EthLib.Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, later, run⟩ := computed
  apply holds.advanceSlots ?_ run
  intro n bound middle cached justified ran cachedOk justifiedOk old
  have atSlot := advanceSlots_slot n ran
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  have before : middle.slot < slot := by
    rw [UInt64.lt_iff_toNat_lt]
    omega
  apply counts middle cached justified ?_ before cachedOk justifiedOk old
  by_cases zero : n = 0
  · subst n
    exact .inl (Except.ok.inj ran).symm
  · right
    have afterStart : state.slot < middle.slot := by
      rw [UInt64.lt_iff_toNat_lt]
      omega
    simp only [EthLib.Consensus.processSlots, bind_ok_iff, ensure_ok_iff]
    refine ⟨(), afterStart, ?_⟩
    have distance : middle.slot.toNat - state.slot.toNat = n := by omega
    rw [distance]
    exact ran

/-- A block keeps the historical source evidence and its epoch. -/
theorem FinalizationSources.processBlock {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state)
    (computed : processBlock config checks engine state block = .ok after) :
    FinalizationSources link anchorEpoch (getCurrentEpoch after).toNat after := by
  have frame := frame_processBlock computed
  have epoch : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  rw [epoch]
  exact holds.of_frame frame

/-- Held block states retain source evidence from fixed-check transitions and historical counts. -/
theorem Store.Reachable.blockState_finalizationSources {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    {link : Checkpoint → Epoch → Prop} {anchorEpoch limit : Epoch}
    (anchor : FinalizationSources link anchorEpoch (getCurrentEpoch anchorState).toNat anchorState)
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    (counts : ∀ (root childRoot : Root) (base middle cached justified : BeaconState preset fork)
      (child : BeaconBlock preset fork), store.blockStates[root]? = some base →
      store.blocks[childRoot]? = some child → child.parentRoot = root →
      (middle = base ∨ processSlots config checks base middle.slot = .ok middle) →
      middle.slot < child.slot → getCurrentEpoch middle ≤ limit →
      processSlot middle = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      FinalizationSources link anchorEpoch (getCurrentEpoch cached).toNat cached →
      FinalizationSources link anchorEpoch ((getCurrentEpoch cached).toNat + 1) justified)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state)
    (bounded : getCurrentEpoch state ≤ limit) :
    FinalizationSources link anchorEpoch (getCurrentEpoch state).toNat state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same]
    exact anchor
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      transitions root block state found stored same
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transitioned
    have monotone {left right : BeaconState preset fork} (le : left.slot ≤ right.slot) :
        getCurrentEpoch left ≤ getCurrentEpoch right := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp le)
    have parentBound : getCurrentEpoch parent ≤ limit := by
      apply UInt64.le_trans (monotone ?_) bounded
      obtain ⟨before, sameSlot⟩ := stateTransition_slot transitioned
      rw [sameSlot]
      exact UInt64.le_of_lt before
    have parentHolds :=
      reachable.blockState_finalizationSources anchor transitions counts parentFound parentBound
    apply FinalizationSources.processBlock (computed := blockOk)
    apply parentHolds.processSlots (computed := slotsOk)
    intro middle cached justified visited before cachedOk justifiedOk old
    apply counts block.parentRoot root parent middle cached justified block parentFound found rfl
      visited ?_ ?_ cachedOk justifiedOk old
    · simpa only [message] using before
    · apply UInt64.le_trans (monotone ?_) bounded
      rw [(stateTransition_slot transitioned).2]
      exact UInt64.le_of_lt before
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- Updating checkpoints preserves any property shared by the old and proposed final checkpoint. -/
theorem Store.updateCheckpoints_finalized_property {store : Store preset fork}
    {justified finalized : Checkpoint} {P : Checkpoint → Prop}
    (old : P store.finalizedCheckpoint) (proposed : P finalized) :
    P (store.updateCheckpoints justified finalized).finalizedCheckpoint := by
  unfold Store.updateCheckpoints
  split <;> dsimp only <;> split <;> assumption

/-- A realized checkpoint from a pulled-up tip is counted in an earlier block epoch.

The strict comparison is the guard that separates realized from unrealized finalization. -/
theorem Store.finalized_of_computePulledUpTip {config : Config}
    {store after : Store preset fork} {root : Root}
    (computed : store.computePulledUpTip config root = .ok after) :
    after.finalizedCheckpoint = store.finalizedCheckpoint ∨
      ∃ state pulled block epoch,
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        store.blocks[root]? = some block ∧
        store.getCurrentStoreEpoch config = .ok epoch ∧
        computeEpochAtSlot preset block.slot < epoch ∧
        after.finalizedCheckpoint = pulled.finalizedCheckpoint := by
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, stateOk, pulled, pulledOk, block, blockOk, epoch, epochOk, computed⟩ := computed
  have stateFound := Store.blockState_ok_iff.mp stateOk
  have unchanged : ∀ (s : Store preset fork) justified finalized,
      (s.updateUnrealizedCheckpoints justified finalized).finalizedCheckpoint =
        s.finalizedCheckpoint := by
    intro s justified finalized
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> rfl
  have blockFound : store.blocks[root]? = some block := by
    simpa only [Store.block, Store.updateUnrealizedCheckpoints_blocks] using
      (Store.block_ok_iff.mp blockOk)
  have clock : store.getCurrentStoreEpoch config = .ok epoch := by
    simpa only [Store.getCurrentStoreEpoch, Store.getCurrentSlot,
      Store.updateUnrealizedCheckpoints_timeMs,
      Store.updateUnrealizedCheckpoints_genesisTimeMs] using epochOk
  split at computed
  · rename_i before
    have same : after = _ := (Except.ok.inj computed).symm
    rw [same]
    apply Store.updateCheckpoints_finalized_property (P := fun checkpoint =>
      checkpoint = store.finalizedCheckpoint ∨ ∃ state pulled block epoch,
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        store.blocks[root]? = some block ∧ store.getCurrentStoreEpoch config = .ok epoch ∧
        computeEpochAtSlot preset block.slot < epoch ∧ checkpoint = pulled.finalizedCheckpoint)
    · exact .inl (unchanged _ _ _)
    · exact .inr ⟨state, pulled, block, epoch, stateFound, mapError_ok_iff.mp pulledOk,
        blockFound, clock, before, rfl⟩
  · have same : after = _ := (Except.ok.inj computed).symm
    rw [same]
    exact .inl (unchanged _ _ _)

/-- A per-slot tick realizes a different checkpoint only at a later epoch boundary. -/
theorem Store.finalized_of_onTickPerSlot {config : Config}
    {store after : Store preset fork} {timeMs : UInt64}
    (computed : store.onTickPerSlot config timeMs = .ok after) :
    after.finalizedCheckpoint = store.finalizedCheckpoint ∨
      ∃ previous current,
        store.getCurrentSlot config = .ok previous ∧
        after.getCurrentSlot config = .ok current ∧ previous < current ∧
        computeSlotsSinceEpochStart preset current = .ok 0 ∧
        after.finalizedCheckpoint = store.unrealizedFinalizedCheckpoint := by
  have frame := Store.onTickPerSlot_frame computed
  unfold Store.onTickPerSlot at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨previous, previousOk, current, currentOk, computed⟩ := computed
  have afterSlot : after.getCurrentSlot config = .ok current := by
    simpa only [Store.getCurrentSlot, frame.1, frame.2.1] using currentOk
  split at computed <;>
    obtain ⟨offset, offsetOk, computed⟩ := computed <;>
    split at computed
  all_goals
    have same : after = _ := (Except.ok.inj computed).symm
    rw [show after.finalizedCheckpoint = _ from congrArg Store.finalizedCheckpoint same]
  · apply Store.updateCheckpoints_finalized_property (P := fun checkpoint =>
      checkpoint = store.finalizedCheckpoint ∨ ∃ previous current,
        store.getCurrentSlot config = .ok previous ∧
        after.getCurrentSlot config = .ok current ∧ previous < current ∧
        computeSlotsSinceEpochStart preset current = .ok 0 ∧
        checkpoint = store.unrealizedFinalizedCheckpoint)
    · exact .inl rfl
    · exact .inr ⟨previous, current, previousOk, afterSlot, ‹_ ∧ _›.1,
        by simpa only [‹_ ∧ _›.2] using mapError_ok_iff.mp offsetOk, rfl⟩
  · exact .inl rfl
  · apply Store.updateCheckpoints_finalized_property (P := fun checkpoint =>
      checkpoint = store.finalizedCheckpoint ∨ ∃ previous current,
        store.getCurrentSlot config = .ok previous ∧
        after.getCurrentSlot config = .ok current ∧ previous < current ∧
        computeSlotsSinceEpochStart preset current = .ok 0 ∧
        checkpoint = store.unrealizedFinalizedCheckpoint)
    · exact .inl rfl
    · exact .inr ⟨previous, current, previousOk, afterSlot, ‹_ ∧ _›.1,
        by simpa only [‹_ ∧ _›.2] using mapError_ok_iff.mp offsetOk, rfl⟩
  · exact .inl rfl

/-- A run from a target epoch through the next epoch keeps that target's committees. -/
theorem RunKept.committeesKept_through_next_epoch {state after : BeaconState preset fork}
    (run : RunKept state after)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {epoch : Epoch} (starts : getCurrentEpoch state = epoch)
    (ends : (getCurrentEpoch after).toNat ≤ epoch.toNat + 1) :
    CommitteesKept epoch state after := by
  apply run.committeesKept
  · rw [starts]
    omega
  · rw [← starts]
    exact getCurrentEpoch_le_activityFixedEpoch state
  · omega

/-- A run through the next epoch keeps the indices decoded from a target-epoch attestation. -/
theorem RunKept.attestingIndices_eq_through_next_epoch {state after : BeaconState preset fork}
    (run : RunKept state after)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {attestation : Attestation preset fork}
    (starts : getCurrentEpoch state = computeEpochAtSlot preset attestation.data.slot)
    (ends : (getCurrentEpoch after).toNat ≤ (getCurrentEpoch state).toNat + 1) :
    getAttestingIndices after attestation = getAttestingIndices state attestation := by
  have fixed := getCurrentEpoch_le_activityFixedEpoch state
  have active := run.active.getActiveValidatorIndices_eq fixed
  have checked := run.active.getActiveValidatorIndicesChecked_eq fixed
  have seed : getSeed after (getCurrentEpoch state) DOMAIN_BEACON_ATTESTER =
      getSeed state (getCurrentEpoch state) DOMAIN_BEACON_ATTESTER := by
    refine getSeed_eq_of_mix _ fun shifted reads =>
      run.mixes shifted fun written low high same => ?_
    have lowNat := UInt64.le_iff_toNat_le.mp low
    have highNat := UInt64.le_iff_toNat_le.mp high
    have sameNat := congrArg UInt64.toNat same
    rw [UInt64.toNat_mod, UInt64.toNat_mod] at sameNat
    exact Nat.mod_ne_of_sub_lt (low := written.toNat) (high := shifted.toNat)
      (length := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (by omega) (by omega) sameNat.symm
  unfold getAttestingIndices attesterShuffle getCommitteeCountPerSlot
  rw [← starts]
  simp only [active, checked, seed]

/-- Caching a slot preserves the complete link for either recent epoch.

This is equality of successful reads and failures, including epochs with one slot. -/
private theorem LinkVote.processSlot_iff {state cached : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (computed : processSlot state = .ok cached)
    (recent : Bool) (position : Nat) (vote : ValidatorIndex × AttestationData) :
    LinkVote cached recent position vote ↔ LinkVote state recent position vote := by
  have frame := frame_processSlot computed
  have current : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previous : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [current]
  unfold LinkVote
  rw [current, previous, frame.currentJustified, frame.previousJustified]
  have roots (epoch : vote.2.target.epoch =
      (if recent then getCurrentEpoch state else getPreviousEpoch state)) :
      getBlockRoot cached vote.2.target.epoch = getBlockRoot state vote.2.target.epoch := by
    apply getBlockRoot_processSlot computed
    apply slot_lt_epoch_add_historical positive window
    cases recent
    · exact .inr epoch
    · exact .inl epoch
  constructor <;> rintro ⟨index, epoch, source, target⟩
  · exact ⟨index, epoch, source, (roots epoch) ▸ target⟩
  · exact ⟨index, epoch, source, (roots epoch).symm ▸ target⟩

/-- Caching preserves the balances and voter sets used by the justification count. -/
theorem processSlot_countingBalances {state cached : BeaconState preset fork}
    (computed : processSlot state = .ok cached) :
    getCurrentEpoch cached = getCurrentEpoch state ∧
    getPreviousEpoch cached = getPreviousEpoch state ∧
    getTotalActiveBalance cached = getTotalActiveBalance state ∧
    (∀ indices, getTotalBalance cached indices = getTotalBalance state indices) ∧
    activeVoters cached = activeVoters state ∧ quorumVoters cached = quorumVoters state ∧
    (∀ index, balanceAt cached index = balanceAt state index) := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩

/-- Caching preserves the participating indices, including errors. -/
theorem processSlot_participatingIndices {state cached : BeaconState preset fork}
    (computed : processSlot state = .ok cached) (altair : .altair ≤ fork)
    (flag : UInt64) (epoch : Epoch) :
    getUnslashedParticipatingIndices cached altair flag epoch =
      getUnslashedParticipatingIndices state altair flag epoch := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  rfl

/-- Caching preserves the pending target attestations for either recent epoch. -/
theorem processSlot_matchingTargetAttestations {state cached : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (computed : processSlot state = .ok cached) (before : fork < .altair)
    {epoch : Epoch} (recent : epoch = getCurrentEpoch state ∨ epoch = getPreviousEpoch state) :
    getMatchingTargetAttestations cached before epoch =
      getMatchingTargetAttestations state before epoch := by
  have roots := getBlockRoot_processSlot computed
    (slot_lt_epoch_add_historical positive window recent)
  have source : getMatchingSourceAttestations cached before epoch =
      getMatchingSourceAttestations state before epoch := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
    rfl
  unfold getMatchingTargetAttestations
  rw [source, roots]

/-- Caching preserves the unslashed indices of any array of pending attestations. -/
theorem processSlot_unslashedAttestingIndices {state cached : BeaconState preset fork}
    (computed : processSlot state = .ok cached)
    (attestations : Array (PendingAttestation preset)) :
    getUnslashedAttestingIndices cached attestations =
      getUnslashedAttestingIndices state attestations := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  rfl

/-- A cached finalization step retains count evidence from the uncached visited state. -/
theorem FinalizationSources.process_cached {link : Checkpoint → Epoch → Prop}
    {anchorEpoch : Epoch} {state cached after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (cachedOk : processSlot state = .ok cached)
    (holds : FinalizationSources link anchorEpoch (getCurrentEpoch cached).toNat cached)
    (ordered : CheckpointsOrdered cached) (settled : JustifiedSettled cached)
    (counts : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ (recent : Bool) (indices : List ValidatorIndex) (total balance threshold weight : Gwei),
      ((∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations = .ok indices) →
      getTotalActiveBalance state = .ok total → getTotalBalance state indices = .ok balance →
      mulChecked total 2 = .ok threshold → mulChecked balance 3 = .ok weight →
      threshold ≤ weight →
      anchorEpoch < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
      link (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint)
        (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (computed : processJustificationAndFinalization cached = .ok after) :
    FinalizationSources link anchorEpoch ((getCurrentEpoch cached).toNat + 1) after := by
  obtain ⟨current, previous, total, balance, -, -, -⟩ := processSlot_countingBalances cachedOk
  have frame := frame_processSlot cachedOk
  apply holds.process_of_counts ordered settled ?_ computed
  intro late recent indices totalValue balanceValue threshold weight counted totalOk balanceOk
    thresholdOk weightOk passed above
  rw [current] at late
  rw [total] at totalOk
  rw [balance] at balanceOk
  rw [frame.currentJustified, frame.previousJustified] at above ⊢
  rw [current, previous]
  apply counts late recent indices totalValue balanceValue threshold weight ?_
    totalOk balanceOk thresholdOk weightOk passed above
  rcases counted with ⟨altair, indicesOk⟩ | ⟨before, attestations, matching, indicesOk⟩
  · left
    refine ⟨altair, ?_⟩
    rw [current, previous, processSlot_participatingIndices cachedOk] at indicesOk
    exact indicesOk
  · right
    refine ⟨before, attestations, ?_, ?_⟩
    · rw [current, previous] at matching
      rw [processSlot_matchingTargetAttestations positive window cachedOk before
        (by cases recent <;> simp)] at matching
      exact matching
    · rwa [processSlot_unslashedAttestingIndices cachedOk] at indicesOk

/-- Pulling up a tip adds only the finalization of its successful justification computation. -/
theorem Store.finalized_properties_of_computePulledUpTip {config : Config}
    {store after : Store preset fork} {root : Root} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (counted : ∀ (state pulled : BeaconState preset fork),
      store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.finalizedCheckpoint)
    (computed : store.computePulledUpTip config root = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  have update : ∀ (s : Store preset fork) justified finalized,
      P s.finalizedCheckpoint → P s.unrealizedFinalizedCheckpoint → P finalized →
      P (s.updateCheckpoints justified finalized).finalizedCheckpoint ∧
        P (s.updateCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
  have updateUnrealized : ∀ (s : Store preset fork) justified finalized,
      P s.finalizedCheckpoint → P s.unrealizedFinalizedCheckpoint → P finalized →
      P (s.updateUnrealizedCheckpoints justified finalized).finalizedCheckpoint ∧
        P (s.updateUnrealizedCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨old, by assumption⟩
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, -, epoch, -, computed⟩ := computed
  have new := counted state pulled (Store.blockState_ok_iff.mp found)
    (mapError_ok_iff.mp processed)
  have preserved := updateUnrealized
    { store with unrealizedJustifications :=
      store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint }
    pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint realized unrealized new
  split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
    subst after
  · exact update _ _ _ preserved.1 preserved.2 new
  · exact preserved

/-- An accepted block adds only its post-state or its pulled-up finalization to the fields. -/
private theorem Store.finalized_properties_of_onBlock {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {store after : Store preset fork} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (states : ∀ (root : Root) (state : BeaconState preset fork),
      after.blockStates[root]? = some state → P state.finalizedCheckpoint)
    (counts : ∀ (root : Root) (state pulled : BeaconState preset fork),
      after.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.finalizedCheckpoint)
    (added : store.onBlock config checks sources signed = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact ⟨realized, unrealized⟩
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedFields : P recorded.finalizedCheckpoint ∧
        P recorded.unrealizedFinalizedCheckpoint := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ⟨realized, unrealized⟩
      · cases record
        exact ⟨realized, unrealized⟩
    have boostedFields : P boosted.finalizedCheckpoint ∧
        P boosted.unrealizedFinalizedCheckpoint := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedFields
    have kept := (Store.computePulledUpTip_frame added).2.2.1
    have newFound : after.blockStates[blockRoot]? = some state := by
      rw [kept, Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
      simp
    have new := states blockRoot state newFound
    have updated :
        P (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).finalizedCheckpoint ∧
        P (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).unrealizedFinalizedCheckpoint := by
      obtain ⟨old, pending⟩ := boostedFields
      unfold Store.updateCheckpoints
      split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
    exact Store.finalized_properties_of_computePulledUpTip P updated.1 updated.2
      (fun s p found processed => counts blockRoot s p (kept.symm ▸ found) processed) added

/-- A tick preserves a property shared by the realized and unrealized finalized checkpoints. -/
theorem Store.finalized_properties_of_onTickPerSlot {config : Config}
    {store after : Store preset fork} {time : UInt64} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (ticked : store.onTickPerSlot config time = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  have update : ∀ (s : Store preset fork) justified finalized,
      P s.finalizedCheckpoint → P s.unrealizedFinalizedCheckpoint → P finalized →
      P (s.updateCheckpoints justified finalized).finalizedCheckpoint ∧
        P (s.updateCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
  unfold Store.onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    obtain ⟨offset, -, ticked⟩ := ticked <;>
    split at ticked <;>
    simp only [pure, Except.pure, Except.ok.injEq] at ticked <;> subst after
  · exact update _ _ _ realized unrealized unrealized
  · exact ⟨realized, unrealized⟩
  · exact update _ _ _ realized unrealized unrealized
  · exact ⟨realized, unrealized⟩

/-- Catch-up preserves a property of both finalized checkpoint fields through every tick. -/
theorem Store.finalized_properties_of_catchUp {config : Config}
    {store after : Store preset fork} {slot : Slot} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (caught : Store.catchUp config store slot = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  induction store using Store.catchUp.induct config slot with
  | _ store ih =>
    rw [Store.catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTime, -, ticked, tick, caught⟩ := caught
      split at caught
      · obtain ⟨realized, unrealized⟩ :=
          Store.finalized_properties_of_onTickPerSlot P realized unrealized tick
        exact ih ticked ‹_› realized unrealized caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst after
      exact ⟨realized, unrealized⟩

/-- A full tick retains original checkpoint provenance, including catch-up realization. -/
theorem Store.finalized_properties_of_onTick {config : Config}
    {store after : Store preset fork} {time : UInt64} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (ticked : store.onTick config time = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, -, caught, catchUp, ticked⟩ := ticked
  obtain ⟨realized, unrealized⟩ :=
    Store.finalized_properties_of_catchUp P realized unrealized catchUp
  exact Store.finalized_properties_of_onTickPerSlot P realized unrealized ticked

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- Successful attestation handling supplies its checked indexed-attestation witness. -/
theorem readsAttestation_of_onAttestation {store after : Store preset fork}
    {attestation : Attestation preset fork} {fromBlock : Bool}
    (handled : store.onAttestation config checks attestation fromBlock = .ok after) :
    ∃ indexed, ReadsAttestation config checks store attestation indexed := by
  unfold Store.onAttestation at handled
  simp only [bind_ok_iff] at handled
  obtain ⟨_, _, stored, storing, target, targetOk, _, _, indexed, indexedOk,
    valid, validOk, handled⟩ := handled
  split at handled
  · rename_i validTrue
    exact ⟨indexed, stored, target, storing, targetOk, mapError_ok_iff.mp indexedOk,
      by simpa [validTrue] using mapError_ok_iff.mp validOk⟩
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at handled

/-- Every attestation in an accepted block was read in a reachable intermediate store. -/
private theorem exists_readsAttestation_of_onBlockWithVotes {store after : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {signed : SignedBeaconBlock preset fork}
    (handled : store.onBlockWithVotes config checks sources signed = .ok after)
    {attestation : Attestation preset fork}
    (member : attestation ∈ signed.message.body.attestations.data) :
    ∃ intermediate indexed, Store.Reachable config anchorState anchorBlock intermediate ∧
      ReadsAttestation config checks intermediate attestation indexed := by
  unfold Store.onBlockWithVotes at handled
  simp only [bind_ok_iff, ← Array.foldlM_toList] at handled
  obtain ⟨blocked, blockOk, voted, votedOk, -⟩ := handled
  have each : ∀ (xs : List (Attestation preset fork)) (first last : Store preset fork),
      Store.Reachable config anchorState anchorBlock first →
      xs.foldlM (fun s a => s.onAttestation config checks a true) first = .ok last →
      ∀ a ∈ xs, ∃ intermediate indexed,
        Store.Reachable config anchorState anchorBlock intermediate ∧
          ReadsAttestation config checks intermediate a indexed := by
    intro xs
    induction xs with
    | nil => simp
    | cons a rest ih =>
      intro first last reached folded item member
      rw [List.foldlM_cons, bind_ok_iff] at folded
      obtain ⟨middle, firstOk, restOk⟩ := folded
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨indexed, reads⟩ := readsAttestation_of_onAttestation firstOk
        exact ⟨first, indexed, reached, reads⟩
      · exact ih middle last (reached.attestation firstOk) restOk item member
  exact each _ blocked voted (reachable.block blockOk) votedOk attestation
    (Array.mem_toList_iff.mpr member)

/-- The finalized checkpoint of an honest store is on the chain of each later justified one.

The justified checkpoint is one of an honest store, at the epoch of the finalized one or later.

Its epoch is at most the horizon, which bounds the epochs that the two chains can differ over.

That store finds the finalized block on the chain of the justified block, at the finalized epoch.

Both stores are at events up to the last time `last`. -/
def FinalizedPrefix
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (horizon : Epoch) (last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ w ∈ J, ∀ n k, (e.world n).time ≤ last → (e.world k).time ≤ last →
    ∀ checkpoint, ((e.world k).state w).Justified checkpoint →
    ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
    checkpoint.epoch ≤ horizon →
    ((e.world k).state w).getCheckpointBlock checkpoint.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root

/-- Two justified checkpoints of honest stores at one epoch, up to a horizon, are the same.

Both stores are at events up to the last time `last`. -/
def OneJustifiedPerEpoch
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (horizon : Epoch) (last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ w ∈ J, ∀ n k, (e.world n).time ≤ last → (e.world k).time ≤ last →
    ∀ first second, ((e.world n).state u).Justified first →
    ((e.world k).state w).Justified second → first.epoch = second.epoch →
    first.epoch ≤ horizon → first = second

/-- A validator signs a vote with a target, in a message sent by the time `last`. -/
def SignsTarget
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) (last : ℕ) : Prop :=
  ∃ k, (e.world k).time ≤ last ∧ ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target

/-- A validator signs a vote with a target, of a slot before a given one, sent by `last`. -/
def SignsTargetBefore
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) (slot : Slot) (last : ℕ) :
    Prop :=
  ∃ k, (e.world k).time ≤ last ∧ ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target ∧
      data.slot < slot

/-- A vote of a slot before a given one is a vote. -/
theorem SignsTargetBefore.signsTarget
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} {v : ValidatorIndex} {target : Checkpoint} {slot : Slot} {last : ℕ}
    (signs : SignsTargetBefore e v target slot last) : SignsTarget e v target last :=
  let ⟨k, bounded, m, sent, data, member, same, _⟩ := signs
  ⟨k, bounded, m, sent, data, member, same⟩

/-- Each justified checkpoint of an honest store after the anchor has an honest vote.

The checkpoint is at a later epoch than the given one, the epoch of the anchor.

Its epoch is at most the horizon.

An honest validator signs a vote with the checkpoint as its target.

The vote is of a slot before the current slot of the store.

The store is at an event up to the last time `last`, and the vote is sent by its time. -/
def JustifiedByHonestVote
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (anchorEpoch horizon : Epoch) (last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n, (e.world n).time ≤ last → ∀ checkpoint slot,
    ((e.world n).state u).Justified checkpoint →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    anchorEpoch < checkpoint.epoch → checkpoint.epoch ≤ horizon →
    ∃ v ∈ J, SignsTargetBefore e v checkpoint slot (e.world n).time

/-- An honest third of the stake signs each justified checkpoint of the epoch of its count.

The stake is read in the pulled-up state of a block of an honest store, as the rule reads it.

The voters are honest and active in that state.

Three times their stake exceeds its active balance by more than the margin.

The margin covers the change of balances between that state and a state that counts votes.

The votes are for a checkpoint of the current epoch of the store.

Take such a checkpoint that an honest store counts as justified.

It is the target of a vote that one of the voters signs.

The vote is of a slot before the current slot of the store that counts the checkpoint.

The epoch is after the given one, the epoch of the anchor.

No voter has to sign a target here: the definition only counts stake.

Both stores are at events up to the last time `last`.

The vote is sent by the time of the store with the justified checkpoint. -/
def HonestThirdPins
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (anchorEpoch horizon : Epoch) (margin last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n, (e.world n).time ≤ last → ∀ head state total epoch,
    ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    epoch ≤ horizon →
    (∀ v ∈ voters, v ∈ J) → (∀ v ∈ voters, v ∈ activeVoters state) →
    total.toNat + margin < 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k, (e.world k).time ≤ last → ∀ checkpoint slot,
      ((e.world k).state w).Justified checkpoint →
      ((e.world k).state w).getCurrentSlot config = .ok slot →
      checkpoint.epoch = epoch → anchorEpoch < epoch →
      ∃ v ∈ voters, SignsTargetBefore e v checkpoint slot (e.world k).time

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- A finalized prefix up to a time is one up to every earlier time. -/
theorem FinalizedPrefix.of_le {horizon : Epoch} {last later : ℕ}
    (chain : FinalizedPrefix e horizon later) (le : last ≤ later) :
    FinalizedPrefix e horizon last :=
  fun u caller w receiver n k nBound kBound =>
    chain u caller w receiver n k (nBound.trans le) (kBound.trans le)

/-- One justified checkpoint per epoch up to a time holds up to every earlier time. -/
theorem OneJustifiedPerEpoch.of_le {horizon : Epoch} {last later : ℕ}
    (unique : OneJustifiedPerEpoch e horizon later) (le : last ≤ later) :
    OneJustifiedPerEpoch e horizon last :=
  fun u caller w receiver n k nBound kBound =>
    unique u caller w receiver n k (nBound.trans le) (kBound.trans le)

/-- Honest votes for justified checkpoints up to a time are honest votes up to every earlier time.

The vote is sent by the time of the store, so its bound does not depend on the last time. -/
theorem JustifiedByHonestVote.of_le {anchorEpoch horizon : Epoch} {last later : ℕ}
    (voted : JustifiedByHonestVote e anchorEpoch horizon later) (le : last ≤ later) :
    JustifiedByHonestVote e anchorEpoch horizon last :=
  fun u honest n bounded => voted u honest n (bounded.trans le)

/-- Honest pins up to a time are honest pins up to every earlier time. -/
theorem HonestThirdPins.of_le {anchorEpoch horizon : Epoch} {margin last later : ℕ}
    (pins : HonestThirdPins e anchorEpoch horizon margin later) (le : last ≤ later) :
    HonestThirdPins e anchorEpoch horizon margin last :=
  fun u caller n nBound head state total epoch voters stateOk totalOk epochOk inHorizon honest
    active large w receiver k kBound =>
    pins u caller n (nBound.trans le) head state total epoch voters stateOk totalOk epochOk
      inHorizon honest active large w receiver k (kBound.trans le)

/-- Every realized finalized boundary stays at or above an epoch-aligned anchor. -/
theorem Execution.anchorSlot_le_finalized_boundary {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {w : ValidatorIndex} (start : e.start w = anchor) {k : ℕ} {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset
      ((e.world k).state w).finalizedCheckpoint.epoch = .ok boundary) :
    anchorBlock.slot ≤ boundary := by
  obtain ⟨_, _, _, _, _, finalized, _, _⟩ := getForkchoiceStore_anchor anchored
  have epochs := (e.epochsLe_of_le w (Nat.zero_le k)).2
  simp only [Execution.world_zero, World.initial, start, finalized] at epochs
  have epochLe := epochs.epoch_le
  have rounded : anchorState.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH =
      anchorState.slot := by
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at anchorBoundary
    rw [anchorSlot, computeStartSlotAtEpoch_computeEpochAtSlot] at anchorBoundary
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, decide_eq_true_eq] at anchorBoundary
    have h := (computeStartSlotAtEpoch_ok_iff.mp
      (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot)).2
    have le : (anchorState.slot / preset.SLOTS_PER_EPOCH *
        preset.SLOTS_PER_EPOCH).toNat ≤ anchorState.slot.toNat := by
      rw [h, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_mul_le_self _ _
    have zero := congrArg UInt64.toNat anchorBoundary
    simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
    have upper := anchorState.slot.toNat_lt
    have lower := (anchorState.slot / preset.SLOTS_PER_EPOCH *
      preset.SLOTS_PER_EPOCH).toNat_lt
    apply UInt64.toNat_inj.mp
    omega
  have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
    (UInt64.le_iff_toNat_le.mp epochLe)
  have anchorValue := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot)).2
  rw [rounded] at anchorValue
  rw [anchorSlot, UInt64.le_iff_toNat_le,
    (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2, anchorValue]
  exact mono

/-- Computing a checkpoint state retains the checks used for its empty slots. -/
theorem checkpointState_run_of_compute {store : Store preset fork} {target : Checkpoint}
    {state : BeaconState preset fork}
    (computed : store.computeCheckpointState config checks target = .ok state) :
    ∃ base slot, store.blockStates[target.root]? = some base ∧
      computeStartSlotAtEpoch preset target.epoch = .ok slot ∧
      lookaheadState config checks base slot = .ok state := by
  unfold Store.computeCheckpointState at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨base, found, slot, slotOk, computed⟩ := computed
  exact ⟨base, slot, Store.blockState_ok_iff.mp found, mapError_ok_iff.mp slotOk, computed⟩

/-- An honest store's cached checkpoint states use the execution's signature checks.

Reachability alone permits different checks at each step, so this follows the execution. -/
theorem Execution.checkpointStates_fixedChecks {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (start : e.start w = anchor) {k : ℕ}
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (found : ((e.world k).state w).checkpointStates[checkpoint]? = some state) :
    ∃ base slot, ((e.world k).state w).blockStates[checkpoint.root]? = some base ∧
      computeStartSlotAtEpoch preset checkpoint.epoch = .ok slot ∧
      lookaheadState config checks base slot = .ok state := by
  let Origin := fun (store : Store preset fork) =>
    ∀ (checkpoint : Checkpoint) (state : BeaconState preset fork),
      store.checkpointStates[checkpoint]? = some state →
      ∃ base slot, store.blockStates[checkpoint.root]? = some base ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok slot ∧
        lookaheadState config checks base slot = .ok state
  have maps : ∀ {store after : Store preset fork}, Origin store →
      after.blockStates = store.blockStates → after.checkpointStates = store.checkpointStates →
      Origin after := by
    intro store after holds blocks cached checkpoint state found
    rw [cached] at found
    rw [blocks]
    exact holds checkpoint state found
  have attestationStep : ∀ {store after : Store preset fork}
      {a : Attestation preset fork} {fromBlock : Bool}, Origin store →
      store.onAttestation config checks a fromBlock = .ok after → Origin after := by
    intro store after a fromBlock holds handled
    unfold Store.onAttestation at handled
    simp only [bind_ok_iff] at handled
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, handled⟩ := handled
    have storedOrigin : Origin stored := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · simp only [pure, Except.pure, Except.ok.injEq] at storing
        exact storing ▸ holds
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
        obtain ⟨computedState, computed, rfl⟩ := storing
        intro checkpoint state found
        simp only [Std.TreeMap.getElem?_insert] at found
        split at found
        · rename_i same
          have eq : a.data.target = checkpoint := by
            unfold Checkpoint.compare at same
            rw [Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq,
              Std.LawfulEqCmp.compare_eq_iff_eq] at same
            obtain ⟨epoch, root⟩ := checkpoint
            dsimp only at same
            rw [← same.1, ← same.2]
          cases found
          subst checkpoint
          exact checkpointState_run_of_compute computed
        · exact holds checkpoint state found
    split at handled
    · simp only [pure, Except.pure, Except.ok.injEq] at handled
      subst after
      exact storedOrigin
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at handled
  have blockStep : ∀ {store after : Store preset fork} {signed : SignedBeaconBlock preset fork},
      Store.Reachable config anchorState anchorBlock store → Origin store →
      store.onBlock config checks sources signed = .ok after → Origin after := by
    intro store after signed reachable holds handled
    rcases Store.onBlock_same_or_insert handled with
      same | ⟨root, -, fresh, -, -, state, -, -, states⟩
    · exact same ▸ holds
    intro checkpoint state found
    rw [(Store.onBlock_checkpointStates_latestMessages handled).1] at found
    obtain ⟨base, slot, baseFound, rest⟩ := holds checkpoint state found
    refine ⟨base, slot, ?_, rest⟩
    have other : root ≠ checkpoint.root := by
      rintro rfl
      rw [reachable.blockState_eq_none fresh] at baseFound
      cases baseFound
    rw [states, getElem?_insert_root]
    simpa only [other, ↓reduceIte] using baseFound
  have foldStep : ∀ {α : Type} (xs : List α) (f : Store preset fork → α →
      Except ForkChoiceError (Store preset fork)) (P : Store preset fork → Prop),
      (∀ a ∈ xs, ∀ s s', P s → f s a = .ok s' → P s') →
      ∀ s s', P s → xs.foldlM f s = .ok s' → P s' := by
    intro α xs f P
    induction xs with
    | nil =>
      intro _ s s' holds step
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at step
      exact step ▸ holds
    | cons a rest ih =>
      intro keeps s s' holds step
      rw [List.foldlM_cons, bind_ok_iff] at step
      obtain ⟨mid, first, restOk⟩ := step
      exact ih (fun a mem => keeps a (List.mem_cons_of_mem _ mem)) mid s'
        (keeps a List.mem_cons_self s mid holds first) restOk
  have invariant : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) ∧
      Origin ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w) ∧ Origin (e.start w)
      rw [start]
      refine ⟨.anchor anchored, ?_⟩
      obtain ⟨root, rootOk, states⟩ := getForkchoiceStore_checkpointStates anchored
      obtain ⟨_, rootOk', -, blocks⟩ := getForkchoiceStore_maps anchored
      rw [rootOk, Except.ok.injEq] at rootOk'
      subst rootOk'
      intro checkpoint state found
      rw [states, Std.TreeMap.getElem?_insert] at found
      split at found
      · rename_i same
        have eq : (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint) = checkpoint := by
          unfold Checkpoint.compare at same
          rw [Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq,
            Std.LawfulEqCmp.compare_eq_iff_eq] at same
          cases checkpoint
          cases same.1
          cases same.2
          rfl
        cases found
        subst checkpoint
        have slotOk :=
          computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot
        refine ⟨anchorState, _, by simp [blocks], slotOk, ?_⟩
        obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp slotOk
        have low : anchorState.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH ≤
            anchorState.slot := by
          rw [UInt64.le_iff_toNat_le, value, computeEpochAtSlot, UInt64.toNat_div]
          exact Nat.div_mul_le_self _ _
        simp [lookaheadState, UInt64.not_lt.mpr low, pure, Except.pure]
      · simp at found
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, handles⟩
      · exact same ▸ ih
      refine ⟨handles.reachable ih.1, ?_⟩
      cases handles with
      | tick _ _ handled =>
        exact maps ih.2 (Store.onTick_frame handled).2.2.2
          (Store.onTick_checkpointStates_latestMessages handled).1
      | attestation _ handled => exact attestationStep ih.2 handled
      | attesterSlashing _ handled =>
        exact maps ih.2 (Store.onAttesterSlashing_frame handled).2.2.1
          (Store.onAttesterSlashing_checkpointStates_latestMessages handled).1
      | block _ handled =>
        unfold Store.onBlockWithVotes at handled
        simp only [bind_ok_iff, ← Array.foldlM_toList] at handled
        obtain ⟨blocked, blockOk, voted, votedOk, slashedOk⟩ := handled
        have votedOrigin := foldStep _ _ Origin (fun _ _ _ _ holds step =>
          attestationStep holds step) blocked voted (blockStep ih.1 ih.2 blockOk) votedOk
        exact foldStep _ _ Origin (fun _ _ _ _ holds step =>
          maps holds (Store.onAttesterSlashing_frame step).2.2.1
            (Store.onAttesterSlashing_checkpointStates_latestMessages step).1)
          voted _ votedOrigin slashedOk
      | payloadAttestation _ handled =>
        obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes handled
        exact same ▸ ih.2
      | envelope _ handled =>
        obtain ⟨_, _, _, _, _, record, same⟩ := Store.onExecutionPayloadEnvelope_ok handled
        rw [same]
        obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
        exact ih.2
      | inclusionList _ handled =>
        obtain ⟨_, _, same⟩ := Store.onInclusionList_ok ‹_› handled
        exact same ▸ ih.2
  exact (invariant k).2 checkpoint state found

/-- Each non-anchor block in an honest store has a transition with the execution's checks. -/
theorem Execution.exists_transition_of_nonanchor_block {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : ((e.world k).state w).blocks[root]? = some block)
    (stored : ((e.world k).state w).blockStates[root]? = some state)
    (other : block ≠ anchorBlock) :
    ∃ parent signed, signed.message = block ∧
      ((e.world k).state w).blockStates[block.parentRoot]? = some parent ∧
      stateTransition config checks sources.engine parent signed true = .ok state := by
  rcases e.exists_signed_of_blocks honest found with old |
    ⟨signed, parent, post, -, message, -, parentFound, transitioned, postFound⟩
  · obtain ⟨anchorRoot, -, blocks, -⟩ := getForkchoiceStore_maps anchored
    rw [start, blocks, getElem?_insert_root] at old
    split at old
    · exact (other (Option.some.inj old.1).symm).elim
    · simp at old
  · rw [stored, Option.some.injEq] at postFound
    subst post
    exact ⟨parent, signed, message, parentFound, transitioned⟩

/-- A pre-block target root reconstructs a checkpoint state with the same target committees.

Every historical transition uses the execution's checks, including empty-slot processing. -/
theorem Execution.exists_checkpointState_of_preBlock_target {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {parent advanced state : BeaconState preset fork} {block : BeaconBlock preset fork}
    {epoch : Epoch} {query : Slot} {root : Root}
    (parentFound : ((e.world k).state w).blockStates[block.parentRoot]? = some parent)
    (slotsOk : processSlots config checks parent block.slot = .ok advanced)
    (blockOk : processBlock config checks sources.engine advanced block = .ok state)
    (epochStart : computeStartSlotAtEpoch preset epoch = .ok query)
    (read : getBlockRootAtSlot advanced query = .ok root)
    (later : anchorState.slot ≤ query)
    (recent : (getCurrentEpoch advanced).toNat ≤ epoch.toNat + 1) :
    ∃ ancestor ancestorState checkpointState,
      ((e.world k).state w).blocks[root]? = some ancestor ∧
      ((e.world k).state w).blockStates[root]? = some ancestorState ∧
      lookaheadState config checks ancestorState query = .ok checkpointState ∧
      checkpointState.slot = query ∧ RunKept checkpointState advanced ∧
      CommitteesKept epoch checkpointState advanced := by
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  obtain ⟨ancestor, ancestorState, checkpointState, held, stored, made, atSlot, run⟩ :=
    (reachable k).preBlock_history_run
      (fun _ _ _ found stored other =>
        e.exists_transition_of_nonanchor_block anchored honest start found stored other)
      nonzero parentFound slotsOk blockOk read later
  refine ⟨ancestor, ancestorState, checkpointState, held, stored, made, atSlot, run,
    run.committeesKept_through_next_epoch ring ?_ recent⟩
  unfold getCurrentEpoch
  rw [atSlot]
  exact computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive) epochStart

private theorem blockVote_attestation_read {store after : Store preset fork}
    {a : Attestation preset fork} {fromBlock : Bool}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (handled : store.onAttestation config checks a fromBlock = .ok after) :
    ∃ targetState indexed,
      after.checkpointStates[a.data.target]? = some targetState ∧
      getIndexedAttestation targetState a = .ok indexed ∧
      (∀ v ∈ indexed.attestingIndices.data,
        (v, a.data) ∈ attestationStatements (config := config) (checks := checks)
          anchorState anchorBlock a) ∧
      ∃ slot, after.getCurrentSlot config = .ok slot ∧ a.data.slot < slot := by
  have clock := (Store.onAttestation_sameClock handled).getCurrentSlot (config := config)
  unfold Store.onAttestation at handled
  simp only [bind_ok_iff] at handled
  obtain ⟨_, validated, stored, storing, targetState, targetOk, _, _, indexed, indexedOk,
    valid, validOk, handled⟩ := handled
  split at handled
  · rename_i validTrue
    simp only [pure, Except.pure, Except.ok.injEq] at handled
    subst after
    have read := mapError_ok_iff.mp indexedOk
    obtain ⟨indices, indicesOk, -⟩ := getAttestingIndices_of_getIndexedAttestation read
    obtain ⟨same, sameOk, _, data, -⟩ :=
      getIndexedAttestation_of_getAttestingIndices indicesOk
    rw [read, Except.ok.injEq] at sameOk
    subst same
    refine ⟨targetState, indexed, Store.checkpointState_ok_iff.mp targetOk, read, ?_, ?_⟩
    · intro v member
      exact ⟨store, indexed, reachable,
        ⟨stored, targetState, storing, targetOk, read,
          by simpa [validTrue] using mapError_ok_iff.mp validOk⟩,
        member, data.symm⟩
    · rw [clock]
      exact (Store.validateOnAttestation_ok validated).2.2.2
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at handled

theorem blockVote_read_of_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (start : e.start w = anchor) {k : ℕ}
    {root : Root} {block : BeaconBlock preset fork}
    (held : ((e.world k).state w).blocks[root]? = some block)
    (other : block ≠ anchorBlock) {a : Attestation preset fork}
    (member : a ∈ block.body.attestations.data) :
    ∃ targetState indexed,
      ((e.world k).state w).checkpointStates[a.data.target]? = some targetState ∧
      getIndexedAttestation targetState a = .ok indexed ∧
      (∀ v ∈ indexed.attestingIndices.data,
        ∃ m ∈ (e.world k).sent,
          (v, a.data) ∈ statements config checks anchorState anchorBlock m) ∧
      ∃ slot, ((e.world k).state w).getCurrentSlot config = .ok slot ∧ a.data.slot < slot := by
  have cacheKept {store after : Store preset fork} {a : Attestation preset fork}
      {fromBlock : Bool} {checkpoint : Checkpoint} {state : BeaconState preset fork}
      (handled : store.onAttestation config checks a fromBlock = .ok after)
      (found : store.checkpointStates[checkpoint]? = some state) :
      after.checkpointStates[checkpoint]? = some state := by
    unfold Store.onAttestation at handled
    simp only [bind_ok_iff] at handled
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, handled⟩ := handled
    split at handled
    · simp only [pure, Except.pure, Except.ok.injEq] at handled
      subst after
      change stored.checkpointStates[checkpoint]? = some state
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · simp only [pure, Except.pure, Except.ok.injEq] at storing
        exact storing ▸ found
      · rename_i absent
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
        obtain ⟨_, _, rfl⟩ := storing
        rw [Std.TreeMap.getElem?_insert]
        split
        · rename_i same
          exact absurd (Std.TreeMap.contains_iff_mem.mpr
            (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
              rw [Std.TreeMap.getElem?_congr same, found]
              rfl))) absent
        · exact found
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at handled
  let P := fun (sent : Set (Message preset fork)) (s : Store preset fork) =>
    ∀ (r : Root) (b : BeaconBlock preset fork), s.blocks[r]? = some b → b ≠ anchorBlock →
      ∀ a ∈ b.body.attestations.data, ∃ targetState indexed,
        s.checkpointStates[a.data.target]? = some targetState ∧
        getIndexedAttestation targetState a = .ok indexed ∧
        (∀ v ∈ indexed.attestingIndices.data,
          ∃ m ∈ sent, (v, a.data) ∈ statements config checks anchorState anchorBlock m) ∧
        ∃ slot, s.getCurrentSlot config = .ok slot ∧ a.data.slot < slot
  have keep {sent sent' : Set (Message preset fork)} {s t : Store preset fork}
      (old : P sent s) (incl : sent ⊆ sent')
      (blocks : t.blocks = s.blocks)
      (cached : ∀ (c : Checkpoint) (st : BeaconState preset fork),
        s.checkpointStates[c]? = some st → t.checkpointStates[c]? = some st)
      (clock : ∀ slot, s.getCurrentSlot config = .ok slot →
        ∃ later, t.getCurrentSlot config = .ok later ∧ slot ≤ later) : P sent' t := by
    intro r b found other a member
    obtain ⟨st, indexed, found, read, signed, slot, slotOk, past⟩ :=
      old r b (blocks ▸ found) other a member
    obtain ⟨later, laterOk, le⟩ := clock slot slotOk
    exact ⟨st, indexed, cached _ _ found, read,
      fun v mem => let ⟨m, sent, vote⟩ := signed v mem; ⟨m, incl sent, vote⟩,
      later, laterOk, UInt64.lt_of_lt_of_le past le⟩
  have invariant : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) ∧
      P (e.world n).sent ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w) ∧
        P (e.world 0).sent (e.start w)
      rw [start]
      refine ⟨.anchor anchored, ?_⟩
      intro r b found other
      obtain ⟨_, _, blocks, -⟩ := getForkchoiceStore_maps anchored
      rw [blocks, getElem?_insert_root] at found
      split at found
      · exact (other (Option.some.inj found).symm).elim
      · simp at found
    | succ n ih =>
      have incl := e.monotone_sent (Nat.le_succ n)
      rcases e.state_succ n w with same | ⟨_, handles⟩
      · rw [same]
        exact ⟨ih.1, keep ih.2 incl rfl (fun _ _ h => h)
          (fun slot ok => ⟨slot, ok, UInt64.le_refl _⟩)⟩
      refine ⟨handles.reachable ih.1, ?_⟩
      have forward := handles.clock_bounds
      cases handles with
      | tick _ fits handled =>
        exact keep ih.2 incl (Store.onTick_frame handled).2.2.1
          (fun _ _ h => (Store.onTick_checkpointStates_latestMessages handled).1 ▸ h)
          (fun slot ok => Store.exists_getCurrentSlot_onTick_ge
            (by rw [(Store.onTick_frame handled).1] at forward; exact forward.2.1) handled ok)
      | attestation _ handled =>
        exact keep ih.2 incl (Store.onAttestation_frame handled).2.1
          (fun _ _ h => cacheKept handled h)
          (fun slot ok => ⟨slot, (Store.onAttestation_sameClock handled).getCurrentSlot ▸ ok,
            UInt64.le_refl _⟩)
      | attesterSlashing _ handled =>
        exact keep ih.2 incl (Store.onAttesterSlashing_frame handled).2.1
          (fun _ _ h => (Store.onAttesterSlashing_checkpointStates_latestMessages handled).1 ▸ h)
          (fun slot ok => ⟨slot, (Store.onAttesterSlashing_sameClock handled).getCurrentSlot ▸ ok,
            UInt64.le_refl _⟩)
      | block seen handled =>
        rename_i signed
        have full := handled
        unfold Store.onBlockWithVotes at handled
        simp only [bind_ok_iff, ← Array.foldlM_toList] at handled
        obtain ⟨blocked, blockOk, voted, votedOk, slashedOk⟩ := handled
        have cached : ∀ (c : Checkpoint) (st : BeaconState preset fork),
            blocked.checkpointStates[c]? = some st →
            ((e.world (n + 1)).state w).checkpointStates[c]? = some st := by
          intro c st found
          have votedFound := foldlM_ok_invariant
            (fun s : Store preset fork => s.checkpointStates[c]? = some st)
            (fun _ _ _ old step => cacheKept step old)
            found votedOk
          exact foldlM_ok_invariant
            (fun s : Store preset fork => s.checkpointStates[c]? = some st)
            (fun _ _ _ old step =>
              (Store.onAttesterSlashing_checkpointStates_latestMessages step).1 ▸ old)
            votedFound slashedOk
        have votedBlocks := foldlM_ok_invariant
          (fun s : Store preset fork => s.blocks = blocked.blocks)
          (fun _ _ _ old step => (Store.onAttestation_frame step).2.1.trans old) rfl votedOk
        have blocks := foldlM_ok_invariant
          (fun s : Store preset fork => s.blocks = blocked.blocks)
          (fun _ _ _ old step => (Store.onAttesterSlashing_frame step).2.1.trans old)
          votedBlocks slashedOk
        intro r b found other a member
        rw [blocks] at found
        rcases Store.onBlock_same_or_insert blockOk with same |
          ⟨newRoot, hashed, fresh, blockMap, rest⟩
        · have old := keep ih.2 incl (blocks.trans (congrArg Store.blocks same))
            (fun c st h => cached c st
              ((Store.onBlock_checkpointStates_latestMessages blockOk).1 ▸ h))
            (fun slot ok => ⟨slot, (Store.onBlockWithVotes_sameClock full).getCurrentSlot ▸ ok,
              UInt64.le_refl _⟩)
          exact old r b (blocks ▸ found) other a member
        rw [blockMap, getElem?_insert_root] at found
        split at found
        · cases Option.some.inj found
          have each : ∀ (xs : List (Attestation preset fork)) first last,
              Store.Reachable config anchorState anchorBlock first →
              xs.foldlM (fun s a => s.onAttestation config checks a true) first = .ok last →
              ∀ a ∈ xs, ∃ st indexed, last.checkpointStates[a.data.target]? = some st ∧
                getIndexedAttestation st a = .ok indexed ∧
                (∀ v ∈ indexed.attestingIndices.data,
                  (v, a.data) ∈ attestationStatements (config := config) (checks := checks)
                    anchorState anchorBlock a) ∧
                ∃ slot, last.getCurrentSlot config = .ok slot ∧ a.data.slot < slot := by
            intro xs
            induction xs with
            | nil => simp
            | cons a tail ih =>
              intro first last reached folded item mem
              rw [List.foldlM_cons, bind_ok_iff] at folded
              obtain ⟨mid, step, tailOk⟩ := folded
              rcases List.mem_cons.mp mem with rfl | mem
              · obtain ⟨st, indexed, found, read, signed, slot, slotOk, past⟩ :=
                  blockVote_attestation_read reached step
                refine ⟨st, indexed, ?_, read, signed, slot, ?_, past⟩
                · exact foldlM_ok_invariant
                    (fun s : Store preset fork => s.checkpointStates[item.data.target]? = some st)
                    (fun _ _ _ old ok => cacheKept ok old)
                    found tailOk
                · exact foldlM_ok_invariant
                    (fun s : Store preset fork => s.getCurrentSlot config = .ok slot)
                    (fun _ _ _ old ok => (Store.onAttestation_sameClock ok).getCurrentSlot ▸ old)
                    slotOk tailOk
              · exact ih mid last (reached.attestation step) tailOk item mem
          obtain ⟨st, indexed, found, read, signedRead, slot, slotOk, past⟩ :=
            each _ blocked voted (ih.1.block blockOk) votedOk a
              (Array.mem_toList_iff.mpr member)
          refine ⟨st, indexed, ?_, read, ?_, slot, ?_, past⟩
          · exact foldlM_ok_invariant
              (fun s : Store preset fork => s.checkpointStates[a.data.target]? = some st)
              (fun _ _ _ old step =>
                (Store.onAttesterSlashing_checkpointStates_latestMessages step).1 ▸ old)
              found slashedOk
          · intro v mem
            exact ⟨.block signed, incl (e.view_subset_sent n w seen),
              Or.inl ⟨a, member, signedRead v mem⟩⟩
          · exact foldlM_ok_invariant
              (fun s : Store preset fork => s.getCurrentSlot config = .ok slot)
              (fun _ _ _ old step =>
                (Store.onAttesterSlashing_sameClock step).getCurrentSlot ▸ old)
              slotOk slashedOk
        · obtain ⟨st, indexed, found, read, signedRead, slot, slotOk, past⟩ :=
            ih.2 r b found other a member
          exact ⟨st, indexed, cached _ _
              ((Store.onBlock_checkpointStates_latestMessages blockOk).1 ▸ found), read,
            fun v mem => let ⟨m, sent, vote⟩ := signedRead v mem; ⟨m, incl sent, vote⟩,
            slot, (Store.onBlockWithVotes_sameClock full).getCurrentSlot ▸ slotOk, past⟩
      | payloadAttestation _ handled =>
        obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes handled
        rw [same]
        exact keep ih.2 incl rfl (fun _ _ h => h) (fun slot ok => ⟨slot, ok, UInt64.le_refl _⟩)
      | envelope _ handled =>
        obtain ⟨_, _, _, _, _, record, same⟩ := Store.onExecutionPayloadEnvelope_ok handled
        rw [same]
        obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
        exact keep ih.2 incl rfl (fun _ _ h => h) (fun slot ok => ⟨slot, ok, UInt64.le_refl _⟩)
      | inclusionList _ handled =>
        obtain ⟨_, _, same⟩ := Store.onInclusionList_ok ‹_› handled
        rw [same]
        exact keep ih.2 incl rfl (fun _ _ h => h) (fun slot ok => ⟨slot, ok, UInt64.le_refl _⟩)
  exact (invariant k).2 root block held other a member

private theorem blockVote_epoch {state post : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (blockOk : processBlock config checks sources.engine state block = .ok post)
    {a : Attestation preset fork} (member : a ∈ block.body.attestations.data) :
    a.data.target.epoch = computeEpochAtSlot preset a.data.slot ∧
      (getCurrentEpoch state).toNat ≤ a.data.target.epoch.toNat + 1 := by
  obtain ⟨first, last, frame, _, folded, _⟩ := processBlock_attestationSplit ring blockOk
  obtain ⟨index, bound, found⟩ := List.getElem_of_mem (Array.mem_toList_iff.mpr member)
  obtain ⟨mid, _, prefixOk, ok, -⟩ := (foldlM_ok_steps (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) folded).2 index bound
  rw [found] at ok
  have slot : mid.slot = state.slot :=
    foldlM_ok_invariant (fun next : BeaconState preset fork => next.slot = state.slot)
      (fun _ _ _ holds ok => (frame_processAttestation ok).slot.trans holds) frame.slot prefixOk
  have epoch : a.data.target.epoch = computeEpochAtSlot preset a.data.slot := by
    by_cases altair : .altair ≤ fork
    · simp only [processAttestation, altair, ↓reduceDIte] at ok
      unfold processAttestationAltair at ok
      simp only [bind_ok_iff, ensure_ok_iff] at ok
      obtain ⟨_, _, _, slotEpoch, -⟩ := ok
      exact slotEpoch
    · exact (processAttestation_checks (Nat.lt_of_not_le altair) ok).2.1
  have recent := processAttestation_slotEpoch ok
  have current : getCurrentEpoch mid = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have previous : getPreviousEpoch mid = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  rw [previous, current, ← epoch] at recent
  have prev := getPreviousEpoch_toNat state
  refine ⟨epoch, ?_⟩
  rcases recent with same | same <;> rw [same] <;> omega

/-- A vote decoded before an accepted block occurs in a sent message with the same data.

The target root must match the block-root history of the state that decodes the vote.

The handler's cached target state and the pre-block history reconstruct the same committees. -/
theorem Execution.exists_sent_of_blockVote {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {block : BeaconBlock preset fork}
    {parent advanced post : BeaconState preset fork}
    (held : ((e.world k).state w).blocks[root]? = some block)
    (other : block ≠ anchorBlock)
    (parentFound : ((e.world k).state w).blockStates[block.parentRoot]? = some parent)
    (slotsOk : processSlots config checks parent block.slot = .ok advanced)
    (blockOk : processBlock config checks sources.engine advanced block = .ok post)
    {v : ValidatorIndex} {data : AttestationData}
    (counted : (v, data) ∈ blockVotes advanced block)
    (target : getBlockRoot advanced data.target.epoch = .ok data.target.root)
    (later : getCurrentEpoch anchorState < data.target.epoch)
    {slot : Slot}
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot) :
    ∃ m ∈ (e.world k).sent,
      (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot := by
  have _ := window
  have _ := preGloas
  obtain ⟨a, member, dataEq, indices, indicesOk, voter⟩ := counted
  dsimp only at dataEq voter
  subst data
  obtain ⟨targetState, indexed, cached, indexedOk, sent, current, currentOk, past⟩ :=
    blockVote_read_of_held anchored start held other member
  rw [slotOk, Except.ok.injEq] at currentOk
  subst current
  obtain ⟨epoch, recent⟩ := blockVote_epoch ring blockOk member
  obtain ⟨query, queryOk, history⟩ := getBlockRoot_ok_iff.mp target
  have anchorBefore : anchorState.slot ≤ query := by
    have laterNat := UInt64.lt_iff_toNat_lt.mp later
    rw [getCurrentEpoch_toNat] at laterNat
    have queryNat := (computeStartSlotAtEpoch_ok_iff.mp queryOk).2
    rw [UInt64.le_iff_toNat_le, queryNat]
    exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul positive).mp laterNat)
  obtain ⟨ancestor, ancestorState, checkpointState, _, stored, made, atSlot, run, _⟩ :=
    e.exists_checkpointState_of_preBlock_target anchored honest start positive ring nonzero
      parentFound slotsOk blockOk queryOk history anchorBefore recent
  obtain ⟨base, boundary, baseFound, boundaryOk, looked⟩ :=
    e.checkpointStates_fixedChecks anchored start cached
  rw [stored, Option.some.injEq] at baseFound
  subst base
  rw [queryOk, Except.ok.injEq] at boundaryOk
  subst boundary
  rw [made, Except.ok.injEq] at looked
  subst targetState
  have starts : getCurrentEpoch checkpointState = computeEpochAtSlot preset a.data.slot := by
    unfold getCurrentEpoch
    rw [atSlot, computeEpochAtSlot_computeStartSlotAtEpoch
      (UInt64.lt_iff_toNat_lt.mpr positive) queryOk, epoch]
  have same := run.attestingIndices_eq_through_next_epoch ring starts (by
    rw [starts, ← epoch]
    exact recent)
  obtain ⟨readIndices, readOk, indexedIndices⟩ :=
    getAttestingIndices_of_getIndexedAttestation indexedOk
  rw [same, readOk, Except.ok.injEq] at indicesOk
  subst readIndices
  obtain ⟨m, sent, statement⟩ := sent v (by simpa [indexedIndices] using voter)
  exact ⟨m, sent, statement, past⟩

/-- A held state, or its fixed-check advance toward a held child, is a counting state. -/
theorem Store.counts_of_fixedChecks {store : Store preset fork}
    {root : Root} {base state : BeaconState preset fork}
    (found : store.blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), store.blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state) :
    store.Counts config state := by
  refine ⟨root, base, found, ?_⟩
  rcases advanced with same | ⟨slot, childRoot, child, held, parent, before, processed⟩
  · exact .inl same
  · exact .inr ⟨checks, slot, childRoot, child, held, parent, before, processed⟩

/-- Target provenance starts after the anchor; source equality needs the source epoch bound. -/
def CountedVote (anchorEpoch : Epoch)
    (votes : Set (ValidatorIndex × AttestationData)) (state : BeaconState preset fork)
    (recent : Bool) (position : Nat) : Prop :=
  anchorEpoch < (if recent then getCurrentEpoch state else getPreviousEpoch state) →
    ∃ vote ∈ votes, vote.1.toNat = position ∧
      vote.2.target.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      getBlockRoot state vote.2.target.epoch = .ok vote.2.target.root ∧
      (anchorEpoch < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
        vote.2.source = (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint))

def CountedFlags (anchorEpoch : Epoch)
    (votes : Set (ValidatorIndex × AttestationData)) (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (recent : Bool) (position : Nat),
    TargetFlagAt (recentParticipation state altair recent) position →
      CountedVote anchorEpoch votes state recent position

private theorem countedVote_of_link {anchorEpoch : Epoch}
    {votes : Set (ValidatorIndex × AttestationData)} {state : BeaconState preset fork}
    {recent : Bool} {position : Nat} {vote : ValidatorIndex × AttestationData}
    (member : vote ∈ votes) (link : LinkVote state recent position vote) :
    CountedVote anchorEpoch votes state recent position := by
  intro _
  exact ⟨vote, member, link.1, link.2.1, link.2.2.2, fun _ => link.2.2.1⟩

private theorem countedVote_voteFrame {anchorEpoch : Epoch}
    {votes added : Set (ValidatorIndex × AttestationData)}
    {state after : BeaconState preset fork} {recent : Bool} {position : Nat}
    (holds : CountedVote anchorEpoch votes state recent position)
    (frame : VoteFrame added state after) :
    CountedVote anchorEpoch votes after recent position := by
  have current : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previous : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  unfold CountedVote at holds ⊢
  simpa only [current, previous, frame.currentJustified, frame.previousJustified,
    getBlockRoot, getBlockRootAtSlot, frame.slot, frame.blockRoots] using holds

theorem countedFlags_voteFrame {anchorEpoch : Epoch}
    {votes added : Set (ValidatorIndex × AttestationData)}
    {state after : BeaconState preset fork}
    (holds : CountedFlags anchorEpoch votes state)
    (frame : VoteFrame added state after)
    (sent : ∀ vote ∈ added, getBlockRoot state vote.2.target.epoch = .ok vote.2.target.root →
      anchorEpoch < vote.2.target.epoch → vote ∈ votes) :
    CountedFlags anchorEpoch votes after := by
  intro altair recent position flagged
  rcases frame.flags altair recent position flagged with old | ⟨vote, member, link⟩
  · exact countedVote_voteFrame (holds altair recent position old) frame
  · apply countedVote_voteFrame (frame := frame)
    intro later
    have voted := sent vote member link.2.2.2 (link.2.1 ▸ later)
    exact countedVote_of_link voted link later

private theorem countedFlags_advanceSlot {anchorEpoch : Epoch}
    {votes : Set (ValidatorIndex × AttestationData)}
    {state after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (holds : CountedFlags anchorEpoch votes state)
    (computed : advanceSlot config checks state = .ok after) :
    CountedFlags anchorEpoch votes after := by
  have roots : ∀ {epoch : Epoch} {root : Root}, getBlockRoot state epoch = .ok root →
      (epoch = getCurrentEpoch state ∨ epoch = getPreviousEpoch state) →
      getBlockRoot after epoch = .ok root :=
    fun read near =>
      getBlockRoot_advanceSlot computed read (slot_lt_epoch_add_historical positive window near)
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  obtain ⟨cachedPrevious, cachedCurrent⟩ := processSlot_participation cachedOk
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro altair current position flagged later
  obtain ⟨flags, found, set⟩ := flagged
  unfold recentParticipation at found
  dsimp only at found
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    simp only [processEpoch, altair, ↓reduceDIte] at epochedOk
    obtain ⟨justified, rooted, justifiedOk, head, tail⟩ := processEpochAltair_split epochedOk
    obtain ⟨-, -, -, -, -, -, -, -, -, justifiedCurrent⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    cases current
    · rcases (tail.flags.1 altair position flags).1 found with rotated | rfl
      · rcases (head.flags.1 altair position flags).2 rotated with old | rfl
        · rw [justifiedCurrent, cachedCurrent] at old
          have prior : anchorEpoch < getCurrentEpoch state := by
            simpa only [Bool.false_eq_true, ↓reduceIte, previousEq] using later
          obtain ⟨vote, voted, index, epoch, rootOk, source⟩ :=
            holds altair true position ⟨flags, old, set⟩ prior
          refine ⟨vote, voted, index, epoch.trans previousEq.symm,
            roots rootOk (.inl epoch), ?_⟩
          intro above
          change anchorEpoch < epoched.previousJustifiedCheckpoint.epoch at above
          change vote.2.source = epoched.previousJustifiedCheckpoint
          simp only [tail.previousJustified, processParticipationFlagUpdates,
            head.previousJustified] at above ⊢
          by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
          · have same := processJustificationAndFinalization_early_eq early justifiedOk
            rw [same, cachedFrame.previousJustified] at above
            -- An early rotation can change the source only at epoch zero, below this guard.
            have earlyState : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := by
              simpa only [getCurrentEpoch, cachedFrame.slot] using early
            have previous := getPreviousEpoch_toNat state
            have order := ordered.2
            unfold JustifiedSettled at settled
            simp only [UInt64.lt_iff_toNat_lt] at above prior
            simp only [UInt64.le_iff_toNat_le] at earlyState settled order
            norm_num [GENESIS_EPOCH] at earlyState
            omega
          · have earlyHolds : JustifiedEarly cached := fun h => (early h).elim
            rw [earlyHolds.previousJustified_of_justification justifiedOk,
              cachedFrame.currentJustified] at above ⊢
            exact source above
        · exact absurd set (by decide)
      · exact absurd set (by decide)
    · rcases (tail.flags.1 altair position flags).2 found with rotated | rfl
      · simp only [processParticipationFlagUpdates, Array.getElem?_replicate] at rotated
        split at rotated
        · cases rotated
          exact absurd set (by decide)
        · cases rotated
      · exact absurd set (by decide)
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    cases current
    · rw [cachedPrevious] at found
      have prior : anchorEpoch < getPreviousEpoch state := by
        simpa only [Bool.false_eq_true, ↓reduceIte, previousEq] using later
      obtain ⟨vote, voted, index, epoch, rootOk, source⟩ :=
        holds altair false position ⟨flags, found, set⟩ prior
      refine ⟨vote, voted, index, epoch.trans previousEq.symm,
        roots rootOk (.inr epoch), ?_⟩
      simpa only [Bool.false_eq_true, ↓reduceIte, cachedFrame.previousJustified] using source
    · rw [cachedCurrent] at found
      have prior : anchorEpoch < getCurrentEpoch state := by
        simpa only [↓reduceIte, currentEq] using later
      obtain ⟨vote, voted, index, epoch, rootOk, source⟩ :=
        holds altair true position ⟨flags, found, set⟩ prior
      refine ⟨vote, voted, index, epoch.trans currentEq.symm,
        roots rootOk (.inl epoch), ?_⟩
      simpa only [↓reduceIte, cachedFrame.currentJustified] using source

theorem countedFlags_advanceSlots {anchorEpoch : Epoch}
    {votes : Set (ValidatorIndex × AttestationData)}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∀ {count : Nat} {state after : BeaconState preset fork}, Invariant state →
      CountedFlags anchorEpoch votes state →
      advanceSlots config checks count state = .ok after → CountedFlags anchorEpoch votes after
  | 0, state, after, _, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | count + 1, state, after, sound, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact countedFlags_advanceSlots positive window (advanceSlot_invariant sound nextOk).1
      (countedFlags_advanceSlot positive window sound.ordered sound.settled holds nextOk) rest

theorem countedFlags_quorum {anchorEpoch : Epoch}
    {votes : Set (ValidatorIndex × AttestationData)} {state : BeaconState preset fork}
    (holds : CountedFlags anchorEpoch votes state) (altair : .altair ≤ fork)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (recent : Bool)
    (later : anchorEpoch < (if recent then getCurrentEpoch state else getPreviousEpoch state))
    {indices : List ValidatorIndex}
    (counted : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices) :
    v ∈ quorumVoters state ∧ ∃ data, (v, data) ∈ votes ∧
      data.target.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      getBlockRoot state data.target.epoch = .ok data.target.root ∧
      (anchorEpoch < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
        data.source = (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint)) := by
  have distinct : getPreviousEpoch state ≠ getCurrentEpoch state := by
    intro same
    have := congrArg UInt64.toNat same
    rw [getPreviousEpoch_toNat] at this
    exact late (UInt64.le_iff_toNat_le.mpr (by simp [GENESIS_EPOCH]; omega))
  obtain ⟨active, ⟨validator, found, clean⟩, flags, read, set⟩ :=
    mem_getUnslashedParticipatingIndices counted v member
  have flag : TargetFlagAt (recentParticipation state altair recent) v.toNat := by
    refine ⟨flags, ?_, set⟩
    cases recent
    · simpa [recentParticipation, distinct] using read
    · simpa [recentParticipation] using read
  obtain ⟨⟨index, data⟩, voted, position, epoch, root, source⟩ :=
    holds altair recent v.toNat flag later
  have same : index = v := UInt64.toNat_inj.mp position
  subst index
  exact ⟨mem_quorumVoters_of_active active found clean, data, voted, epoch, root, source⟩

/-- Pending attestations retain their original data and bits, even before their target is read. -/
def CountedPending (anchorEpoch : Epoch)
    (origin : PendingAttestation preset → Prop) (state : BeaconState preset fork) : Prop :=
  ∀ (before : fork < .altair) (recent : Bool),
    anchorEpoch < (if recent then getCurrentEpoch state else getPreviousEpoch state) →
    ∀ pending ∈ recentPending state before recent,
      pending.data.target.epoch =
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
      (anchorEpoch < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
        pending.data.source = (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint)) ∧
      origin pending

private theorem countedPending_frame {anchorEpoch : Epoch}
    {origin : PendingAttestation preset → Prop} {state after : BeaconState preset fork}
    (holds : CountedPending anchorEpoch origin state) (frame : PendingFrame state after) :
    CountedPending anchorEpoch origin after := by
  have current : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previous : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  intro before recent later pending member
  have lists : recentPending after before recent = recentPending state before recent := by
    cases recent <;> simp [recentPending, frame.previousPending, frame.currentPending]
  rw [lists] at member
  rw [current, previous] at later ⊢
  obtain ⟨epoch, slot, source, voted⟩ := holds before recent later pending member
  refine ⟨epoch, slot, ?_, voted⟩
  simpa only [frame.currentJustified, frame.previousJustified] using source

private theorem countedPending_attestation {anchorEpoch : Epoch}
    {origin : PendingAttestation preset → Prop} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (before : fork < .altair) (holds : CountedPending anchorEpoch origin state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (sent : ∀ pending : PendingAttestation preset, pending.data = attestation.data →
      pending.aggregationBits.bits = attestation.aggregationBits.bits → origin pending) :
    CountedPending anchorEpoch origin after := by
  have frame := voteFrame_processAttestation computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, currentEq]
  have kept : ∀ (current : Bool),
      anchorEpoch < (if current then getCurrentEpoch after else getPreviousEpoch after) →
      ∀ pending ∈ recentPending state before current,
      pending.data.target.epoch =
          (if current then getCurrentEpoch after else getPreviousEpoch after) ∧
        computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
        (anchorEpoch < (if current then after.currentJustifiedCheckpoint
          else after.previousJustifiedCheckpoint).epoch →
          pending.data.source = (if current then after.currentJustifiedCheckpoint
            else after.previousJustifiedCheckpoint)) ∧
        origin pending := by
    intro current later pending member
    rw [currentEq, previousEq] at later ⊢
    obtain ⟨epoch, slot, source, voted⟩ := holds before current later pending member
    refine ⟨epoch, slot, ?_, voted⟩
    simpa only [frame.currentJustified, frame.previousJustified] using source
  obtain ⟨recent, slotEpoch, -, -, -, ⟨committee, committeeOk, -⟩, source⟩ :=
    processAttestation_checks before computed
  obtain ⟨pending, bits, dataEq, -, -, recorded, -⟩ := processAttestation_records before computed
  have lists : ∀ current, recentPending after before current =
      if current = (attestation.data.target.epoch == getCurrentEpoch state) then
        (recentPending state before current).push pending
      else recentPending state before current := by
    intro current
    have records := recordPendingAttestation_ok recorded
    cases current <;> split at records <;>
      simp_all [recentPending]
    · rw [← records.2]
    · rw [← records.2]
  intro before' current later other member
  rw [lists] at member
  split at member
  · rename_i chosen
    rcases Array.mem_push.mp member with old | rfl
    · exact kept current later other old
    rw [dataEq]
    have epoch : attestation.data.target.epoch =
        (if current then getCurrentEpoch after else getPreviousEpoch after) := by
      cases current
      · have differ : attestation.data.target.epoch ≠ getCurrentEpoch state :=
          ne_of_beq_false chosen.symm
        simpa [previousEq] using recent.resolve_right differ
      · simpa [currentEq] using beq_iff_eq.mp chosen.symm
    refine ⟨epoch, slotEpoch.symm, ?_, sent other dataEq bits⟩
    intro _
    rw [frame.currentJustified, frame.previousJustified, source]
    cases current
    · simp [ne_of_beq_false chosen.symm]
    · simp [beq_iff_eq.mp chosen.symm]
  · exact kept current later other member

private theorem countedPending_block {anchorEpoch : Epoch}
    {origin : PendingAttestation preset → Prop} {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (before : fork < .altair)
    (holds : CountedPending anchorEpoch origin state)
    (computed : processBlock config checks sources.engine state block = .ok after)
    (sent : ∀ a ∈ block.body.attestations.data, ∀ pending : PendingAttestation preset,
      pending.data = a.data → pending.aggregationBits.bits = a.aggregationBits.bits →
      origin pending) : CountedPending anchorEpoch origin after := by
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  apply countedPending_frame (frame := tail)
  have each : ∀ (xs : List (Attestation preset fork)) first last,
      CountedPending anchorEpoch origin first →
      (∀ a ∈ xs, ∀ pending : PendingAttestation preset,
        pending.data = a.data → pending.aggregationBits.bits = a.aggregationBits.bits →
        origin pending) →
      xs.foldlM (processAttestation config checks · state.latestBlockHeader.slot ·) first =
        .ok last → CountedPending anchorEpoch origin last := by
    intro xs
    induction xs with
    | nil => intro first last holds _ computed; cases computed; exact holds
    | cons a rest ih =>
      intro first last holds all computed
      rw [List.foldlM_cons, bind_ok_iff] at computed
      obtain ⟨middle, step, restOk⟩ := computed
      exact ih middle last (countedPending_attestation before holds step
        (all a (by simp))) (fun b member => all b (by simp [member])) restOk
  exact each _ first last (countedPending_frame holds head)
    (fun a mem => sent a (Array.mem_toList_iff.mp mem)) attested

private theorem countedPending_advanceSlot {anchorEpoch : Epoch}
    {origin : PendingAttestation preset → Prop} {state after : BeaconState preset fork}
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (holds : CountedPending anchorEpoch origin state)
    (computed : advanceSlot config checks state = .ok after) :
    CountedPending anchorEpoch origin after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedLists : ∀ before current, recentPending cached before current =
      recentPending state before current := by
    intro before current
    cases current <;> simp [recentPending, cachedEq]
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro before current later pending member
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation before epochedOk
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    cases current
    · have moved : recentPending { epoched with slot := next } before false =
          recentPending state before true := by
        rw [← cachedLists before true]
        simp [recentPending, rotated]
      rw [moved] at member
      have prior : anchorEpoch < getCurrentEpoch state := by
        simpa only [Bool.false_eq_true, ↓reduceIte, previousEq] using later
      obtain ⟨epoch, slot, source, voted⟩ := holds before true prior pending member
      refine ⟨epoch.trans previousEq.symm, slot, ?_, voted⟩
      intro above
      change anchorEpoch < epoched.previousJustifiedCheckpoint.epoch at above
      change pending.data.source = epoched.previousJustifiedCheckpoint
      rw [frame.previousJustified] at above ⊢
      by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
      · have same := processJustificationAndFinalization_early_eq early justifiedOk
        rw [same, cachedFrame.previousJustified] at above
        have earlyState : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := by
          simpa only [getCurrentEpoch, cachedFrame.slot] using early
        have previous := getPreviousEpoch_toNat state
        have order := ordered.2
        unfold JustifiedSettled at settled
        simp only [UInt64.lt_iff_toNat_lt] at above prior
        simp only [UInt64.le_iff_toNat_le] at earlyState settled order
        norm_num [GENESIS_EPOCH] at earlyState
        omega
      · have earlyHolds : JustifiedEarly cached := fun h => (early h).elim
        rw [earlyHolds.previousJustified_of_justification justifiedOk,
          cachedFrame.currentJustified] at above ⊢
        exact source above
    · simp [recentPending, emptied] at member
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    have lists : recentPending { cached with slot := next } before current =
        recentPending state before current := cachedLists before current
    rw [lists] at member
    rw [currentEq, previousEq] at later ⊢
    obtain ⟨epoch, slot, source, voted⟩ := holds before current later pending member
    refine ⟨epoch, slot, ?_, voted⟩
    simpa only [cachedFrame.currentJustified, cachedFrame.previousJustified] using source

theorem countedPending_advanceSlots {anchorEpoch : Epoch}
    {origin : PendingAttestation preset → Prop} :
    ∀ {count : Nat} {state after : BeaconState preset fork}, Invariant state →
      CountedPending anchorEpoch origin state →
      advanceSlots config checks count state = .ok after →
        CountedPending anchorEpoch origin after
  | 0, state, after, _, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | count + 1, state, after, sound, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact countedPending_advanceSlots (advanceSlot_invariant sound nextOk).1
      (countedPending_advanceSlot sound.ordered sound.settled holds nextOk) rest

private theorem countedFlags_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {slot : Slot} (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    {root : Root} {state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some state) :
    CountedFlags (getCurrentEpoch anchorState)
      {vote | ∃ m ∈ (e.world k).sent,
        vote ∈ statements config checks anchorState anchorBlock m ∧ vote.2.slot < slot} state := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
      intro n
      induction n with
      | zero =>
        change Store.Reachable config anchorState anchorBlock (e.start w)
        rw [start]
        exact .anchor anchored
      | succ n ih =>
        rcases e.state_succ n w with same | ⟨_, moved⟩
        · exact same ▸ ih
        · exact moved.reachable ih
    exact all k
  obtain ⟨block, held⟩ := reachable.known_of_blockState found
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, atAnchor, -⟩ := reachable.blockStatesFromParents held
    rw [found, Option.some.injEq] at postOk
    subst post
    rw [atAnchor same]
    intro _ recent _ _ later
    have bound := getPreviousEpoch_le anchorState
    cases recent <;> simp only [Bool.false_eq_true, ↓reduceIte] at later
    · exact (UInt64.not_lt.mpr bound later).elim
    · exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start held found same
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transitioned
    have parentHolds := countedFlags_held anchored sound positive window ring preGloas
      honest start nonzero slotOk parentFound
    have parentSound := (reachable.ordered sound).2 parentFound
    have advancedHolds : CountedFlags (getCurrentEpoch anchorState)
        {vote | ∃ m ∈ (e.world k).sent,
          vote ∈ statements config checks anchorState anchorBlock m ∧ vote.2.slot < slot}
        advanced := by
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
      obtain ⟨_, _, processed⟩ := slotsOk
      exact countedFlags_advanceSlots positive window parentSound parentHolds processed
    apply countedFlags_voteFrame advancedHolds (voteFrame_processBlock ring blockOk)
    intro vote counted target later
    apply e.exists_sent_of_blockVote anchored positive window ring preGloas honest start
      nonzero held same parentFound (message ▸ slotsOk) (message ▸ blockOk)
      (message ▸ counted) target later slotOk
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

theorem countedPending_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {root : Root} {state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some state) :
    CountedPending (getCurrentEpoch anchorState)
      (fun pending => ∃ (root : Root) (block : BeaconBlock preset fork)
        (a : Attestation preset fork),
        ((e.world k).state w).blocks[root]? = some block ∧ block ≠ anchorBlock ∧
        a ∈ block.body.attestations.data ∧ pending.data = a.data ∧
        pending.aggregationBits.bits = a.aggregationBits.bits) state := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
      intro n
      induction n with
      | zero =>
        change Store.Reachable config anchorState anchorBlock (e.start w)
        rw [start]
        exact .anchor anchored
      | succ n ih =>
        rcases e.state_succ n w with same | ⟨_, moved⟩
        · exact same ▸ ih
        · exact moved.reachable ih
    exact all k
  obtain ⟨block, held⟩ := reachable.known_of_blockState found
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, atAnchor, -⟩ := reachable.blockStatesFromParents held
    rw [found, Option.some.injEq] at postOk
    subst post
    rw [atAnchor same]
    intro _ recent later
    have bound := getPreviousEpoch_le anchorState
    cases recent <;> simp only [Bool.false_eq_true, ↓reduceIte] at later
    · exact (UInt64.not_lt.mpr bound later).elim
    · exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start held found same
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transitioned
    have parentHolds := countedPending_held anchored sound honest start parentFound
    have parentSound := (reachable.ordered sound).2 parentFound
    have advancedHolds : CountedPending (getCurrentEpoch anchorState)
        (fun pending => ∃ (root : Root) (block : BeaconBlock preset fork)
          (a : Attestation preset fork),
          ((e.world k).state w).blocks[root]? = some block ∧ block ≠ anchorBlock ∧
          a ∈ block.body.attestations.data ∧ pending.data = a.data ∧
          pending.aggregationBits.bits = a.aggregationBits.bits) advanced := by
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
      obtain ⟨_, _, processed⟩ := slotsOk
      exact countedPending_advanceSlots parentSound parentHolds processed
    intro before
    apply countedPending_block before advancedHolds blockOk ?_ before
    intro a member pending data bits
    exact ⟨root, block, a, held, same, message ▸ member, data, bits⟩
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

theorem countedPending_member {anchorEpoch : Epoch}
    {origin : PendingAttestation preset → Prop} {state : BeaconState preset fork}
    (before : fork < .altair) (holds : CountedPending anchorEpoch origin state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (recent : Bool)
    (later : anchorEpoch < (if recent then getCurrentEpoch state else getPreviousEpoch state))
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingTargetAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    {indices : List ValidatorIndex}
    (counted : getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices) :
    ∃ pending attesters, origin pending ∧
      getPendingAttestingIndices state pending = .ok attesters ∧ v ∈ attesters ∧
      pending.data.target.epoch =
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
      getBlockRoot state pending.data.target.epoch = .ok pending.data.target.root ∧
      (anchorEpoch < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
        pending.data.source = (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint)) ∧
      ∃ validator, getValidator state v = .ok validator ∧ validator.slashed = false := by
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at counted
  obtain ⟨signers, signersOk, unslashed⟩ := counted
  have clean := passes_of_mem_filterM_ok unslashed member
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at clean
  obtain ⟨validator, validatorOk, clean⟩ := clean
  have flattened := mem_sortedSet.mp (mem_of_filterM_ok unslashed member)
  obtain ⟨signed, signedMember, inside⟩ := List.mem_flatten.mp flattened
  obtain ⟨length, each⟩ := mapM_eq_ok_iff.mp signersOk
  obtain ⟨position, bound, rfl⟩ := List.getElem_of_mem signedMember
  have attestersOk := each position (length ▸ bound)
  have listed : attestations.toList[position]'(length ▸ bound) ∈ attestations.toList :=
    List.getElem_mem _
  generalize attestations.toList[position]'(length ▸ bound) = pending at attestersOk listed
  simp only [getMatchingTargetAttestations, bind_ok_iff] at matching
  obtain ⟨items, itemsOk, matching⟩ := matching
  split at matching
  · simp only [pure, Except.pure, Except.ok.injEq] at matching
    subst matching
    simp at listed
  simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at matching
  obtain ⟨root, rootOk, rfl⟩ := matching
  obtain ⟨found, sameRoot⟩ := Array.mem_filter.mp (Array.mem_toList_iff.mp listed)
  have distinct : getPreviousEpoch state ≠ getCurrentEpoch state := by
    intro same
    have := congrArg UInt64.toNat same
    rw [getPreviousEpoch_toNat] at this
    exact late (UInt64.le_iff_toNat_le.mpr (by simp [GENESIS_EPOCH]; omega))
  have itemsEq : items = recentPending state before recent := by
    cases recent <;>
      simpa [getMatchingSourceAttestations, recentPending, distinct, getPreviousEpoch_le,
        ensure, pure, Except.pure, bind, Except.bind] using itemsOk.symm
  rw [itemsEq] at found
  obtain ⟨epoch, slot, source, voted⟩ := holds before recent later pending found
  refine ⟨pending, _, voted, attestersOk, inside, epoch, slot, ?_, source,
    validator, validatorOk, ?_⟩
  · rw [epoch, beq_iff_eq.mp sameRoot]
    exact rootOk
  · simpa using clean

private theorem counted_history_run {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {base state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    {query : Slot} {readRoot : Root}
    (known : ∃ block, ((e.world k).state w).blocks[readRoot]? = some block)
    (read : getBlockRootAtSlot state query = .ok readRoot)
    (later : anchorState.slot ≤ query) :
    ∃ ancestorState checkpointState,
      ((e.world k).state w).blockStates[readRoot]? = some ancestorState ∧
      lookaheadState config checks ancestorState query = .ok checkpointState ∧
      checkpointState.slot = query ∧ RunKept checkpointState state := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
      intro n
      induction n with
      | zero =>
        change Store.Reachable config anchorState anchorBlock (e.start w)
        rw [start]
        exact .anchor anchored
      | succ n ih =>
        rcases e.state_succ n w with same | ⟨_, moved⟩
        · exact same ▸ ih
        · exact moved.reachable ih
    exact all k
  have transitions := fun r b st held stored other =>
    e.exists_transition_of_nonanchor_block anchored honest start
      (k := k) (root := r) (block := b) (state := st) held stored other
  rcases advanced with rfl | ⟨slot, childRoot, child, held, parentEq, before, processed⟩
  · obtain ⟨_, ancestorState, checkpointState, _, stored, made, atSlot, run⟩ :=
      reachable.blockState_history_run transitions nonzero found read later
    exact ⟨ancestorState, checkpointState, stored, made, atSlot, run⟩
  · by_cases old : query < base.slot
    · have run := processed
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
      obtain ⟨_, _, run⟩ := run
      obtain ⟨_, ancestorState, checkpointState, _, stored, made, atSlot, kept⟩ :=
        reachable.blockState_history_run transitions nonzero found
          (getBlockRootAtSlot_of_advanceSlots run read old) later
      exact ⟨ancestorState, checkpointState, stored, made, atSlot,
        kept.trans (runKept_processSlots processed)⟩
    · obtain ⟨baseBlock, baseHeld⟩ := reachable.known_of_blockState found
      have eq : readRoot = root := by
        by_cases same : baseBlock = anchorBlock
        · obtain ⟨post, stored, atAnchor, _⟩ := reachable.blockStatesFromParents baseHeld
          rw [found, Option.some.injEq] at stored
          subst post
          obtain ⟨readBlock, readHeld⟩ := known
          rw [atAnchor same] at processed
          exact reachable.anchor_processSlots_root (same ▸ nonzero _ _ baseHeld)
            (same ▸ baseHeld) readHeld processed read later
        · exact reachable.blockState_processSlots_root baseHeld found same
            (nonzero _ _ baseHeld) processed read
            ((reachable.blockState_header baseHeld found same).1 ▸ UInt64.not_lt.mp old)
      have high : query < slot := by
        rw [← (processSlots_slot processed).2]
        exact UInt64.lt_iff_toNat_lt.mpr (getBlockRootAtSlot_ok_iff.mp read).1
      obtain ⟨checkpointState, made, atSlot, run⟩ :=
        lookaheadState_of_processSlots processed (UInt64.not_lt.mp old) high
      exact ⟨base, checkpointState, eq.symm ▸ found, made, atSlot, run⟩

private theorem counted_provenance {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {base state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (recent : Bool)
    (later : getCurrentEpoch anchorState <
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    {indices : List ValidatorIndex}
    (counted : (∃ altair : .altair ≤ fork,
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
      ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
        getMatchingTargetAttestations state before
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices)
    {slot : Slot} (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot) :
    v ∈ quorumVoters state ∧ ∃ data,
      data.target.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      getBlockRoot state data.target.epoch = .ok data.target.root ∧
      (getCurrentEpoch anchorState < (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).epoch →
        data.source = (if recent then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint)) ∧
      ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot := by
  have reachable : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
      intro n
      induction n with
      | zero =>
        change Store.Reachable config anchorState anchorBlock (e.start w)
        rw [start]
        exact .anchor anchored
      | succ n ih =>
        rcases e.state_succ n w with same | ⟨_, moved⟩
        · exact same ▸ ih
        · exact moved.reachable ih
    exact all k
  have baseSound := (reachable.ordered sound).2 found
  rcases counted with ⟨altair, counted⟩ | ⟨before, attestations, matching, counted⟩
  · have flags := countedFlags_held anchored sound positive window ring preGloas honest start
      nonzero slotOk found
    have stateFlags : CountedFlags (getCurrentEpoch anchorState)
        {vote | ∃ m ∈ (e.world k).sent,
          vote ∈ statements config checks anchorState anchorBlock m ∧ vote.2.slot < slot}
        state := by
      rcases advanced with rfl | ⟨_, _, _, _, _, _, processed⟩
      · exact flags
      · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
        obtain ⟨_, _, run⟩ := processed
        exact countedFlags_advanceSlots positive window baseSound flags run
    obtain ⟨quorum, data, sent, epoch, root, source⟩ :=
      countedFlags_quorum stateFlags altair late recent later counted member
    exact ⟨quorum, data, epoch, root, source, sent⟩
  · have pending := countedPending_held anchored sound honest start found
    have statePending : CountedPending (getCurrentEpoch anchorState)
        (fun pending => ∃ (root : Root) (block : BeaconBlock preset fork)
          (a : Attestation preset fork),
          ((e.world k).state w).blocks[root]? = some block ∧ block ≠ anchorBlock ∧
          a ∈ block.body.attestations.data ∧ pending.data = a.data ∧
          pending.aggregationBits.bits = a.aggregationBits.bits) state := by
      rcases advanced with rfl | ⟨_, _, _, _, _, _, processed⟩
      · exact pending
      · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
        obtain ⟨_, _, run⟩ := processed
        exact countedPending_advanceSlots baseSound pending run
    obtain ⟨item, attesters, ⟨blockRoot, block, a, held, other, listed, dataEq, bits⟩,
      attestersOk, inside, epoch, slotEpoch, target, source, validator, validatorOk, clean⟩ :=
      countedPending_member before statePending late recent later matching counted member
    have active : v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) := by
      have read := attestersOk
      simp only [getPendingAttestingIndices, bind_ok_iff] at read
      obtain ⟨committee, committeeOk, attested⟩ := read
      have active := mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
        (mem_of_committeeAttesters attested inside)
      rwa [slotEpoch, epoch] at active
    refine ⟨mem_quorumVoters_of_active active validatorOk clean, item.data,
      epoch, target, source, ?_⟩
    obtain ⟨targetState, indexed, cached, indexedOk, sent, current, currentOk, past⟩ :=
      blockVote_read_of_held anchored start held other listed
    rw [slotOk, Except.ok.injEq] at currentOk
    subst current
    obtain ⟨cacheBase, boundary, cacheBaseFound, boundaryOk, looked⟩ :=
      e.checkpointStates_fixedChecks anchored start cached
    obtain ⟨query, queryOk, history⟩ := getBlockRoot_ok_iff.mp target
    have anchorBefore : anchorState.slot ≤ query := by
      have laterNat := UInt64.lt_iff_toNat_lt.mp later
      rw [← epoch, getCurrentEpoch_toNat] at laterNat
      have queryNat := (computeStartSlotAtEpoch_ok_iff.mp queryOk).2
      rw [UInt64.le_iff_toNat_le, queryNat]
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul positive).mp laterNat)
    have known : ∃ block, ((e.world k).state w).blocks[item.data.target.root]? = some block := by
      rw [dataEq]
      exact reachable.known_of_blockState cacheBaseFound
    obtain ⟨ancestorState, checkpointState, stored, made, atSlot, run⟩ :=
      counted_history_run anchored honest start nonzero found advanced known history anchorBefore
    -- The counting history and the handler cache reconstruct the same target committee state.
    rw [dataEq] at stored queryOk
    rw [stored, Option.some.injEq] at cacheBaseFound
    subst cacheBase
    rw [queryOk, Except.ok.injEq] at boundaryOk
    subst boundary
    rw [made, Except.ok.injEq] at looked
    subst targetState
    have starts : getCurrentEpoch checkpointState = item.data.target.epoch := by
      unfold getCurrentEpoch
      rw [atSlot]
      exact computeEpochAtSlot_computeStartSlotAtEpoch
        (UInt64.lt_iff_toNat_lt.mpr positive) (dataEq ▸ queryOk)
    have ends : (getCurrentEpoch state).toNat ≤ item.data.target.epoch.toNat + 1 := by
      rw [epoch]
      have previous := getPreviousEpoch_toNat state
      cases recent <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have committees := run.committeesKept_through_next_epoch ring starts ends
    have pendingRead := attestersOk
    unfold getPendingAttestingIndices at pendingRead
    rw [committees _ _ slotEpoch] at pendingRead
    rw [dataEq, bits] at pendingRead
    have signers : getAttestingIndices checkpointState a = .ok (sortedSet attesters) := by
      simp only [bind_ok_iff] at pendingRead
      obtain ⟨committee, committeeOk, attested⟩ := pendingRead
      simp only [getAttestingIndices_of_lt_electra (Nat.lt_trans before (by decide)),
        committeeOk, bind, Except.bind, attested, pure, Except.pure]
    obtain ⟨readIndices, readOk, indexedIndices⟩ :=
      getAttestingIndices_of_getIndexedAttestation indexedOk
    rw [signers, Except.ok.injEq] at readOk
    subst readIndices
    obtain ⟨m, sent, statement⟩ := sent v (by simpa [indexedIndices] using mem_sortedSet.mpr inside)
    exact ⟨m, sent, dataEq.symm ▸ statement, dataEq.symm ▸ past⟩

/-- A counted index for a source after the anchor has a sent vote for the complete link.

The counting state uses the execution's checks.

The justified checkpoint that the state holds for the epoch of the count is after the anchor.

A first-epoch anchor may hold two justified checkpoints of its epoch, with different roots.

Then at the third epoch the previous-epoch flags may come from votes with either as source.

Both have the anchor's epoch, so this bound excludes that case.

It also excludes inherited anchor participation.

It does not assert a provenance invariant for that participation. -/
theorem Execution.exists_sent_link_of_counted {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {base state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (recent : Bool)
    (above : getCurrentEpoch anchorState < (if recent then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint).epoch)
    {indices : List ValidatorIndex}
    (counted : (∃ altair : .altair ≤ fork,
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
      ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
        getMatchingTargetAttestations state before
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices)
    {slot : Slot} (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot) :
    v ∈ quorumVoters state ∧ ∃ data,
      LinkVote state recent v.toNat (v, data) ∧
      ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot := by
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  have baseSound := ((reachable k).ordered sound).2 found
  have stateSound : Invariant state := by
    rcases advanced with rfl | ⟨_, _, _, _, _, _, processed⟩
    · exact baseSound
    · exact (processSlots_invariant baseSound processed).1
  have later : getCurrentEpoch anchorState <
      (if recent then getCurrentEpoch state else getPreviousEpoch state) := by
    cases recent
    · exact UInt64.lt_of_lt_of_le above (UInt64.le_trans stateSound.ordered.2 stateSound.settled)
    · exact UInt64.lt_of_lt_of_le above
        (UInt64.le_trans stateSound.settled (getPreviousEpoch_le state))
  obtain ⟨quorum, data, epoch, target, source, sent⟩ :=
    counted_provenance anchored sound positive window ring preGloas honest start nonzero
      found advanced late recent later counted member slotOk
  exact ⟨quorum, data, ⟨rfl, epoch, source above, target⟩, sent⟩

/-- A counted index for an epoch after the anchor has a sent vote for the counted target.

The counting state uses the execution's checks.

The vote has the target epoch of the count, and the target root that the state records for it.

Its source is not fixed: at the third epoch, an anchor of the first epoch may leave two sources.

There the previous-epoch flags come from votes with the current justified checkpoint as source.

Votes included in the third epoch for the previous target carry the previous one instead.

The recent epoch restriction excludes inherited anchor participation.

It does not assert a provenance invariant for that participation. -/
theorem Execution.exists_sent_target_of_counted {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {base state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (recent : Bool)
    (later : getCurrentEpoch anchorState <
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    {indices : List ValidatorIndex}
    (counted : (∃ altair : .altair ≤ fork,
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
      ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
        getMatchingTargetAttestations state before
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices)
    {slot : Slot} (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot) :
    v ∈ quorumVoters state ∧ ∃ data,
      data.target.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      getBlockRoot state data.target.epoch = .ok data.target.root ∧
      ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot := by
  obtain ⟨quorum, data, epoch, target, _, sent⟩ :=
    counted_provenance anchored sound positive window ring preGloas honest start nonzero
      found advanced late recent later counted member slotOk
  exact ⟨quorum, data, epoch, target, sent⟩

/-- A passing count above the anchor supplies a sent source link from the chosen set. -/
theorem Execution.exists_sent_source_of_counted {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {base state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (recent : Bool)
    (above : getCurrentEpoch anchorState < (if recent then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint).epoch)
    {indices : List ValidatorIndex}
    (counted : (∃ altair : .altair ≤ fork,
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
      ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
        getMatchingTargetAttestations state before
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok indices)
    {slot : Slot} (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    {total balance threshold weight : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state indices = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat) :
    ∃ v data, p v ∧
      data.source = (if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint) ∧
      data.target.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m := by
  let attested : Set (ValidatorIndex × AttestationData) :=
    {vote | ∃ m ∈ (e.world k).sent,
      vote ∈ statements config checks anchorState anchorBlock m}
  have provenance : ∀ v ∈ indices, v ∈ quorumVoters state ∧
      ∃ data, (v, data) ∈ attested ∧ LinkVote state recent v.toNat (v, data) := by
    intro v member
    obtain ⟨quorum, data, link, m, sent, statement, -⟩ :=
      e.exists_sent_link_of_counted anchored sound positive window ring preGloas honest start
        nonzero found advanced late recent above counted member slotOk
    exact ⟨quorum, data, ⟨m, sent, statement⟩, link⟩
  obtain ⟨v, data, good, signed, link⟩ := exists_linkVote_of_justificationTest totalOk
    balanceOk thresholdOk weightOk passed large provenance p few
  exact ⟨v, data, good, link.2.2.1, link.2.1, signed⟩

/-- Historical block-state finalization retains a sent source link from the chosen set. -/
theorem Execution.blockState_sent_sources {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {epoch : Epoch} {slot : Slot}
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (large : ∀ state : BeaconState preset fork,
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ epoch →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (few : ∀ (state : BeaconState preset fork) (total : Gwei),
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ epoch →
      getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat)
    {root : Root} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state)
    (bounded : getCurrentEpoch state ≤ epoch) :
    FinalizationSources (fun source target => ∃ v data, p v ∧ data.source = source ∧
      data.target.epoch = target ∧ ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m)
      (getCurrentEpoch anchorState) (getCurrentEpoch state).toNat state := by
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  apply (reachable k).blockState_finalizationSources (checks := checks)
    (engine := sources.engine) (limit := epoch) ?_ ?_ ?_ stored bounded
  · apply FinalizationSources.anchor
    · exact UInt64.le_trans sound.ordered.2
        (UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState))
    · exact UInt64.le_trans sound.ordered.1 (UInt64.le_trans sound.ordered.2
        (UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState)))
  · intro root block state held found other
    exact e.exists_transition_of_nonanchor_block anchored honest start held found other
  · intro root childRoot base middle cached justified child found held parent visited before bound
      cachedOk justifiedOk old
    have baseSound := ((reachable k).ordered sound).2 found
    have middleSound : Invariant middle := by
      rcases visited with same | processed
      · exact same ▸ baseSound
      · exact (processSlots_invariant baseSound processed).1
    have cachedSound := (frame_processSlot cachedOk).invariant middleSound
    apply old.process_cached positive window cachedOk cachedSound.ordered cachedSound.settled
      ?_ justifiedOk
    intro late recent indices total balance threshold weight counted totalOk balanceOk thresholdOk
      weightOk passed above
    have advanced : middle = base ∨ ∃ (slot : Slot) (childRoot : Root)
        (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok middle := by
      rcases visited with same | processed
      · exact .inl same
      · exact .inr ⟨middle.slot, childRoot, child, held, parent, UInt64.le_of_lt before,
          processed⟩
    have counts := Store.counts_of_fixedChecks found advanced
    exact e.exists_sent_source_of_counted anchored sound positive window ring preGloas honest start
      nonzero found advanced late recent above counted slotOk totalOk balanceOk thresholdOk weightOk
      passed (large middle counts bound) p (few middle total counts bound totalOk)

/-- Pulling up a held state retains historical sources and adds its current passing counts. -/
theorem Execution.pulledState_sent_sources {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {epoch : Epoch} {slot : Slot}
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (large : ∀ state : BeaconState preset fork,
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ epoch →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (few : ∀ (state : BeaconState preset fork) (total : Gwei),
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ epoch →
      getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat)
    {root : Root} {state pulled : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state)
    (bounded : getCurrentEpoch state ≤ epoch)
    (computed : processJustificationAndFinalization state = .ok pulled) :
    FinalizationSources (fun source target => ∃ v data, p v ∧ data.source = source ∧
      data.target.epoch = target ∧ ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m)
      (getCurrentEpoch anchorState) ((getCurrentEpoch state).toNat + 1) pulled := by
  have old := e.blockState_sent_sources anchored sound positive window ring preGloas honest start
    nonzero slotOk p large few stored bounded
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  have stateSound := ((reachable k).ordered sound).2 stored
  apply old.process_of_counts stateSound.ordered stateSound.settled ?_ computed
  intro late recent indices total balance threshold weight counted totalOk balanceOk thresholdOk
    weightOk passed above
  have counts := Store.counts_of_fixedChecks (config := config) (checks := checks) stored (.inl rfl)
  exact e.exists_sent_source_of_counted anchored sound positive window ring preGloas honest start
    nonzero stored (.inl rfl) late recent above counted slotOk totalOk balanceOk thresholdOk
    weightOk passed (large state counts bounded) p (few state total counts bounded totalOk)

private theorem exists_member_of_target_count {state : BeaconState preset fork}
    {indices : List ValidatorIndex} {total balance threshold weight : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state indices = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (quorum : ∀ v ∈ indices, v ∈ quorumVoters state)
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat) :
    ∃ v ∈ indices, p v := by
  classical
  by_contra missing
  have subset : indices.toFinset ⊆ {v ∈ quorumVoters state | ¬p v} := by
    intro v member
    have member := List.mem_toFinset.mp member
    exact Finset.mem_filter.mpr ⟨quorum v member, fun good => missing ⟨v, member, good⟩⟩
  have bounded := stake_mono (w := fun v => balanceAt state v.toNat) subset
  have tested := (justificationTest_iff_stake (getTotalActiveBalance_ok totalOk)
    balanceOk thresholdOk weightOk large).mp passed
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  have floor : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun v => balanceAt state v.toNat) (activeVoters state) := by omega
  change total.toNat = max _ (stake (fun v => balanceAt state v.toNat) (activeVoters state))
    at totalEq
  rw [Nat.max_eq_right floor] at totalEq
  change 2 * stake (fun v => balanceAt state v.toNat) (activeVoters state) ≤ _ at tested
  omega

/-- A changed target retains the successful count, without a claim about its source. -/
private theorem target_count_of_process {state after : BeaconState preset fork}
    {P : Checkpoint → Prop} (old : P state.currentJustifiedCheckpoint)
    (counts : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ (recent : Bool) (indices : List ValidatorIndex) (total balance threshold weight : Gwei),
      ((∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations = .ok indices) →
      getTotalActiveBalance state = .ok total → getTotalBalance state indices = .ok balance →
      mulChecked total 2 = .ok threshold → mulChecked balance 3 = .ok weight →
      threshold ≤ weight → ∀ checkpoint,
      checkpoint.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root → P checkpoint)
    (computed : processJustificationAndFinalization state = .ok after) :
    P after.currentJustifiedCheckpoint := by
  have weighed : ∀ (previous current : List ValidatorIndex) total previousBalance currentBalance,
      (¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) →
      (∀ recent : Bool, (∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) =
            .ok (if recent then current else previous)) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations =
            .ok (if recent then current else previous)) →
      getTotalActiveBalance state = .ok total →
      getTotalBalance state previous = .ok previousBalance →
      getTotalBalance state current = .ok currentBalance →
      weighJustificationAndFinalization state total previousBalance currentBalance = .ok after →
      P after.currentJustifiedCheckpoint := by
    intro previous current total previousBalance currentBalance late counted totalOk previousOk
      currentOk run
    rcases weighJustificationAndFinalization_currentJustified run with
      ⟨same, -⟩ | ⟨recent, threshold, weight, thresholdOk, weightOk, passed, epoch, rootOk⟩
    · exact same ▸ old
    apply counts late recent _ _ _ _ _ (counted recent) totalOk ?_
      thresholdOk weightOk passed _ epoch rootOk
    cases recent <;> assumption
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · cases Except.ok.inj computed
      exact old
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, run⟩ := computed
    apply weighed previous current total previousBalance currentBalance late ?_
      totalOk previousBalanceOk currentBalanceOk run
    intro recent
    exact .inl ⟨altair, by cases recent <;> assumption⟩
  · rename_i notAltair
    split at computed
    · cases Except.ok.inj computed
      exact old
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩,
      currentBalance, ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, run⟩ := computed
    apply weighed previousIndices currentIndices total previousBalance currentBalance late ?_
      totalOk previousBalanceOk currentBalanceOk run
    intro recent
    cases recent
    · exact .inr ⟨Nat.lt_of_not_le notAltair, previous, previousOk, previousIndicesOk⟩
    · exact .inr ⟨Nat.lt_of_not_le notAltair, current, currentOk, currentIndicesOk⟩

private theorem target_count_of_cached {state cached after : BeaconState preset fork}
    {P : Checkpoint → Prop}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (cachedOk : processSlot state = .ok cached)
    (old : P state.currentJustifiedCheckpoint)
    (counts : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ (recent : Bool) (indices : List ValidatorIndex) (total balance threshold weight : Gwei),
      ((∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations = .ok indices) →
      getTotalActiveBalance state = .ok total → getTotalBalance state indices = .ok balance →
      mulChecked total 2 = .ok threshold → mulChecked balance 3 = .ok weight →
      threshold ≤ weight → ∀ checkpoint,
      checkpoint.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root → P checkpoint)
    (computed : processJustificationAndFinalization cached = .ok after) :
    P after.currentJustifiedCheckpoint := by
  obtain ⟨current, previous, total, balance, -, -, -⟩ := processSlot_countingBalances cachedOk
  apply target_count_of_process ((frame_processSlot cachedOk).currentJustified.symm ▸ old)
    ?_ computed
  intro late recent indices totalValue balanceValue threshold weight counted totalOk balanceOk
    thresholdOk weightOk passed checkpoint epoch rootOk
  rw [current] at late
  rw [total] at totalOk
  rw [balance] at balanceOk
  rw [current, previous] at epoch
  have recentEpoch : checkpoint.epoch = getCurrentEpoch state ∨
      checkpoint.epoch = getPreviousEpoch state := by
    cases recent
    · exact .inr epoch
    · exact .inl epoch
  rw [getBlockRoot_processSlot cachedOk
    (slot_lt_epoch_add_historical positive window recentEpoch)] at rootOk
  apply counts late recent indices totalValue balanceValue threshold weight ?_
    totalOk balanceOk thresholdOk weightOk passed checkpoint epoch rootOk
  rcases counted with ⟨altair, indicesOk⟩ | ⟨before, attestations, matching, indicesOk⟩
  · left
    refine ⟨altair, ?_⟩
    rw [current, previous, processSlot_participatingIndices cachedOk] at indicesOk
    exact indicesOk
  · right
    refine ⟨before, attestations, ?_, ?_⟩
    · rw [current, previous] at matching
      rw [processSlot_matchingTargetAttestations positive window cachedOk before
        (by cases recent <;> simp)] at matching
      exact matching
    · rwa [processSlot_unslashedAttestingIndices cachedOk] at indicesOk

private theorem target_property_advanceSlots {P : Checkpoint → Prop}
    {state after : BeaconState preset fork} {count : Nat}
    (old : P state.currentJustifiedCheckpoint)
    (counts : ∀ n, n < count → ∀ middle cached justified,
      advanceSlots config checks n state = .ok middle → processSlot middle = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      P middle.currentJustifiedCheckpoint → P justified.currentJustifiedCheckpoint)
    (computed : advanceSlots config checks count state = .ok after) :
    P after.currentJustifiedCheckpoint := by
  induction count generalizing state after with
  | zero =>
    cases Except.ok.inj computed
    exact old
  | succ count ih =>
    simp only [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, step, rest⟩ := computed
    have nextHolds : P next.currentJustifiedCheckpoint := by
      obtain ⟨slot, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok step
      change P epoched.currentJustifiedCheckpoint
      unfold epochIfLast at epochedOk
      split at epochedOk
      · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
        rw [frame.toFrame.currentJustified]
        exact counts 0 (by omega) state cached justified rfl cachedOk justifiedOk old
      · cases Except.ok.inj epochedOk
        exact (frame_processSlot cachedOk).currentJustified.symm ▸ old
    apply ih nextHolds (fun n bound middle cached justified ran cachedOk justifiedOk prior => ?_)
      rest
    apply counts (n + 1) (by omega) middle cached justified ?_ cachedOk justifiedOk prior
    simp only [EthLib.Consensus.advanceSlots, step, bind, Except.bind]
    exact ran

private theorem target_property_processSlots {P : Checkpoint → Prop}
    {state after : BeaconState preset fork} {slot : Slot}
    (old : P state.currentJustifiedCheckpoint)
    (counts : ∀ middle cached justified,
      (middle = state ∨ processSlots config checks state middle.slot = .ok middle) →
      middle.slot < slot → processSlot middle = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      P middle.currentJustifiedCheckpoint → P justified.currentJustifiedCheckpoint)
    (computed : processSlots config checks state slot = .ok after) :
    P after.currentJustifiedCheckpoint := by
  simp only [EthLib.Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, later, run⟩ := computed
  apply target_property_advanceSlots old ?_ run
  intro n bound middle cached justified ran cachedOk justifiedOk prior
  have atSlot := advanceSlots_slot n ran
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  have before : middle.slot < slot := by
    rw [UInt64.lt_iff_toNat_lt]
    omega
  apply counts middle cached justified ?_ before cachedOk justifiedOk prior
  by_cases zero : n = 0
  · subst n
    exact .inl (Except.ok.inj ran).symm
  · right
    have afterStart : state.slot < middle.slot := by
      rw [UInt64.lt_iff_toNat_lt]
      omega
    simp only [EthLib.Consensus.processSlots, bind_ok_iff, ensure_ok_iff]
    refine ⟨(), afterStart, ?_⟩
    have distance : middle.slot.toNat - state.slot.toNat = n := by omega
    rw [distance]
    exact ran

private theorem blockState_target_property {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {P : Checkpoint → Prop} (anchor : P anchorState.currentJustifiedCheckpoint)
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks sources.engine parent signed true = .ok state)
    (counts : ∀ (root childRoot : Root) (base middle cached justified : BeaconState preset fork)
      (child : BeaconBlock preset fork), store.blockStates[root]? = some base →
      store.blocks[childRoot]? = some child → child.parentRoot = root →
      (middle = base ∨ processSlots config checks base middle.slot = .ok middle) →
      middle.slot < child.slot → processSlot middle = .ok cached →
      processJustificationAndFinalization cached = .ok justified →
      P middle.currentJustifiedCheckpoint → P justified.currentJustifiedCheckpoint)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) : P state.currentJustifiedCheckpoint := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same]
    exact anchor
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      transitions root block state found stored same
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transitioned
    have parentHolds := blockState_target_property reachable anchor transitions counts parentFound
    rw [(frame_processBlock blockOk).currentJustified]
    apply target_property_processSlots parentHolds ?_ slotsOk
    intro middle cached justified visited before cachedOk justifiedOk old
    exact counts block.parentRoot root parent middle cached justified block parentFound found rfl
      visited (by simpa only [message] using before) cachedOk justifiedOk old
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- Historical targets use uncached counting states in the target's two-epoch window. -/
private theorem blockState_target_counts {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {P : Checkpoint → Prop} (anchor : P anchorState.currentJustifiedCheckpoint)
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks sources.engine parent signed true = .ok state)
    (counts : ∀ (root : Root) (base state : BeaconState preset fork),
      store.blockStates[root]? = some base →
      (state = base ∨ ∃ (slot : Slot) (childRoot : Root) (child : BeaconBlock preset fork),
        store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state) →
      store.Counts config state → ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ (recent : Bool) (indices : List ValidatorIndex) (total balance threshold weight : Gwei),
      ((∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations = .ok indices) →
      getTotalActiveBalance state = .ok total → getTotalBalance state indices = .ok balance →
      mulChecked total 2 = .ok threshold → mulChecked balance 3 = .ok weight →
      threshold ≤ weight → ∀ checkpoint,
      checkpoint.epoch.toNat ≤ (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ checkpoint.epoch.toNat + 1 →
      checkpoint.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root → P checkpoint)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) : P state.currentJustifiedCheckpoint := by
  apply blockState_target_property reachable anchor transitions ?_ stored
  intro root childRoot base middle cached justified child found held parent visited before
    cachedOk justifiedOk old
  have advanced : middle = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), store.blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok middle := by
    rcases visited with same | processed
    · exact .inl same
    · exact .inr ⟨middle.slot, childRoot, child, held, parent, UInt64.le_of_lt before, processed⟩
  apply target_count_of_cached positive window cachedOk old ?_ justifiedOk
  intro late recent indices total balance threshold weight counted totalOk balanceOk thresholdOk
    weightOk passed checkpoint epoch rootOk
  apply counts root base middle found advanced (Store.counts_of_fixedChecks found advanced)
    late recent indices total balance threshold weight counted totalOk balanceOk thresholdOk
    weightOk passed checkpoint ?_ ?_ epoch rootOk
  · cases recent
    · simp only [Bool.false_eq_true, ↓reduceIte] at epoch
      rw [epoch, getPreviousEpoch_toNat]
      omega
    · simp only [↓reduceIte] at epoch
      rw [epoch]
  · cases recent
    · simp only [Bool.false_eq_true, ↓reduceIte] at epoch
      rw [epoch, getPreviousEpoch_toNat]
      omega
    · simp only [↓reduceIte] at epoch
      rw [epoch]
      omega

private def TargetProperties (P : Checkpoint → Prop) (store : Store preset fork) : Prop :=
  P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
    ∀ (root : Root) checkpoint,
      store.unrealizedJustifications[root]? = some checkpoint → P checkpoint

private theorem target_properties_update {store : Store preset fork} {P : Checkpoint → Prop}
    {j f : Checkpoint} (old : TargetProperties P store) (proposed : P j) :
    TargetProperties P (store.updateCheckpoints j f) := by
  have realized := old.1
  unfold Store.updateCheckpoints
  split <;> dsimp only <;> split <;> exact ⟨by assumption, old.2⟩

private theorem target_properties_pull {store after : Store preset fork} {root : Root}
    {P : Checkpoint → Prop} (old : TargetProperties P store)
    (counts : ∀ state pulled, store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.currentJustifiedCheckpoint)
    (computed : store.computePulledUpTip config root = .ok after) :
    TargetProperties P after := by
  have update : ∀ (s : Store preset fork) j f,
      TargetProperties P s → P j → TargetProperties P (s.updateUnrealizedCheckpoints j f) := by
    intro s j f holds new
    have pending := holds.2.1
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨holds.1, by assumption, holds.2.2⟩
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, -, epoch, -, computed⟩ := computed
  have new := counts state pulled (Store.blockState_ok_iff.mp found)
    (mapError_ok_iff.mp processed)
  have inserted : TargetProperties P
      { store with unrealizedJustifications :=
          store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint } := by
    refine ⟨old.1, old.2.1, ?_⟩
    intro key checkpoint entry
    rw [getElem?_insert_root] at entry
    split at entry
    · cases Option.some.inj entry
      exact new
    · exact old.2.2 key checkpoint entry
  have preserved := update _ pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
    inserted new
  split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
    subst after
  · exact target_properties_update preserved new
  · exact preserved

private theorem target_properties_block {store after : Store preset fork}
    {signatureChecks : SignatureChecks} {blockSources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {P : Checkpoint → Prop}
    (old : TargetProperties P store)
    (states : ∀ (root : Root) (state : BeaconState preset fork),
      after.blockStates[root]? = some state →
      P state.currentJustifiedCheckpoint)
    (counts : ∀ (root : Root) (state pulled : BeaconState preset fork),
      after.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.currentJustifiedCheckpoint)
    (added : store.onBlock config signatureChecks blockSources signed = .ok after) :
    TargetProperties P after := by
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact old
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedFields : TargetProperties P recorded := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact old
      · cases record
        exact old
    have boostedFields : TargetProperties P boosted := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedFields
    have kept := (Store.computePulledUpTip_frame added).2.2.1
    have newFound : after.blockStates[blockRoot]? = some state := by
      rw [kept, Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
      simp
    exact target_properties_pull
      (target_properties_update boostedFields (states blockRoot state newFound))
      (fun s p found processed => counts blockRoot s p (kept.symm ▸ found) processed) added

private theorem target_properties_tickSlot {store after : Store preset fork} {time : UInt64}
    {P : Checkpoint → Prop} (old : TargetProperties P store)
    (ticked : store.onTickPerSlot config time = .ok after) : TargetProperties P after := by
  unfold Store.onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    obtain ⟨offset, -, ticked⟩ := ticked <;>
    split at ticked <;>
    simp only [pure, Except.pure, Except.ok.injEq] at ticked <;> subst after
  · exact target_properties_update old old.2.1
  · exact old
  · exact target_properties_update old old.2.1
  · exact old

private theorem target_properties_catchUp {store after : Store preset fork} {slot : Slot}
    {P : Checkpoint → Prop} (old : TargetProperties P store)
    (caught : Store.catchUp config store slot = .ok after) : TargetProperties P after := by
  induction store using Store.catchUp.induct config slot with
  | _ store ih =>
    rw [Store.catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTime, -, ticked, tick, caught⟩ := caught
      split at caught
      · exact ih ticked ‹_› (target_properties_tickSlot old tick) caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst after
      exact old

private theorem target_properties_tick {store after : Store preset fork} {time : UInt64}
    {P : Checkpoint → Prop} (old : TargetProperties P store)
    (ticked : store.onTick config time = .ok after) : TargetProperties P after := by
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, -, caught, catchUp, ticked⟩ := ticked
  exact target_properties_tickSlot (target_properties_catchUp old catchUp) ticked

private theorem target_properties_reachable {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (before : fork < .glamsterdam) {P : Checkpoint → Prop}
    (anchor : ∀ checkpoint, checkpoint.epoch = getCurrentEpoch anchorState → P checkpoint)
    (states : ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state →
      P state.currentJustifiedCheckpoint)
    (counts : ∀ (root : Root) (state pulled : BeaconState preset fork),
      store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled →
      P pulled.currentJustifiedCheckpoint) :
    TargetProperties P store := by
  induction reachable with
  | anchor made =>
    unfold getForkchoiceStore at made
    simp only [bind_ok_iff] at made
    obtain ⟨stateRoot, _, made⟩ := made
    split at made
    · cases made
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
      obtain ⟨root, _, time, _, rfl⟩ := made
      refine ⟨anchor _ rfl, anchor _ rfl, ?_⟩
      intro key checkpoint entry
      rw [getElem?_insert_root] at entry
      split at entry
      · cases Option.some.inj entry
        exact anchor _ rfl
      · simp at entry
  | tick prior ticked ih =>
    have kept := (Store.onTick_frame ticked).2.2.2
    exact target_properties_tick
      (ih (fun r s h => states r s (kept.symm ▸ h))
        (fun r s p h run => counts r s p (kept.symm ▸ h) run)) ticked
  | @block prior after signatureChecks blockSources signed reachable added ih =>
    have kept : ∀ (root : Root) (state : BeaconState preset fork),
        prior.blockStates[root]? = some state →
        after.blockStates[root]? = some state := by
      intro root state found
      rcases Store.onBlock_same_or_insert added with same |
        ⟨newRoot, -, fresh, -, -, post, -, -, mapped⟩
      · exact same ▸ found
      have other : newRoot ≠ root := by
        rintro rfl
        rw [reachable.blockState_eq_none fresh] at found
        cases found
      rw [mapped, getElem?_insert_root]
      simpa only [other, ↓reduceIte] using found
    exact target_properties_block
      (ih (fun r s h => states r s (kept r s h))
        (fun r s p h run => counts r s p (kept r s h) run)) states counts added
  | attestation prior attested ih =>
    have kept := (Store.onAttestation_frame attested).2.2.1
    have old := ih (fun r s h => states r s (kept.symm ▸ h))
      (fun r s p h run => counts r s p (kept.symm ▸ h) run)
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
    have storedHolds : TargetProperties P stored := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · simp only [pure, Except.pure, Except.ok.injEq] at storing
        exact storing ▸ old
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
        obtain ⟨_, _, rfl⟩ := storing
        exact old
    split at attested
    · cases Except.ok.inj attested
      exact storedHolds
    · cases attested
  | attesterSlashing prior slashed ih =>
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact ih states counts
  | payloadAttestation => exact False.elim (Nat.not_le_of_lt before ‹.glamsterdam ≤ fork›)
  | envelope => exact False.elim (Nat.not_le_of_lt before ‹.glamsterdam ≤ fork›)
  | inclusionList =>
    exact False.elim (Nat.not_le_of_lt before
      (Nat.le_trans (by decide : Fork.glamsterdam ≤ Fork.hegota) ‹.hegota ≤ fork›))

private theorem signsTarget_of_count {state : BeaconState preset fork} {k : Nat}
    {checkpoint : Checkpoint} {slot : Slot} {recent : Bool}
    {indices : List ValidatorIndex} {total balance threshold weight : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state indices = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : 3 * stake (fun v => balanceAt state v.toNat)
      {v ∈ quorumVoters state | ¬p v} < 2 * total.toNat)
    (epoch : checkpoint.epoch =
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (rootOk : getBlockRoot state checkpoint.epoch = .ok checkpoint.root)
    (provenance : ∀ v ∈ indices, v ∈ quorumVoters state ∧ ∃ data,
      data.target.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      getBlockRoot state data.target.epoch = .ok data.target.root ∧
      ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot) :
    ∃ v, p v ∧ SignsTargetBefore e v checkpoint slot (e.world k).time := by
  obtain ⟨v, member, good⟩ := exists_member_of_target_count totalOk balanceOk thresholdOk
    weightOk passed large (fun v member => (provenance v member).1) p few
  obtain ⟨-, data, targetEpoch, targetRoot, m, sent, statement, before⟩ := provenance v member
  have sameEpoch : data.target.epoch = checkpoint.epoch := targetEpoch.trans epoch.symm
  rw [sameEpoch, rootOk, Except.ok.injEq] at targetRoot
  have same : data.target = checkpoint := by
    cases h : data.target
    cases checkpoint
    simp_all
  exact ⟨v, good, k, le_rfl, m, sent, data, statement, same, before⟩

theorem justified_target_property {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (before : fork < .glamsterdam) {P : Checkpoint → Prop}
    (anchor : ∀ checkpoint, checkpoint.epoch ≤ getCurrentEpoch anchorState → P checkpoint)
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks sources.engine parent signed true = .ok state)
    (counts : ∀ (root : Root) (base state : BeaconState preset fork),
      store.blockStates[root]? = some base →
      (state = base ∨ ∃ (slot : Slot) (childRoot : Root) (child : BeaconBlock preset fork),
        store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state) →
      store.Counts config state → ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ (recent : Bool) (indices : List ValidatorIndex) (total balance threshold weight : Gwei),
      ((∃ altair : .altair ≤ fork,
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
        ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
          getMatchingTargetAttestations state before
            (if recent then getCurrentEpoch state else getPreviousEpoch state) =
              .ok attestations ∧
          getUnslashedAttestingIndices state attestations = .ok indices) →
      getTotalActiveBalance state = .ok total → getTotalBalance state indices = .ok balance →
      mulChecked total 2 = .ok threshold → mulChecked balance 3 = .ok weight →
      threshold ≤ weight → ∀ checkpoint,
      checkpoint.epoch.toNat ≤ (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ checkpoint.epoch.toNat + 1 →
      checkpoint.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root → P checkpoint)
    {checkpoint : Checkpoint} (justified : store.Justified checkpoint) : P checkpoint := by
  have states : ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state → P state.currentJustifiedCheckpoint := by
    intro root state found
    exact blockState_target_counts reachable positive window
      (anchor _ (UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState)))
      transitions counts found
  have pulled : ∀ (root : Root) (state after : BeaconState preset fork),
      store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok after →
      P after.currentJustifiedCheckpoint := by
    intro root state after found processed
    apply target_count_of_process (states root state found) ?_ processed
    intro late recent indices total balance threshold weight counted totalOk balanceOk thresholdOk
      weightOk passed checkpoint epoch rootOk
    apply counts root state state found (.inl rfl)
      (Store.counts_of_fixedChecks (checks := checks) found (.inl rfl))
      late recent indices total balance threshold weight counted totalOk balanceOk thresholdOk
      weightOk passed checkpoint ?_ ?_ epoch rootOk
    · cases recent
      · simp only [Bool.false_eq_true, ↓reduceIte] at epoch
        rw [epoch, getPreviousEpoch_toNat]
        omega
      · simp only [↓reduceIte] at epoch
        rw [epoch]
    · cases recent
      · simp only [Bool.false_eq_true, ↓reduceIte] at epoch
        rw [epoch, getPreviousEpoch_toNat]
        omega
      · simp only [↓reduceIte] at epoch
        rw [epoch]
        omega
  have properties := target_properties_reachable reachable before
    (fun checkpoint same => anchor checkpoint (UInt64.le_of_eq same)) states pulled
  rcases justified with same | same | ⟨-, ⟨root, state, found, same⟩ | ⟨root, found⟩⟩
  · exact same ▸ properties.1
  · exact same ▸ properties.2.1
  · exact same ▸ states root state found
  · exact properties.2.2 root checkpoint found

/-- The count: a set of validators signs a justified checkpoint when the others cannot.

The checkpoint is one that an honest store counts as justified, after the epoch of its anchor.

The store starts as the store of the anchor.

No checkpoint of the state of the anchor is of a later epoch than that state.

A state of the store counts the votes for it, in its epoch or the one after.

It is the state of a block of the store, maybe at a later slot, as `Store.Counts` says.

In each such state, take the validators outside the set whose votes can count.

They hold less than two thirds of the active balance.

The active stake exceeds one and a half balance increments in each counting state.

This excludes a passing justification test caused by the minimum balance of an empty vote set.

Then a validator of the set signs a vote with the checkpoint as its target.

The vote is of a slot before the current slot of the store.

A block holds only votes of earlier slots, and a store takes no block of a later slot.

The proof is new, and has three parts.

A justified checkpoint of a store comes from the count of a state of one of its blocks.

Each counted vote is in a block of the chain of that state.

The store has read each vote of each of its blocks.

A block reaches the store in a sent message, so its votes are sent by the time of the store.

It uses the agreement of the committees of the state of a block with those of the target state.

The RANDAO ring must retain the seed through the epoch after the target.

Epochs have a positive length, and block-root history covers two epochs.

This keeps the target root from being overwritten before its participation is counted.

Each held block has a nonzero state root, so slot processing fills its header only once.

A zero state root is an explicit exceptional case for the caller, not excluded by hash injectivity.

Inherited anchor participation targets only epochs at or below the anchor, which are excluded.

In [verified-fast-confirmation][vfc], `IncludedSupermajorityLink` holds the signers of a count.

There `one_third_honest_intersects_two_thirds` and `two_quorums_intersect_honest` intersect them.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.exists_signsTarget_of_justified {anchor : Store preset fork}
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
    {checkpoint : Checkpoint} {slot : Slot}
    (justified : ((e.world k).state w).Justified checkpoint)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (after : anchor.justifiedCheckpoint.epoch < checkpoint.epoch)
    (large : ∀ state : BeaconState preset fork,
      ((e.world k).state w).Counts config state →
      checkpoint.epoch.toNat ≤ (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ checkpoint.epoch.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : ∀ (state : BeaconState preset fork) (total : Gwei),
      ((e.world k).state w).Counts config state →
      checkpoint.epoch.toNat ≤ (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ checkpoint.epoch.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat) :
    ∃ v, p v ∧ SignsTargetBefore e v checkpoint slot (e.world k).time := by
  have reachable : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
    intro n
    induction n with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start w)
      rw [start]
      exact .anchor anchored
    | succ n ih =>
      rcases e.state_succ n w with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  obtain ⟨anchorRoot, -, -, -, anchorCheckpoint, -⟩ := getForkchoiceStore_anchor anchored
  have later : getCurrentEpoch anchorState < checkpoint.epoch := by
    simpa only [anchorCheckpoint] using after
  -- Track only the requested checkpoint, so stake bounds are needed only in its own window.
  let P := fun target : Checkpoint => target = checkpoint →
    ∃ v, p v ∧ SignsTargetBefore e v checkpoint slot (e.world k).time
  have holds : P checkpoint := by
    refine justified_target_property (checks := checks) (sources := sources)
      (reachable k) sound slotsPositive window preGloas
      (P := P) ?_ ?_ ?_ justified
    · intro target bound same
      subst target
      have strict := UInt64.lt_iff_toNat_lt.mp later
      have lower := UInt64.le_iff_toNat_le.mp bound
      omega
    · intro root block state held found other
      exact e.exists_transition_of_nonanchor_block anchored honest start held found other
    · intro root base state found advanced counts late recent indices total balance threshold weight
        counted totalOk balanceOk thresholdOk weightOk passed target lower upper epoch rootOk same
      subst target
      apply signsTarget_of_count totalOk balanceOk thresholdOk weightOk passed
        (large state counts lower upper) p (few state total counts lower upper totalOk)
        epoch rootOk
      intro v member
      exact e.exists_sent_target_of_counted anchored sound slotsPositive window ring preGloas
        honest start nonzero found advanced late recent (epoch ▸ later) counted member slotOk
  exact holds rfl

/-- Each justified checkpoint has an honest vote, from the bound in each counting state.

The bound counts Byzantine current-or-previous-epoch voters against the active denominator.

The threshold is in percent.

Take each state where an honest store can count votes, up to the epoch after the horizon.

The threshold is strictly below two thirds, and the denominator is positive.

No comparison with a reference state's balances is needed. -/
theorem Execution.justifiedByHonestVote [DecidablePred (· ∈ J)] {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (slotsPositive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {last : ℕ} (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
      ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch}
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ last →
      ((e.world k).state w).Counts config state →
      anchor.justifiedCheckpoint.epoch.toNat < (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    {threshold : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ last → ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200) :
    JustifiedByHonestVote e anchor.justifiedCheckpoint.epoch horizon last := by
  intro w honest k bounded checkpoint slot justified slotOk after inHorizon
  have afterNat := UInt64.lt_iff_toNat_lt.mp after
  have inside := UInt64.le_iff_toNat_le.mp inHorizon
  refine e.exists_signsTarget_of_justified anchored sound slotsPositive window ring preGloas
    honest (start w honest)
    (nonzero w honest k bounded) justified slotOk
    after (fun state counts lower upper =>
      large w honest k state bounded counts (by omega) (by omega))
    (· ∈ J) fun state total counts _ upper totalOk => ?_
  have bound := byzantine w honest k state total bounded counts (by omega) totalOk
  have lower := UInt64.le_iff_toNat_le.mp (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
  have pos := UInt64.lt_iff_toNat_lt.mp positive
  have strict := Nat.mul_lt_mul_of_pos_right enough (show 0 < total.toNat by omega)
  nlinarith

/-- An honest third signs each justified checkpoint of its epoch, with the drift as the margin.

The reference is the pulled-up state of a block of an honest store, where the rule counts.

Take each state where an honest store can count votes.

Its epoch is the current epoch of the first store or the one after.

It has drifted from the reference by at most the given drift.

No honest validator is slashed in a state where an honest store can count votes.

That number is the margin, and it covers two epochs of drift at most. -/
theorem Execution.honestThirdPins {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (slotsPositive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {last : ℕ} (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
      ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} {drift : ℕ}
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ last →
      ((e.world k).state w).Counts config state →
      anchor.justifiedCheckpoint.epoch.toNat < (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (drifts : ∀ u ∈ J, ∀ n head reference epoch, (e.world n).time ≤ last →
      ((e.world n).state u).getPulledUpHeadState config head = .ok reference →
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ last →
        ((e.world k).state w).Counts config state →
        epoch.toNat ≤ (getCurrentEpoch state).toNat →
        (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 →
        DriftAtMost reference state drift)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ last →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v) :
    HonestThirdPins e anchor.justifiedCheckpoint.epoch horizon drift last := by
  intro u caller n callerBound head reference total epoch voters referenceOk totalOk epochOk
    inHorizon good active third w honest k bounded checkpoint slot justified slotOk same after
  subst same
  have afterNat := UInt64.lt_iff_toNat_lt.mp after
  have inside := UInt64.le_iff_toNat_le.mp inHorizon
  obtain ⟨v, member, signs⟩ := e.exists_signsTarget_of_justified anchored sound slotsPositive window
    ring preGloas honest
    (start w honest) (nonzero w honest k bounded) justified slotOk after
      (fun state counts lower upper => large w honest k state bounded counts (by omega) (by omega))
      (· ∈ voters)
      fun state stateTotal counts lower upper stateTotalOk => by
    have split := Finset.sum_filter_add_sum_filter_not (activeVoters reference) (· ∈ voters)
      fun v => balanceAt reference v.toNat
    have same : ({v ∈ activeVoters reference | v ∈ voters} : Finset ValidatorIndex) = voters :=
      Finset.ext fun v => by
        simpa only [Finset.mem_filter, and_iff_right_iff_imp] using active v
    have covered := Store.stake_le_of_getTotalBalance (getTotalActiveBalance_ok totalOk)
      (W := activeVoters reference) fun v member => List.mem_toFinset.mp member
    rw [same] at split
    simp only [stake] at third covered ⊢
    exact (drifts u caller n head reference checkpoint.epoch callerBound referenceOk epochOk
      inHorizon w honest k state bounded counts lower upper).lt_two_mul_total (· ∈ voters)
      (fun v member => unslashed w honest k state bounded counts v (good v member))
      (by simp only [stake]; omega) stateTotalOk
  exact ⟨v, member, signs⟩

end Models.Network

end EthLib.Consensus
