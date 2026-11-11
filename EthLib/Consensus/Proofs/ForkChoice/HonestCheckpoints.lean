module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
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

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- A checkpoint that a store counts as justified.

It is the justified checkpoint of the store, realized or not, or that of a block of the store.

A block has the justified checkpoint of its state and its unrealized justification. -/
def Store.Justified (store : Store preset fork) (checkpoint : Checkpoint) : Prop :=
  checkpoint = store.justifiedCheckpoint ∨ checkpoint = store.unrealizedJustifiedCheckpoint ∨
    (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
      checkpoint = state.currentJustifiedCheckpoint) ∨
    ∃ root : Root, store.unrealizedJustifications[root]? = some checkpoint

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
theorem exists_linkVote_of_processJustification {state after : BeaconState preset fork}
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
theorem exists_sourceVote_of_weighJustification_bit_zero
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
    currentWeightOk, newCurrent, newPrevious, -, finalized⟩ :=
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
theorem exists_sourceVote_of_processJustification {state after : BeaconState preset fork}
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
theorem exists_readsAttestation_of_onBlockWithVotes {store after : Store preset fork}
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

That store finds the finalized block on the chain of the justified block, at the finalized epoch. -/
def FinalizedPrefix
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (horizon : Epoch) : Prop :=
  ∀ u ∈ J, ∀ w ∈ J, ∀ n k checkpoint, ((e.world k).state w).Justified checkpoint →
    ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
    checkpoint.epoch ≤ horizon →
    ((e.world k).state w).getCheckpointBlock checkpoint.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root

/-- Two justified checkpoints of honest stores at one epoch, up to a horizon, are the same. -/
def OneJustifiedPerEpoch
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (horizon : Epoch) : Prop :=
  ∀ u ∈ J, ∀ w ∈ J, ∀ n k first second, ((e.world n).state u).Justified first →
    ((e.world k).state w).Justified second → first.epoch = second.epoch →
    first.epoch ≤ horizon → first = second

/-- A validator signs a vote with a target, in a message sent along the execution. -/
def SignsTarget
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) : Prop :=
  ∃ k, ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target

/-- A validator signs a vote with a target, of a slot before a given one. -/
def SignsTargetBefore
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) (slot : Slot) : Prop :=
  ∃ k, ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target ∧
      data.slot < slot

/-- A vote of a slot before a given one is a vote. -/
theorem SignsTargetBefore.signsTarget
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} {v : ValidatorIndex} {target : Checkpoint} {slot : Slot}
    (signs : SignsTargetBefore e v target slot) : SignsTarget e v target :=
  let ⟨k, m, sent, data, member, same, _⟩ := signs
  ⟨k, m, sent, data, member, same⟩

/-- Each justified checkpoint of an honest store after the anchor has an honest vote.

The checkpoint is at a later epoch than the given one, the epoch of the anchor.

Its epoch is at most the horizon.

An honest validator signs a vote with the checkpoint as its target.

The vote is of a slot before the current slot of the store. -/
def JustifiedByHonestVote
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (anchorEpoch horizon : Epoch) : Prop :=
  ∀ u ∈ J, ∀ n checkpoint slot, ((e.world n).state u).Justified checkpoint →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    anchorEpoch < checkpoint.epoch → checkpoint.epoch ≤ horizon →
    ∃ v ∈ J, SignsTargetBefore e v checkpoint slot

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

No voter has to sign a target here: the definition only counts stake. -/
def HonestThirdPins
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (anchorEpoch horizon : Epoch) (margin : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n head state total epoch, ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    epoch ≤ horizon →
    (∀ v ∈ voters, v ∈ J) → (∀ v ∈ voters, v ∈ activeVoters state) →
    total.toNat + margin < 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k checkpoint slot, ((e.world k).state w).Justified checkpoint →
      ((e.world k).state w).getCurrentSlot config = .ok slot →
      checkpoint.epoch = epoch → anchorEpoch < epoch →
      ∃ v ∈ voters, SignsTargetBefore e v checkpoint slot

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

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
        exact maps ih.2 (Store.onAttesterSlashing_frame handled).2.2
          (Store.onAttesterSlashing_checkpointStates_latestMessages handled).1
      | block _ handled =>
        unfold Store.onBlockWithVotes at handled
        simp only [bind_ok_iff, ← Array.foldlM_toList] at handled
        obtain ⟨blocked, blockOk, voted, votedOk, slashedOk⟩ := handled
        have votedOrigin := foldStep _ _ Origin (fun _ _ _ _ holds step =>
          attestationStep holds step) blocked voted (blockStep ih.1 ih.2 blockOk) votedOk
        exact foldStep _ _ Origin (fun _ _ _ _ holds step =>
          maps holds (Store.onAttesterSlashing_frame step).2.2
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

/-- A vote decoded before an accepted block occurs in a sent message with the same data.

The target root must match the block-root history of the state that decodes the vote.

The message and committee provenance proof is unfinished. -/
theorem Execution.exists_sent_of_blockVote {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
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
  sorry

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

/-- A counted index for an epoch after the anchor has a sent vote for the complete link.

The counting state uses the execution's checks.

The recent epoch restriction excludes inherited anchor participation.

It does not assert a provenance invariant for that participation.

The participation and message provenance proof is unfinished. -/
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
      LinkVote state recent v.toNat (v, data) ∧
      ∃ m ∈ (e.world k).sent,
        (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot := by
  sorry

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
    ∃ v, p v ∧ SignsTargetBefore e v checkpoint slot := by
  sorry

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
    (nonzero : ∀ w ∈ J, ∀ k (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch}
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state →
      anchor.justifiedCheckpoint.epoch.toNat < (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    {threshold : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200) :
    JustifiedByHonestVote e anchor.justifiedCheckpoint.epoch horizon := by
  intro w honest k checkpoint slot justified slotOk after inHorizon
  have afterNat := UInt64.lt_iff_toNat_lt.mp after
  have inside := UInt64.le_iff_toNat_le.mp inHorizon
  refine e.exists_signsTarget_of_justified anchored sound slotsPositive window ring preGloas
    honest (start w honest)
    (nonzero w honest k) justified slotOk
    after (fun state counts lower upper =>
      large w honest k state counts (by omega) (by omega))
    (· ∈ J) fun state total counts _ upper totalOk => ?_
  have bound := byzantine w honest k state total counts (by omega) totalOk
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
    (nonzero : ∀ w ∈ J, ∀ k (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} {drift : ℕ}
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state →
      anchor.justifiedCheckpoint.epoch.toNat < (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (drifts : ∀ u ∈ J, ∀ n head reference epoch,
      ((e.world n).state u).getPulledUpHeadState config head = .ok reference →
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
        ((e.world k).state w).Counts config state →
        epoch.toNat ≤ (getCurrentEpoch state).toNat →
        (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 →
        DriftAtMost reference state drift)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v) :
    HonestThirdPins e anchor.justifiedCheckpoint.epoch horizon drift := by
  intro u caller n head reference total epoch voters referenceOk totalOk epochOk inHorizon good active third w
    honest k checkpoint slot justified slotOk same after
  subst same
  have afterNat := UInt64.lt_iff_toNat_lt.mp after
  have inside := UInt64.le_iff_toNat_le.mp inHorizon
  obtain ⟨v, member, signs⟩ := e.exists_signsTarget_of_justified anchored sound slotsPositive window
    ring preGloas honest
    (start w honest) (nonzero w honest k) justified slotOk after
      (fun state counts lower upper => large w honest k state counts (by omega) (by omega))
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
    exact (drifts u caller n head reference checkpoint.epoch referenceOk epochOk inHorizon w honest k
      state counts lower upper).lt_two_mul_total (· ∈ voters)
      (fun v member => unslashed w honest k state counts v (good v member))
      (by simp only [stake]; omega) stateTotalOk
  exact ⟨v, member, signs⟩

end Models.Network

end EthLib.Consensus
