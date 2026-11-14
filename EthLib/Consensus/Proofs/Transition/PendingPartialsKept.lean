module

public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: slots keep the queue of pending partial withdrawals

From Electra, the state holds a queue of pending partial withdrawals.

Only two steps of a block write it.

A withdrawal request appends an entry.

The withdrawals of the payload remove the entries they pay.

A slot caches the roots of the state and of the latest block.

The last slot of an epoch also runs the epoch transition.

No step of an epoch writes the queue.

So a run of slots keeps the queue, whatever the signature checks.

[EIP-7002] defines the partial withdrawal requests.

[EIP-7251] defines the queue of pending partial withdrawals.

[EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002#specification
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## The steps that keep the queue -/

/-- Two states hold the same queue of pending partial withdrawals, from Electra. -/
private def PartialsSame (state after : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork,
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra

private theorem PartialsSame.refl (state : BeaconState preset fork) : PartialsSame state state :=
  fun _ => rfl

private theorem PartialsSame.trans {first second third : BeaconState preset fork}
    (one : PartialsSame first second) (two : PartialsSame second third) :
    PartialsSame first third :=
  fun electra => (two electra).trans (one electra)

private theorem PartialsSame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → PartialsSame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : PartialsSame state after :=
  foldlM_ok_invariant (PartialsSame state)
    (fun _ _ _ before ok => before.trans (frame _ _ _ ok)) (PartialsSame.refl state) computed

/-- Setting a validator at a plain position keeps the queue. -/
private theorem partialsSame_setValidatorAt {position : Nat} {validator : Validator}
    (set : state.setValidatorAt position validator = .ok after) : PartialsSame state after := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact fun _ => rfl

/-- Setting a validator keeps the queue. -/
private theorem partialsSame_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : PartialsSame state after :=
  partialsSame_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

/-- Setting a balance keeps the queue. -/
private theorem partialsSame_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : PartialsSame state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact fun _ => rfl

/-- Raising a balance keeps the queue. -/
private theorem partialsSame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : PartialsSame state after :=
  let ⟨_, set⟩ := increaseBalance_ok computed
  partialsSame_setBalance set

/-- Lowering a balance keeps the queue. -/
private theorem partialsSame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : PartialsSame state after :=
  let ⟨_, set⟩ := decreaseBalance_ok computed
  partialsSame_setBalance set

/-- Starting the exit of a validator keeps the queue. -/
private theorem partialsSame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    PartialsSame state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact PartialsSame.refl _
  refine PartialsSame.trans ?_ (partialsSame_setValidator set)
  unfold exitQueue at queue
  split at queue
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := queue
    exact fun _ => rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, rfl, _⟩ := queue
    exact PartialsSame.refl _

/-- Adding a validator keeps the queue. -/
private theorem partialsSame_addValidatorToRegistry {pubkey withdrawalCredentials amount}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    PartialsSame state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact fun _ => rfl
  split at computed
  · cases computed
    exact fun _ => rfl
  · cases computed

/-- Keeping the queue satisfies the laws of the epoch steps. -/
private theorem partialsEpochFrameLaws : EpochFrameLaws (@PartialsSame preset fork) where
  refl := PartialsSame.refl
  trans := PartialsSame.trans
  setValidatorAt := fun set _ _ _ _ _ => partialsSame_setValidatorAt set
  increaseBalance := partialsSame_increaseBalance
  decreaseBalance := partialsSame_decreaseBalance
  initiateValidatorExit := partialsSame_initiateValidatorExit
  addValidatorToRegistry := fun computed _ => partialsSame_addValidatorToRegistry computed
  eth1DataVotes _ _ := fun _ => rfl
  inactivityScores _ _ := fun _ => rfl
  slashings _ _ := fun _ => rfl
  randaoMixes _ _ := fun _ => rfl
  historicalRoots _ _ := fun _ => rfl
  historicalSummaries _ _ := fun _ => rfl
  participationRecords _ := fun _ => rfl
  pendingDeposits _ _ _ := fun _ => rfl
  pendingConsolidations _ _ := fun _ => rfl
  syncCommittees _ _ _ := fun _ => rfl
  proposerLookahead _ _ := fun _ => rfl
  ptcWindow _ _ := fun _ => rfl

/-! ## The epoch transition and the slots -/

/-- Justification and finalization keep the queue. -/
private theorem partialsSame_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    PartialsSame state after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact PartialsSame.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact fun _ => by rw [← rest]

/-- The epoch transition keeps the queue. -/
private theorem partialsSame_processEpoch
    (computed : processEpoch config checks state = .ok after) : PartialsSame state after := by
  unfold processEpoch at computed
  split at computed
  · rename_i altair
    obtain ⟨pending, paid, rooted, pendingOk, paidOk, middle, tail⟩ :=
      partialsEpochFrameLaws.processEpochAltair_paymentSplit computed
    obtain ⟨justified, justifiedOk, head⟩ :=
      partialsEpochFrameLaws.epochBeforePayments_split pendingOk
    have paidSame : PartialsSame pending paid := by
      split at paidOk
      · rw [processBuilderPendingPayments_eq (liftAccessor_ok.mp paidOk)]
        exact fun _ => rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
        exact paidOk ▸ PartialsSame.refl _
    exact (partialsSame_processJustificationAndFinalization justifiedOk).trans <|
      head.trans <| paidSame.trans <| middle.trans <|
      (show PartialsSame rooted (processParticipationFlagUpdates rooted altair) from
        fun _ => rfl).trans tail
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  exact (partialsSame_processJustificationAndFinalization justifiedOk).trans <|
    (partialsEpochFrameLaws.processRewardsAndPenalties rewardedOk).trans <|
    (partialsEpochFrameLaws.processRegistryUpdates registeredOk).trans <|
    (partialsEpochFrameLaws.processSlashings slashedOk).trans <|
    (partialsEpochFrameLaws.processEth1DataReset resetOk).trans <|
    (partialsEpochFrameLaws.processEffectiveBalanceUpdates balancedOk).trans <|
    (partialsEpochFrameLaws.processSlashingsReset clearedOk).trans <|
    (partialsEpochFrameLaws.processRandaoMixesReset mixedOk).trans <|
    (partialsEpochFrameLaws.processHistoricalRootsUpdate rootedOk).trans <|
    partialsEpochFrameLaws.processParticipationRecordUpdates rotated

/-- One slot keeps the queue of pending partial withdrawals, whatever the signature checks. -/
theorem advanceSlot_pendingPartialWithdrawals (electra : .pectra ≤ fork)
    (computed : advanceSlot config checks state = .ok after) :
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact partialsSame_processEpoch epochedOk electra
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    rfl

/-- Advancing to a later slot keeps the queue of pending partial withdrawals.

This holds whatever the signature checks.

No block runs on the way, so only the slot caching and the epoch transitions act. -/
theorem processSlots_pendingPartialWithdrawals (electra : .pectra ≤ fork) {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra := by
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  generalize slot.toNat - state.slot.toNat = count at advanced
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at advanced
    subst advanced
    rfl
  | succ count step =>
    simp only [advanceSlots, bind_ok_iff] at advanced
    obtain ⟨next, nextOk, rest⟩ := advanced
    exact (step rest).trans (advanceSlot_pendingPartialWithdrawals electra nextOk)

end EthLib.Consensus
