module

public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochPending

/-!
# Proofs: the pending deposits of an epoch

The pending deposits of an epoch keep one balance for each validator.

The queue never grows.

A pass never credits more inside the churn than the churn available.

The churn that a pass uses grows by the amounts of the deposits it reads that take churn.

A pass reads a prefix of the queue, applies some of it in order, and postpones the others.

So the queue splits into the deposits added to the balances, those dropped, and the queue after.

A pass postpones exactly the deposits it reads whose validator exits and is not withdrawn.

That needs the registry and the limit per epoch to fit together in 64 bits.

The validators it tests are those at the start of the pass.

The balances plus the amounts in the queue never rise.

A pass that leaves deposits unread stops at its stop condition, the limit per epoch or the churn.

Only a pass that stops at the churn records that it reached the churn.

If it does, the churn that the pass did not use carries over to the next epoch, and else none does.

The pass of an epoch reads only deposits with a slot at most the first slot of the finalized epoch.

In Electra, while deposits of the old mechanism remain, it reads no request either.

So only such deposits leave the queue.

From Gloas, the churn of deposits is the churn of activations alone.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The credits and postponements of a consumed prefix, in queue order.

The amount `charged` counts only deposits to targets that are neither withdrawn nor exiting.

Each target status is read from the state at that deposit, not the initial state.

EIP-7251, Consensus layer, introduces the balance-based pending-deposit queue.

The stop predicate must be false before any credit or postponement. -/
inductive PendingDepositTrace (config : Config) (checks : SignatureChecks)
    (stop : PendingDeposit → Bool) (nextEpoch : Epoch) :
    BeaconState preset fork → List PendingDeposit → BeaconState preset fork →
      Array PendingDeposit → Nat → Prop where
  | nil (state : BeaconState preset fork) :
      PendingDepositTrace config checks stop nextEpoch state [] state #[] 0
  | withdrawn {state credited after deposit rest postponed charged}
      (ready : stop deposit = false)
      (withdrawn : (depositTargetStatus state nextEpoch deposit.pubkey).2 = true)
      (applied : applyPendingDeposit config checks state deposit = .ok credited)
      (tail : PendingDepositTrace config checks stop nextEpoch credited rest after
        postponed charged) :
      PendingDepositTrace config checks stop nextEpoch state (deposit :: rest) after
        postponed charged
  | exiting {state after deposit rest postponed charged}
      (ready : stop deposit = false)
      (withdrawn : (depositTargetStatus state nextEpoch deposit.pubkey).2 = false)
      (exited : (depositTargetStatus state nextEpoch deposit.pubkey).1 = true)
      (tail : PendingDepositTrace config checks stop nextEpoch state rest after
        postponed charged) :
      PendingDepositTrace config checks stop nextEpoch state (deposit :: rest) after
        (#[deposit] ++ postponed) charged
  | charged {state credited after deposit rest postponed amount}
      (ready : stop deposit = false)
      (withdrawn : (depositTargetStatus state nextEpoch deposit.pubkey).2 = false)
      (exited : (depositTargetStatus state nextEpoch deposit.pubkey).1 = false)
      (applied : applyPendingDeposit config checks state deposit = .ok credited)
      (tail : PendingDepositTrace config checks stop nextEpoch credited rest after
        postponed amount) :
      PendingDepositTrace config checks stop nextEpoch state (deposit :: rest) after
        postponed (deposit.amount.toNat + amount)

/-- Every consumed entry passes the stop predicate, including withdrawn and exiting targets. -/
theorem PendingDepositTrace.ready {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {deposits : List PendingDeposit} {postponed : Array PendingDeposit} {charged : Nat}
    (trace : PendingDepositTrace config checks stop nextEpoch state deposits after
      postponed charged) : ∀ deposit ∈ deposits, stop deposit = false := by
  induction trace with
  | nil => simp
  | withdrawn ready _ _ _ ih | exiting ready _ _ _ ih | charged ready _ _ _ _ ih =>
    intro deposit member
    rcases List.mem_cons.mp member with rfl | member
    · exact ready
    · exact ih deposit member

/-- Postponed entries form a subsequence of the consumed prefix, with duplicates preserved. -/
theorem PendingDepositTrace.postponed_sublist {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {deposits : List PendingDeposit} {postponed : Array PendingDeposit}
    {charged : Nat}
    (trace : PendingDepositTrace config checks stop nextEpoch state deposits after
      postponed charged) : postponed.toList.Sublist deposits := by
  induction trace with
  | nil => exact .refl _
  | withdrawn _ _ _ _ ih | charged _ _ _ _ _ ih => exact ih.cons _
  | @exiting _ _ deposit _ _ _ _ _ _ _ ih =>
    simpa only [Array.toList_append, Array.toList_push, Array.toList_empty, List.singleton_append]
      using ih.cons_cons deposit

/-- A successful pass consumes a bounded prefix and preserves its untouched suffix.

The trace records the postponed entries in order and the exact amount charged to churn.

An initial count within the epoch limit leaves at most the remaining number of entries consumed.

The initial postponed entries precede those encountered by this pass. -/
theorem passPendingDeposits_trace {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      count ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat →
      ∃ consumed delayed charged,
        deposits = consumed ++ pass.1.rest ∧
        count + consumed.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        pass.1.postponed = postponed ++ delayed ∧
        PendingDepositTrace config checks stop nextEpoch state consumed pass.1.state delayed
          charged ∧
        pass.1.processed.toNat = processed.toNat + charged
  | [], _, _, _, _, _, computed, within => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact ⟨[], #[], 0, rfl, by simpa using within, by simp, .nil _, by simp⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed, within => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact ⟨[], #[], 0, rfl, by simpa using within, by simp, .nil _, by simp⟩
    rename_i proceeds
    have gate : (stop deposit ||
        decide (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤ count)) = false := by
      simpa using proceeds
    have ready : stop deposit = false := (Bool.or_eq_false_iff.mp gate).1
    have room : count + 1 ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
      have := (Bool.or_eq_false_iff.mp gate).2
      simp only [decide_eq_false_iff_not] at this
      omega
    split at computed
    · rename_i withdrawn
      split at computed
      · cases computed
      rename_i credited applied
      split at computed
      · cases computed
      rename_i tail passed
      cases computed
      obtain ⟨consumed, delayed, charged, suffix, bound, queue, trace, amount⟩ :=
        passPendingDeposits_trace passed room
      exact ⟨deposit :: consumed, delayed, charged, by simp [suffix],
        by simp only [List.length_cons]; omega,
        queue, .withdrawn ready withdrawn applied trace, amount⟩
    rename_i withdrawn
    split at computed
    · rename_i exited
      split at computed
      · cases computed
      rename_i tail passed
      cases computed
      obtain ⟨consumed, delayed, charged, suffix, bound, queue, trace, amount⟩ :=
        passPendingDeposits_trace passed room
      refine ⟨deposit :: consumed, #[deposit] ++ delayed, charged, by simp [suffix],
        by simp only [List.length_cons]; omega,
        ?_, .exiting ready (by simpa using withdrawn) exited trace, amount⟩
      dsimp only
      rw [queue, Array.push_eq_append, Array.append_assoc]
    rename_i exited
    split at computed
    · cases computed
    rename_i total added
    split at computed
    · cases computed
      exact ⟨[], #[], 0, rfl, by simpa using within, by simp, .nil _, by simp⟩
    split at computed
    · cases computed
    rename_i credited applied
    split at computed
    · cases computed
    rename_i tail passed
    cases computed
    obtain ⟨consumed, delayed, charged, suffix, bound, queue, trace, amount⟩ :=
      passPendingDeposits_trace passed room
    have sum := (addChecked_ok_iff.mp
      (mapError_ok_iff.mp (liftAccessor_ok.mp added))).2
    refine ⟨deposit :: consumed, delayed, deposit.amount.toNat + charged, by simp [suffix],
      by simp only [List.length_cons]; omega, queue,
      .charged ready (by simpa using withdrawn) (by simpa using exited) applied trace, ?_⟩
    dsimp only at amount ⊢
    rw [amount, sum]
    omega

/-- A pass over the pending deposits keeps one balance for each validator. -/
theorem balancesMatch_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      BalancesMatch state → BalancesMatch pass.1.state
  | [], _, _, _, _, _, computed, holds => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds
  | deposit :: rest, state, processed, count, postponed, pass, computed, holds => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact holds
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact balancesMatch_passPendingDeposits (deposits := rest) ‹_›
        ((applyPendingDeposit_kept credited).1 holds)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact balancesMatch_passPendingDeposits (deposits := rest) ‹_› holds
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact holds
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact balancesMatch_passPendingDeposits (deposits := rest) ‹_›
      ((applyPendingDeposit_kept credited).1 holds)

/-- A pass that starts within the churn available credits no more than that churn inside it. -/
theorem passPendingDeposits_processed_le {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      processed ≤ available → pass.1.processed ≤ available
  | [], _, _, _, _, _, computed, within => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact within
  | deposit :: rest, state, processed, count, postponed, pass, computed, within => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact within
    split at computed
    · split at computed
      · cases computed
      split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_processed_le (deposits := rest) ‹_› within
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_processed_le (deposits := rest) ‹_› within
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact within
    rename_i fits
    split at computed
    · cases computed
    split at computed
    · cases computed
    cases computed
    exact passPendingDeposits_processed_le (deposits := rest) ‹_›
      (UInt64.not_lt.mp fits)

/-- A deposit keeps, at each epoch and key, the two tests of the validator with that key.

They ask whether it exits and whether it is withdrawn.

A new validator does neither, as at a key that no validator has.

That needs an index that fits 64 bits. -/
theorem depositTargetStatus_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (small : state.validators.data.size < 2 ^ 64) :
    depositTargetStatus after = depositTargetStatus state := by
  funext nextEpoch pubkey
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · have pushed := addValidatorToRegistry_validators_eq_push computed small
      -- The new validator has no exit before the far future, and no epoch passes the far future.
      have far : ¬FAR_FUTURE_EPOCH < nextEpoch := by
        rw [UInt64.lt_iff_toNat_lt]
        have := nextEpoch.toNat_lt
        have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        omega
      simp only [depositTargetStatus, pushed, Array.find?_push]
      cases state.validators.data.find? (·.pubkey == pubkey) with
      | some _ => rfl
      | none =>
        simp only [Option.none_or]
        by_cases key : deposit.pubkey = pubkey
        · simp [getValidatorFromDeposit, key, far]
        · simp [getValidatorFromDeposit, key]
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
  · rw [liftAccessor_ok] at computed
    simp only [depositTargetStatus, increaseBalance_validators computed]

/-- The pending deposits of an epoch end with a pass over the queue from its front.

The pass reads the next epoch and the churn available.

That churn is the churn left from the last epoch and the churn of deposits.

It stops at a deposit that waits for the first slot of the finalized epoch.

The registry and the balances are those of the pass.

The queue holds the deposits that the pass did not reach, then those it postponed.

If the pass records that it reached the churn, the churn it did not use carries over.

Otherwise none carries over to the next epoch. -/
theorem processPendingDeposits_pass {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ nextEpoch churn available finalizedSlot pass,
      liftArith (addChecked (getCurrentEpoch state) 1) = .ok nextEpoch ∧
      depositChurnLimit config state = .ok churn ∧
      liftArith (addChecked (state.depositBalanceToConsume electra) churn) = .ok available ∧
      liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch) =
        .ok finalizedSlot ∧
      passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch available
          state 0 0 #[] (state.pendingDeposits electra).data.toList = .ok pass ∧
        after.validators = pass.1.state.validators ∧ after.balances = pass.1.state.balances ∧
        (after.pendingDeposits electra).data = pass.1.rest.toArray ++ pass.1.postponed ∧
        (after.depositBalanceToConsume electra).toNat =
          if pass.1.churnReached then available.toNat - pass.1.processed.toNat else 0 := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals refine ⟨_, _, _, _, _, liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›,
    liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›, ‹_›, rfl, rfl, rfl, ?_⟩
  -- With the churn reached, the step subtracts the churn used, and else it carries none.
  · rename_i reached _ _ subtracted
    rw [ite_eq_left_of_eq_true _ _ (eq_true reached)]
    exact (subChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp subtracted))).2
  · rename_i unreached
    rw [ite_eq_right_of_eq_false _ _ (eq_false unreached)]
    rfl

/-- From Fulu the finalized slot is the only gate in the stop predicate. -/
theorem depositWaits_of_fulu (fulu : .fusaka ≤ fork) (finalizedSlot : Slot)
    (deposit : PendingDeposit) :
    depositWaits state finalizedSlot deposit = decide (finalizedSlot < deposit.slot) := by
  have notElectra : ¬ (.pectra ≤ fork ∧ fork < .fusaka) :=
    fun h => Nat.not_lt.mpr fulu h.2
  simp [depositWaits, bridgeDepositsPending, notElectra]

/-- A consumed deposit is no later than the finalized slot, at every fork from Electra. -/
theorem PendingDepositTrace.finalized {nextEpoch : Epoch} {finalizedSlot : Slot}
    {deposits : List PendingDeposit} {credited : BeaconState preset fork}
    {postponed : Array PendingDeposit} {charged : Nat}
    (trace : PendingDepositTrace config checks (depositWaits state finalizedSlot) nextEpoch
      state deposits credited postponed charged) :
    ∀ deposit ∈ deposits, deposit.slot ≤ finalizedSlot := by
  intro deposit member
  have ready := trace.ready deposit member
  simp only [depositWaits, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ready
  exact UInt64.not_lt.mp ready.2

/-- Each epoch consumes a bounded prefix, charges it within churn, and retains queue order.

The trace distinguishes withdrawn credits from charged credits and postponed entries.

All consumed entries pass finality and, before Fulu, the bridge gate.

The carry is exact on natural numbers, without wrapping subtraction. -/
theorem processPendingDeposits_spec {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ nextEpoch churn available finalizedSlot pass consumed delayed,
      liftArith (addChecked (getCurrentEpoch state) 1) = .ok nextEpoch ∧
      depositChurnLimit config state = .ok churn ∧
      liftArith (addChecked (state.depositBalanceToConsume electra) churn) = .ok available ∧
      liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch) =
        .ok finalizedSlot ∧
      passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch available
          state 0 0 #[] (state.pendingDeposits electra).data.toList = .ok pass ∧
      (state.pendingDeposits electra).data.toList = consumed ++ pass.1.rest ∧
      consumed.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
      PendingDepositTrace config checks (depositWaits state finalizedSlot) nextEpoch state
        consumed pass.1.state delayed pass.1.processed.toNat ∧
      pass.1.processed ≤ available ∧
      (∀ deposit ∈ consumed, deposit.slot ≤ finalizedSlot) ∧
      after.validators = pass.1.state.validators ∧ after.balances = pass.1.state.balances ∧
      (after.pendingDeposits electra).data = pass.1.rest.toArray ++ delayed ∧
      (after.depositBalanceToConsume electra).toNat =
        if pass.1.churnReached then available.toNat - pass.1.processed.toNat else 0 := by
  obtain ⟨nextEpoch, churn, available, finalizedSlot, pass, next, limit, added, finalized,
    passed, validators, balances, queue, carry⟩ := processPendingDeposits_pass computed
  obtain ⟨consumed, delayed, charged, suffix, bound, postponed, trace, amount⟩ :=
    passPendingDeposits_trace passed (Nat.zero_le _)
  simp only [UInt64.toNat_zero, Nat.zero_add] at amount
  subst charged
  simp only [Array.empty_append] at postponed
  have within := passPendingDeposits_processed_le passed UInt64.zero_le
  refine ⟨nextEpoch, churn, available, finalizedSlot, pass, consumed, delayed, next, limit,
    added, finalized, passed, suffix, by simpa using bound, trace, within, trace.finalized,
    validators, balances, ?_, carry⟩
  simpa only [postponed] using queue

/-- The pending deposits of an epoch keep one balance for each validator. -/
theorem balancesMatch_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, validators, balances, _⟩ :=
    processPendingDeposits_pass computed
  have kept := balancesMatch_passPendingDeposits passed holds
  unfold BalancesMatch at kept ⊢
  rw [validators, balances]
  exact kept

/-- The pending deposits of an epoch leave a queue at most as long as before. -/
theorem processPendingDeposits_size_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    (after.pendingDeposits electra).data.size ≤ (state.pendingDeposits electra).data.size := by
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, _, _, queue, _⟩ :=
    processPendingDeposits_pass computed
  have fits := pass.2
  simp only [Array.size_empty, Nat.add_zero, Array.length_toList] at fits
  rw [queue, Array.size_append, List.size_toArray]
  exact fits

/-- A pair of tests is two false tests exactly when neither test holds. -/
private theorem beq_false_false {status : Bool × Bool} :
    (status == (false, false)) = (!status.1 && !status.2) := by
  cases status with
  | mk exited withdrawn => cases exited <;> cases withdrawn <;> rfl

/-- A pair of tests is a true test then a false test exactly when only the first holds. -/
private theorem beq_true_false {status : Bool × Bool} :
    (status == (true, false)) = (status.1 && !status.2) := by
  cases status with
  | mk exited withdrawn => cases exited <;> cases withdrawn <;> rfl

/-- What a pass does with `read`, the deposits that it reads.

They are a prefix of its deposits, at most what the limit per epoch still allows.

It applies `applied` in order, and postpones `moved` in order, and the two make up `read`.

It reads no deposit for which `stop` is true.

If deposits remain, it stopped at one for which `stop` is true, or at the limit per epoch.

Otherwise that deposit takes churn, and it would take more than the churn available.

After the deposits it applied, no validator with its key exits or is withdrawn.

The pass records that it reached the churn.

In every other case it records that it did not reach the churn.

Suppose the registry and the rest of the limit per epoch fit together in 64 bits.

Then the churn that it uses grows by the amount of each deposit it reads that takes churn.

Those are the deposits whose validator, at the start of the pass, neither exits nor is withdrawn.

The churn grows by nothing else.

Under it, `moved` holds exactly the deposits of `read` whose validator exits and is not withdrawn.

As for the churn, the validators are those at the start of the pass.

`applied` holds the others. -/
structure PassPendingDepositsFacts (config : Config) (checks : SignatureChecks)
    (stop : PendingDeposit → Bool) (nextEpoch : Epoch) (available : Gwei)
    (state : BeaconState preset fork) (processed : Gwei) (count : Nat)
    (postponed : Array PendingDeposit) (deposits : List PendingDeposit)
    (pass : PendingDepositsPass preset fork) (read applied moved : List PendingDeposit) : Prop where
  split : deposits = read ++ pass.rest
  pushed : pass.postponed.toList = postponed.toList ++ moved
  bounded : read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count
  appliedSublist : applied.Sublist read
  movedSublist : moved.Sublist read
  perm : (applied ++ moved).Perm read
  applies : applied.foldlM (applyPendingDeposit config checks) state = .ok pass.state
  noneStop : ∀ deposit ∈ read, stop deposit = false
  stops : ∀ deposit tail, pass.rest = deposit :: tail →
    stop deposit = true ∨ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤ count + read.length ∨
      (depositTargetStatus pass.state nextEpoch deposit.pubkey = (false, false) ∧
        available.toNat < pass.processed.toNat + deposit.amount.toNat ∧ pass.churnReached = true)
  reached : pass.churnReached = true →
    ∃ deposit tail, pass.rest = deposit :: tail ∧ stop deposit = false ∧
      count + read.length < preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  used : state.validators.data.size + (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count) <
      2 ^ 64 →
    pass.processed.toNat = processed.toNat + pendingAmount (read.filter fun deposit =>
      depositTargetStatus state nextEpoch deposit.pubkey == (false, false))
  appliedFilter : state.validators.data.size +
      (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count) < 2 ^ 64 →
    applied = read.filter fun deposit =>
      depositTargetStatus state nextEpoch deposit.pubkey != (true, false)
  movedFilter : state.validators.data.size +
      (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count) < 2 ^ 64 →
    moved = read.filter fun deposit =>
      depositTargetStatus state nextEpoch deposit.pubkey == (true, false)

/-- A pass reads a prefix of its deposits, applies some of them and postpones the others.

When the registry and the rest of the limit per epoch fit in 64 bits, it also counts its churn.

In that case it postpones exactly those it reads whose validator exits and is not withdrawn. -/
theorem passPendingDeposits_applied {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      ∃ read applied moved : List PendingDeposit,
        PassPendingDepositsFacts config checks stop nextEpoch available state processed count
          postponed deposits pass.1 read applied moved
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
      List.Perm.refl _, rfl, by simp, by simp, by simp, fun _ => by simp [pendingAmount],
      fun _ => rfl, fun _ => rfl⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · rename_i stopped
      cases computed
      refine ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl, by simp, ?_, by simp, fun _ => by simp [pendingAmount],
        fun _ => rfl, fun _ => rfl⟩
      rintro _ _ ⟨⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at stopped
      exact stopped.imp_right Or.inl
    rename_i continues
    -- The pass reads this deposit, so `stop` is false there and the count is below the limit.
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true,
      Nat.not_le] at continues
    obtain ⟨reads, below⟩ := continues
    split at computed
    · rename_i isWithdrawn
      split at computed
      · cases computed
      rename_i step
      split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      have within := facts.bounded
      -- A deposit credited outside the churn does not wait.
      have notMoved :
          (depositTargetStatus state nextEpoch deposit.pubkey == (true, false)) = false := by
        simp [beq_true_false, isWithdrawn]
      refine ⟨deposit :: read, deposit :: applied, moved,
        { split := congrArg (deposit :: ·) facts.split
          pushed := facts.pushed
          bounded := by simp only [List.length_cons]; omega
          appliedSublist := facts.appliedSublist.cons_cons _
          movedSublist := facts.movedSublist.cons _
          perm := facts.perm.cons deposit
          applies := ?_
          noneStop := List.forall_mem_cons.mpr ⟨reads, facts.noneStop⟩
          stops := fun _ _ head => (facts.stops _ _ head).imp_right
            (Or.imp_left (by simp only [List.length_cons]; omega))
          reached := fun flagged => (facts.reached flagged).imp fun _ =>
            .imp fun _ ⟨front, unstopped, under⟩ =>
              ⟨front, unstopped, by simp only [List.length_cons]; omega⟩
          used := fun room => ?_
          appliedFilter := fun room => ?_
          movedFilter := fun room => ?_ }⟩
      · simp only [List.foldlM_cons, bind, Except.bind, step]
        exact facts.applies
      all_goals
        have small : state.validators.data.size < 2 ^ 64 := by omega
        have grows := (applyPendingDeposit_validators_size_le_and_mem step small).1
        -- The rest of the pass tests the state after the deposit, which keeps both tests per key.
        have kept := depositTargetStatus_applyPendingDeposit step small
      · have used := facts.used (by omega)
        rw [kept] at used
        -- A deposit credited outside the churn takes none of it.
        have outside :
            (depositTargetStatus state nextEpoch deposit.pubkey == (false, false)) = false := by
          simp [beq_false_false, isWithdrawn]
        simp only [List.filter_cons, outside, Bool.false_eq_true, ↓reduceIte, used]
      · have filtered := facts.appliedFilter (by omega)
        rw [kept] at filtered
        simp only [List.filter_cons, bne, notMoved, Bool.not_false, ↓reduceIte, filtered]
      · have filtered := facts.movedFilter (by omega)
        rw [kept] at filtered
        simp only [List.filter_cons, notMoved, Bool.false_eq_true, ↓reduceIte, filtered]
    rename_i notWithdrawn
    split at computed
    · rename_i isExited
      split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      have within := facts.bounded
      -- Its validator exits and is not withdrawn, so the deposit waits.
      have isMoved :
          (depositTargetStatus state nextEpoch deposit.pubkey == (true, false)) = true := by
        simp only [Bool.not_eq_true] at notWithdrawn
        simp [beq_true_false, isExited, notWithdrawn]
      refine ⟨deposit :: read, applied, deposit :: moved,
        { split := congrArg (deposit :: ·) facts.split
          pushed := ?_
          bounded := by simp only [List.length_cons]; omega
          appliedSublist := facts.appliedSublist.cons _
          movedSublist := facts.movedSublist.cons_cons _
          perm := List.perm_middle.trans (facts.perm.cons deposit)
          applies := facts.applies
          noneStop := List.forall_mem_cons.mpr ⟨reads, facts.noneStop⟩
          stops := fun _ _ head => (facts.stops _ _ head).imp_right
            (Or.imp_left (by simp only [List.length_cons]; omega))
          reached := fun flagged => (facts.reached flagged).imp fun _ =>
            .imp fun _ ⟨front, unstopped, under⟩ =>
              ⟨front, unstopped, by simp only [List.length_cons]; omega⟩
          used := fun room => ?_
          appliedFilter := fun room => ?_
          movedFilter := fun room => ?_ }⟩
      · -- The deposit waits after those that earlier steps postponed.
        rw [facts.pushed, Array.toList_push, List.append_assoc]
        rfl
      · have used := facts.used (by omega)
        -- A deposit postponed takes no churn.
        have outside :
            (depositTargetStatus state nextEpoch deposit.pubkey == (false, false)) = false := by
          simp [beq_false_false, isExited]
        simp only [List.filter_cons, outside, Bool.false_eq_true, ↓reduceIte, used]
      · have filtered := facts.appliedFilter (by omega)
        simp only [List.filter_cons, bne, isMoved, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          filtered]
      · have filtered := facts.movedFilter (by omega)
        simp only [List.filter_cons, isMoved, ↓reduceIte, filtered]
    rename_i notExited
    simp only [Bool.not_eq_true] at notWithdrawn notExited
    split at computed
    · cases computed
    rename_i total checked
    have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp checked))).2
    -- The deposit takes churn, since neither test of its validator held.
    have inside :
        (depositTargetStatus state nextEpoch deposit.pubkey == (false, false)) = true := by
      simp [beq_false_false, notExited, notWithdrawn]
    split at computed
    · rename_i over
      cases computed
      -- The deposit does not fit in the churn available.
      have beyond : available.toNat < processed.toNat + deposit.amount.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp over
        omega
      refine ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl, by simp, ?_,
        fun _ => ⟨deposit, rest, rfl, reads, by simpa using below⟩,
        fun _ => by simp [pendingAmount], fun _ => rfl, fun _ => rfl⟩
      rintro _ _ ⟨⟩
      exact Or.inr (Or.inr ⟨eq_of_beq inside, beyond, rfl⟩)
    split at computed
    · cases computed
    rename_i step
    split at computed
    · cases computed
    cases computed
    obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
    have within := facts.bounded
    -- The deposit takes churn, so it does not wait.
    have notMoved :
        (depositTargetStatus state nextEpoch deposit.pubkey == (true, false)) = false := by
      simp [beq_true_false, notExited]
    refine ⟨deposit :: read, deposit :: applied, moved,
      { split := congrArg (deposit :: ·) facts.split
        pushed := facts.pushed
        bounded := by simp only [List.length_cons]; omega
        appliedSublist := facts.appliedSublist.cons_cons _
        movedSublist := facts.movedSublist.cons _
        perm := facts.perm.cons deposit
        applies := ?_
        noneStop := List.forall_mem_cons.mpr ⟨reads, facts.noneStop⟩
        stops := fun _ _ head => (facts.stops _ _ head).imp_right
          (Or.imp_left (by simp only [List.length_cons]; omega))
        reached := fun flagged => (facts.reached flagged).imp fun _ =>
          .imp fun _ ⟨front, unstopped, under⟩ =>
            ⟨front, unstopped, by simp only [List.length_cons]; omega⟩
        used := fun room => ?_
        appliedFilter := fun room => ?_
        movedFilter := fun room => ?_ }⟩
    · simp only [List.foldlM_cons, bind, Except.bind, step]
      exact facts.applies
    all_goals
      have small : state.validators.data.size < 2 ^ 64 := by omega
      have grows := (applyPendingDeposit_validators_size_le_and_mem step small).1
      -- The rest of the pass tests the state after the deposit, which keeps both tests at each key.
      have kept := depositTargetStatus_applyPendingDeposit step small
    · have used := facts.used (by omega)
      rw [kept] at used
      simp only [List.filter_cons, inside, ↓reduceIte, pendingAmount, List.map_cons,
        List.sum_cons] at used ⊢
      omega
    · have filtered := facts.appliedFilter (by omega)
      rw [kept] at filtered
      simp only [List.filter_cons, bne, notMoved, Bool.not_false, ↓reduceIte, filtered]
    · have filtered := facts.movedFilter (by omega)
      rw [kept] at filtered
      simp only [List.filter_cons, notMoved, Bool.false_eq_true, ↓reduceIte, filtered]

/-- The pending deposits of an epoch read a prefix of the queue, at most the limit per epoch.

They apply some of those in order, and move the others to the end of the queue in order.

The state after is the state of those applied, with a new queue and a new churn left over. -/
theorem processPendingDeposits_applied {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ (read rest applied postponed : List PendingDeposit) (next : BeaconState preset fork)
        (pending : PendingDeposits preset fork) (carried : Gwei),
      (state.pendingDeposits electra).data.toList = read ++ rest ∧
        pending.data.toList = rest ++ postponed ∧
        read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        applied.Sublist read ∧ postponed.Sublist read ∧ (applied ++ postponed).Perm read ∧
        applied.foldlM (applyPendingDeposit config checks) state = .ok next ∧
        after = { next with
          pendingDeposits := fun _ => pending
          depositBalanceToConsume := fun _ => carried } := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- Each success ends in the same record, after a pass from count zero with nothing postponed.
  repeat' (split at computed <;> try cases computed)
  all_goals
    obtain ⟨read, applied, postponed, facts⟩ := passPendingDeposits_applied ‹_›
    exact ⟨read, _, applied, postponed, _, _, _, facts.split, by simpa using facts.pushed,
      by simpa using facts.bounded, facts.appliedSublist, facts.movedSublist, facts.perm,
      facts.applies, rfl⟩

/-- The pending deposits of an epoch read a prefix of the queue, at most the limit per epoch.

They postpone those whose validator, in the state before, exits and is not withdrawn.

Withdrawn means withdrawable before the next epoch.

They apply the others in order, and move the postponed ones to the end of the queue in order.

The state after is the state of those applied, with a new queue and a new churn left over.

That needs the registry and the limit per epoch to fit together in 64 bits. -/
theorem processPendingDeposits_postponed {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ (read rest : List PendingDeposit) (next : BeaconState preset fork)
        (pending : PendingDeposits preset fork) (carried : Gwei),
      (state.pendingDeposits electra).data.toList = read ++ rest ∧
        pending.data.toList = rest ++ read.filter (fun deposit =>
          depositTargetStatus state (getCurrentEpoch state + 1) deposit.pubkey == (true, false)) ∧
        read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        (read.filter fun deposit =>
            depositTargetStatus state (getCurrentEpoch state + 1) deposit.pubkey !=
              (true, false)).foldlM (applyPendingDeposit config checks) state = .ok next ∧
        after = { next with
          pendingDeposits := fun _ => pending
          depositBalanceToConsume := fun _ => carried } := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- Each success ends in the same record, after a pass from count zero with nothing postponed.
  repeat' (split at computed <;> try cases computed)
  all_goals
    -- The next epoch that the step computes is the wrapping sum, since the step succeeds.
    have added := liftAccessor_ok.mp
      ‹liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1)) = .ok _›
    rw [liftArith, mapError_ok_iff, addChecked_ok_iff] at added
    obtain rfl := UInt64.toNat_inj.mp (added.2.trans (toNat_add_of_lt added.1).symm)
    obtain ⟨read, applied, _, facts⟩ := passPendingDeposits_applied ‹_›
    have within : state.validators.data.size +
        (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - 0) < 2 ^ 64 := by
      omega
    have applies := facts.applies
    rw [facts.appliedFilter within] at applies
    refine ⟨read, _, _, _, _, facts.split, ?_, by simpa using facts.bounded, applies, rfl⟩
    rw [← facts.movedFilter within]
    simpa using facts.pushed

/-- The queue before splits into the deposits added, the deposits dropped, and the queue after.

The sum of the balances rises by the amounts added.

Each dropped deposit is droppable at the state before.

That needs one balance for each validator.

It also needs room in 64 bits for the registry and the limit per epoch. -/
theorem processPendingDeposits_partition {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ added dropped : List PendingDeposit,
      (added ++ dropped ++ (after.pendingDeposits electra).data.toList).Perm
          (state.pendingDeposits electra).data.toList ∧
        (∀ deposit ∈ dropped, DepositDroppable config checks state deposit) ∧
        balanceSum after = balanceSum state + pendingAmount added := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, length, inRead, _,
    perm, later, rfl⟩ := processPendingDeposits_applied computed
  have fits := inRead.length_le
  obtain ⟨added, dropped, split, all, sum⟩ :=
    foldlM_applyPendingDeposit_partition later holds (by omega)
  refine ⟨added, dropped, ?_, all, sum⟩
  change (added ++ dropped ++ pending.data.toList).Perm _
  rw [queue, kept]
  -- The queue before is `read ++ rest`, and `read` holds `applied` and `postponed` together.
  refine (split.append_right _).trans ((List.perm_append_comm.append_left applied).trans ?_)
  rw [← List.append_assoc]
  exact perm.append_right rest

/-- The pending deposits of an epoch never raise the balances plus the amounts in the queue. -/
theorem processPendingDeposits_total_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    balanceSum after + pendingAmount (after.pendingDeposits electra).data.toList ≤
      balanceSum state + pendingAmount (state.pendingDeposits electra).data.toList := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, _, _, _, perm,
    later, rfl⟩ := processPendingDeposits_applied computed
  have raised := foldlM_applyPendingDeposit_le later
  have amounts := (perm.map (·.amount.toNat)).sum_nat
  change balanceSum next + pendingAmount pending.data.toList ≤ _
  rw [queue, kept]
  simp only [pendingAmount, List.map_append, List.sum_append_nat] at amounts raised ⊢
  omega

/-- A deposit waits when its slot is after `finalizedSlot`.

It also waits when `bridgeDepositsPending` holds and its slot is after the genesis slot.

It waits in no other case. -/
theorem depositWaits_eq_false_iff {finalizedSlot : Slot} {deposit : PendingDeposit} :
    depositWaits state finalizedSlot deposit = false ↔
      deposit.slot ≤ finalizedSlot ∧
        (bridgeDepositsPending state = true → deposit.slot ≤ GENESIS_SLOT) := by
  simp only [depositWaits, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, UInt64.not_lt]
  cases bridgeDepositsPending state <;> simp [and_comm]

/-- A deposit leaves the queue of an epoch only if its slot is at most `finalizedSlot`.

That slot is the first slot of the finalized epoch.

In Electra, while deposits of the old mechanism remain, no request leaves it.

A deposit leaves when the queue after holds fewer copies of it than the queue before. -/
theorem processPendingDeposits_finalized {electra : .pectra ≤ fork} {finalizedSlot : Slot}
    {deposit : PendingDeposit}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (start : computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (fewer : (after.pendingDeposits electra).data.toList.count deposit <
      (state.pendingDeposits electra).data.toList.count deposit) :
    deposit.slot ≤ finalizedSlot ∧
      (bridgeDepositsPending state = true → deposit.slot ≤ GENESIS_SLOT) := by
  obtain ⟨_, _, _, waitSlot, pass, _, _, _, waitSlotOk, passed, _, _, queue, _⟩ :=
    processPendingDeposits_pass computed
  -- The pass waits for the first slot of the finalized epoch.
  obtain rfl : waitSlot = finalizedSlot :=
    Except.ok.inj ((mapError_ok_iff.mp waitSlotOk).symm.trans start)
  obtain ⟨read, _, moved, facts⟩ := passPendingDeposits_applied passed
  -- The queue after holds the deposits not reached, then some of those read.
  have kept : (after.pendingDeposits electra).data.toList = pass.1.rest ++ moved := by
    rw [queue]
    simpa using facts.pushed
  have before := congrArg (List.count deposit) facts.split
  rw [kept] at fewer
  simp only [List.count_append] at fewer before
  have bound := facts.movedSublist.count_le deposit
  exact depositWaits_eq_false_iff.mp (facts.noneStop deposit (List.count_pos_iff.mp (by omega)))

end EthLib.Consensus
