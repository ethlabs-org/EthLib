module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.ValidatorCaps
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# The stake that can leave the active set within two epochs

Take a reachable state in some epoch, and a state at most two epochs later.

A validator active in the first state and not in the later one exits in between.

Either its exit epoch was already set in the first state, or a step charged it later.

A charge in a later epoch lands too late, since the seed lookahead delays every exit.

So a charge that counts happens in the epoch of the first state.

Those charges spend the exit and consolidation queues of that epoch, as [EIP-7251] specifies.

Before Electra they spend the count of exits per epoch of the exit queue.

Within one epoch the effective balances and the active set stay fixed.

So the churn of that epoch is the churn of the first state, and each charge is the stake it moves.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus.ExitChurn

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Steps that keep what the churn reads -/

/-- Two states that hold the same exit and consolidation queues, from Electra. -/
private def QueuesSame (s t : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork,
    t.earliestExitEpoch electra = s.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = s.exitBalanceToConsume electra ∧
      t.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra ∧
      t.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra

/-- A step that keeps the epoch, the queues, the active set, the exits and the effective balances.

It may add validators.

A new validator has no exit epoch yet, and is active in no epoch up to the current one.
-/
private structure Kept (s t : BeaconState preset fork) : Prop where
  epoch : getCurrentEpoch t = getCurrentEpoch s
  queues : QueuesSame s t
  active : ActiveKept (getCurrentEpoch s) s t
  old : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    ∃ w : Validator, t.validators.data[i]? = some w ∧
      w.exitEpoch = v.exitEpoch ∧ w.effectiveBalance = v.effectiveBalance
  new : ∀ (i : Nat) (w : Validator), s.validators.data.size ≤ i → t.validators.data[i]? = some w →
    w.exitEpoch = FAR_FUTURE_EPOCH

private theorem Kept.refl (s : BeaconState preset fork) : Kept s s :=
  ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, ActiveKept.refl _ _, fun _ v found => ⟨v, found, rfl, rfl⟩,
    fun _ _ large found => absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega)⟩

private theorem Kept.trans {s m t : BeaconState preset fork} (one : Kept s m) (two : Kept m t) :
    Kept s t where
  epoch := two.epoch.trans one.epoch
  queues electra := by
    obtain ⟨a, b, c, d⟩ := one.queues electra
    obtain ⟨a', b', c', d'⟩ := two.queues electra
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  active := one.active.trans (one.epoch ▸ two.active)
  old i v found := by
    obtain ⟨u, hu, eu, bu⟩ := one.old i v found
    obtain ⟨w, hw, ew, bw⟩ := two.old i u hu
    exact ⟨w, hw, ew.trans eu, bw.trans bu⟩
  new i w large found := by
    by_cases inside : i < m.validators.data.size
    · obtain ⟨u, hu⟩ : ∃ u, m.validators.data[i]? = some u := ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨w', hw', ew', _⟩ := two.old i u hu
      rw [found] at hw'
      cases hw'
      exact ew'.trans (one.new i u large hu)
    · exact two.new i w (by omega) found

/-- A kept step keeps every validator, so the registry does not shrink. -/
private theorem Kept.size_le {s t : BeaconState preset fork} (kept : Kept s t) :
    s.validators.data.size ≤ t.validators.data.size := by
  by_contra small
  have inside : t.validators.data.size < s.validators.data.size := by omega
  obtain ⟨w, hw, _⟩ := kept.old _ _ (Array.getElem?_eq_getElem inside)
  have := (Array.getElem?_eq_some_iff.mp hw).1
  omega

/-- A step that keeps the registry, the epoch and the queues. -/
private theorem Kept.of_epoch {s t : BeaconState preset fork}
    (validators : t.validators.data = s.validators.data)
    (epoch : getCurrentEpoch t = getCurrentEpoch s)
    (queues : QueuesSame s t := by exact fun _ => ⟨rfl, rfl, rfl, rfl⟩) : Kept s t where
  epoch := epoch
  queues := queues
  active _ _ i := by simp only [isActiveAt, validators]
  old i v found := ⟨v, by rw [validators]; exact found, rfl, rfl⟩
  new i w large found := by
    rw [validators] at found
    exact absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega)

/-- A step that keeps the registry, the slot and the queues. -/
private theorem Kept.of_data {s t : BeaconState preset fork}
    (validators : t.validators.data = s.validators.data := by rfl)
    (slot : t.slot = s.slot := by rfl)
    (queues : QueuesSame s t := by exact fun _ => ⟨rfl, rfl, rfl, rfl⟩) : Kept s t :=
  Kept.of_epoch validators (by unfold getCurrentEpoch; rw [slot]) queues

/-- A state equal to an update of another field of the state keeps what the churn reads. -/
private theorem Kept.of_update {s t u : BeaconState preset fork} (rest : u = s)
    (validators : t.validators.data = u.validators.data := by rfl)
    (slot : t.slot = u.slot := by rfl)
    (queues : QueuesSame u t := by exact fun _ => ⟨rfl, rfl, rfl, rfl⟩) : Kept s t := by
  subst rest
  exact Kept.of_data validators slot queues

/-- A validator write that keeps the exit epoch, the effective balance and the activity. -/
private theorem kept_setValidatorAt {s t : BeaconState preset fork} {i : Nat} {old v : Validator}
    (found : getValidatorAt s i = .ok old) (set : s.setValidatorAt i v = .ok t)
    (exit : v.exitEpoch = old.exitEpoch) (balance : v.effectiveBalance = old.effectiveBalance)
    (activity : ∀ e ≤ getCurrentEpoch s, isActiveValidator v e = isActiveValidator old e) :
    Kept s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldFound : s.validators.data[i]? = some old := getValidatorAt_eq_ok_iff.mp found
  refine ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro e le j
    simp only [isActiveAt, BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
    split
    · rename_i same
      subst same
      simp [oldFound, activity e le]
    · rfl
  · intro j w found
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set] at found ⊢
    split
    · rename_i same
      subst same
      rw [oldFound] at found
      cases found
      exact ⟨v, rfl, exit, balance⟩
    · exact ⟨w, found, rfl, rfl⟩
  · intro j w large found
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set] at found
    split at found
    · omega
    · exact absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega)

private theorem kept_setValidatorAt_same {s t : BeaconState preset fork} {i : Nat}
    {old v : Validator}
    (found : getValidatorAt s i = .ok old) (set : s.setValidatorAt i v = .ok t)
    (exit : v.exitEpoch = old.exitEpoch) (balance : v.effectiveBalance = old.effectiveBalance)
    (activation : v.activationEpoch = old.activationEpoch) : Kept s t :=
  kept_setValidatorAt found set exit balance fun _ _ => by
    unfold isActiveValidator
    rw [activation, exit]

private theorem kept_setValidator {s t : BeaconState preset fork} {i : ValidatorIndex}
    {old v : Validator}
    (found : getValidator s i = .ok old) (set : s.setValidator i v = .ok t)
    (exit : v.exitEpoch = old.exitEpoch) (balance : v.effectiveBalance = old.effectiveBalance)
    (activity : ∀ e ≤ getCurrentEpoch s, isActiveValidator v e = isActiveValidator old e) :
    Kept s t :=
  kept_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) exit balance activity

private theorem kept_setValidator_same {s t : BeaconState preset fork} {i : ValidatorIndex}
    {old v : Validator} (found : getValidator s i = .ok old) (set : s.setValidator i v = .ok t)
    (exit : v.exitEpoch = old.exitEpoch) (balance : v.effectiveBalance = old.effectiveBalance)
    (activation : v.activationEpoch = old.activationEpoch) : Kept s t :=
  kept_setValidatorAt_same (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) exit balance activation

private theorem kept_setBalance {s t : BeaconState preset fork} {i : ValidatorIndex}
    {balance : Gwei}
    (set : s.setBalance i balance = .ok t) : Kept s t := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact Kept.of_data

private theorem kept_increaseBalance {s t : BeaconState preset fork} {i : ValidatorIndex}
    {delta : Gwei}
    (ok : increaseBalance s i delta = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  exact kept_setBalance set

private theorem kept_decreaseBalance {s t : BeaconState preset fork} {i : ValidatorIndex}
    {delta : Gwei}
    (ok : decreaseBalance s i delta = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  exact kept_setBalance set

/-- A validator with no activation epoch is active in no epoch. -/
private theorem inactive_of_far {v : Validator} (far : v.activationEpoch = FAR_FUTURE_EPOCH)
    (e : Epoch) :
    isActiveValidator v e = false := by
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  have bound := v.exitEpoch.toNat_lt
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, far, FAR_FUTURE_EPOCH] at *
  have farNat : (UInt64.ofNat (2 ^ 64 - 1)).toNat = 18446744073709551615 := rfl
  omega

/-- Appending a validator that has no exit and is active in no epoch keeps what the churn reads. -/
private theorem kept_append {s t : BeaconState preset fork} {v : Validator}
    (added : t.validators.data = s.validators.data.push v)
    (slot : t.slot = s.slot) (queues : QueuesSame s t)
    (exit : v.exitEpoch = FAR_FUTURE_EPOCH) (far : v.activationEpoch = FAR_FUTURE_EPOCH) :
    Kept s t where
  epoch := by unfold getCurrentEpoch; rw [slot]
  queues := queues
  active e _ i := by
    simp only [isActiveAt, added, Array.getElem?_push]
    split
    · rename_i same
      subst same
      simp [inactive_of_far far]
    · rfl
  old i w found := by
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨w, ?_, rfl, rfl⟩
    simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found
  new i w large found := by
    rw [added, Array.getElem?_push] at found
    split at found
    · cases found; exact exit
    · exact absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega)

private theorem kept_addValidatorToRegistry {s t : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s pubkey credentials amount = .ok t) : Kept s t := by
  have added := addValidatorToRegistry_validators_eq_push ok
  have fields : t.slot = s.slot ∧ QueuesSame s t := by
    unfold addValidatorToRegistry at ok
    split at ok
    · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
      exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
    · split at ok
      · cases ok
        exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
      · cases ok
  exact kept_append added fields.1 fields.2 rfl rfl

/-! ## The churn of a kept state -/

/-- A sum over more positions that adds only zeros past the first ones. -/
private theorem sum_range_extend {n m : Nat} (le : n ≤ m) (f g : Nat → Nat)
    (agree : ∀ j < n, f j = g j) (zero : ∀ j, n ≤ j → j < m → f j = 0) :
    ((List.range m).map f).sum = ((List.range n).map g).sum := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  induction k with
  | zero =>
    exact congrArg List.sum (List.map_congr_left fun j member => agree j (List.mem_range.mp member))
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append,
      ih (Nat.le_add_right _ _) (fun j low high => zero j low (by omega))]
    simp [zero (n + k) (by omega) (by omega)]

/-- A kept step keeps the total active balance, and so every churn limit. -/
private theorem totalActiveBalance_eq {s t : BeaconState preset fork}
    (epoch : getCurrentEpoch t = getCurrentEpoch s) (active : ActiveKept (getCurrentEpoch s) s t)
    (size : s.validators.data.size ≤ t.validators.data.size)
    (balanceKept : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      ∃ w : Validator, t.validators.data[i]? = some w ∧ w.effectiveBalance = v.effectiveBalance) :
    getTotalActiveBalance t = getTotalActiveBalance s := by
  unfold getTotalActiveBalance
  rw [epoch, active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _)]
  cases checked : getActiveValidatorIndicesChecked s (getCurrentEpoch s) with
  | error e => rfl
  | ok indices =>
    simp only [bind, Except.bind]
    have listed := fun (index : ValidatorIndex) =>
      mem_iff_of_getActiveValidatorIndicesChecked_ok checked (index := index)
    have below : ∀ index ∈ indices, index.toNat < s.validators.data.size := by
      intro index member
      obtain ⟨v, found, _⟩ := (listed index).mp member
      exact (Array.getElem?_eq_some_iff.mp found).1
    have findS : indices.find? (s.validators.data.size ≤ ·.toNat) = none :=
      List.find?_eq_none.mpr fun index member => by simpa using below index member
    have findT : indices.find? (t.validators.data.size ≤ ·.toNat) = none :=
      List.find?_eq_none.mpr fun index member => by
        have := below index member
        simp only [decide_eq_true_eq, not_le]
        omega
    have sum : sumMarked t.validators.data (markIndices t.validators.data.size indices) =
        sumMarked s.validators.data (markIndices s.validators.data.size indices) := by
      rw [sumMarked_eq_sum, sumMarked_eq_sum]
      apply sum_range_extend size
      · intro j inside
        rw [getElem?_markIndices, getElem?_markIndices,
          ite_eq_left (show j < t.validators.data.size by omega), ite_eq_left inside]
        simp only [Option.getD_some]
        by_cases marked : (indices.any fun x => x.toNat == j) = true
        · rw [ite_eq_left marked, ite_eq_left marked]
          obtain ⟨index, member, equal⟩ := List.any_eq_true.mp marked
          have same := beq_iff_eq.mp equal
          obtain ⟨v, found, _⟩ := (listed index).mp member
          rw [same] at found
          obtain ⟨w, hw, balance⟩ := balanceKept j v found
          simp [found, hw, balance]
        · rw [ite_eq_right marked, ite_eq_right marked]
      · intro j low high
        rw [getElem?_markIndices, ite_eq_left high]
        simp only [Option.getD_some]
        by_cases marked : (indices.any fun x => x.toNat == j) = true
        · obtain ⟨index, member, equal⟩ := List.any_eq_true.mp marked
          have := below index member
          have := beq_iff_eq.mp equal
          omega
        · rw [ite_eq_right marked]
    unfold getTotalBalance
    simp only [findS, findT, sum]

/-- A kept step keeps the total active balance. -/
private theorem Kept.totalActiveBalance {s t : BeaconState preset fork} (kept : Kept s t) :
    getTotalActiveBalance t = getTotalActiveBalance s :=
  totalActiveBalance_eq kept.epoch kept.active kept.size_le fun i v found => by
    obtain ⟨w, hw, _, balance⟩ := kept.old i v found
    exact ⟨w, hw, balance⟩

/-- The exit churn reads only the total active balance. -/
private theorem exitChurn_congr {s t : BeaconState preset fork}
    (total : getTotalActiveBalance t = getTotalActiveBalance s) :
    exitChurnLimit config t = exitChurnLimit config s := by
  unfold exitChurnLimit getExitChurnLimit getActivationExitChurnLimit getBalanceChurnLimit
  rw [total]

/-- The consolidation churn reads only the total active balance. -/
private theorem consolidationChurn_congr {s t : BeaconState preset fork}
    (total : getTotalActiveBalance t = getTotalActiveBalance s) :
    getConsolidationChurnLimit config t = getConsolidationChurnLimit config s := by
  unfold getConsolidationChurnLimit getActivationExitChurnLimit getBalanceChurnLimit
  rw [total]

/-- Before Electra the churn counts the active validators of the current epoch. -/
private theorem validatorChurn_congr {s t : BeaconState preset fork}
    (epoch : getCurrentEpoch t = getCurrentEpoch s) (active : ActiveKept (getCurrentEpoch s) s t) :
    getValidatorChurnLimit config t = getValidatorChurnLimit config s := by
  unfold getValidatorChurnLimit
  rw [epoch, active.getActiveValidatorIndices_eq (UInt64.le_refl _)]

/-! ## Invariants of the steps of one epoch -/

/-- An invariant of states of one fork that every step of one epoch keeps.

Kept steps keep it.

So does each call of a queue: an exit, a partial withdrawal or a consolidation. -/
private structure Laws (config : Config) (Inv : BeaconState preset fork → Prop) : Prop where
  kept : ∀ {s t : BeaconState preset fork}, Kept s t → Inv s → Inv t
  exit : ∀ {s t : BeaconState preset fork} {index : ValidatorIndex},
    initiateValidatorExit config s index = .ok t → Inv s → Inv t
  churn : ∀ {s t : BeaconState preset fork} {electra : .pectra ≤ fork} {amount : Gwei}
    {epoch : Epoch}, computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch) →
    Inv s → Inv t
  consolidate : ∀ {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator},
    s.validators.data[sourceIndex.toNat]? = some source → source.exitEpoch = FAR_FUTURE_EPOCH →
    queueConsolidation config s electra sourceIndex source targetIndex = .ok t → Inv s → Inv t

/-- A step after which an invariant holds when it held before. -/
private def Keeps (Inv : BeaconState preset fork → Prop) (s t : BeaconState preset fork) : Prop :=
  Inv s → Inv t

section Traversal

variable {Inv : BeaconState preset fork → Prop}

private theorem Keeps.refl (s : BeaconState preset fork) : Keeps Inv s s := id

private theorem Keeps.trans {s m t : BeaconState preset fork} (one : Keeps Inv s m)
    (two : Keeps Inv m t) : Keeps Inv s t := two ∘ one

private theorem Keeps.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → Keeps Inv s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : Keeps Inv state after :=
  foldlM_ok_invariant (Keeps Inv state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (Keeps.refl state) ok

private theorem keeps_of_kept (laws : Laws config Inv) {s t : BeaconState preset fork}
    (kept : Kept s t) :
    Keeps Inv s t :=
  laws.kept kept

private theorem keeps_exit (laws : Laws config Inv) {s t : BeaconState preset fork}
    {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) : Keeps Inv s t :=
  laws.exit ok

/-- A validator that activates later than an epoch is not active in it. -/
private theorem inactive_of_lt {v : Validator} {e : Epoch} (late : e < v.activationEpoch) :
    isActiveValidator v e = false := by
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact .inl (UInt64.not_le.mpr late)

private theorem keeps_slashValidator (laws : Laws config Inv) {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) : Keeps Inv state after := by
  obtain ⟨exited, _, _, marked, _, _, slashings, lowered, _, _, raised, last, exitedOk, read, _,
    set, _, _, _, loweredOk, _, _, raisedOk, lastOk, rfl⟩ := slashValidator_ok ok
  have first : Kept exited lowered :=
    (kept_setValidator_same read set rfl rfl rfl).trans
      ((Kept.of_data (s := marked) (t := { marked with slashings })).trans
        (kept_decreaseBalance loweredOk))
  have second : Kept lowered last :=
    (kept_increaseBalance raisedOk).trans (kept_increaseBalance lastOk)
  apply (keeps_exit laws exitedOk).trans (keeps_of_kept laws (first.trans second)) |>.trans
  split
  · exact keeps_of_kept laws Kept.of_data
  · exact Keeps.refl _

private theorem keeps_processProposerSlashing (laws : Laws config Inv) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    Keeps Inv state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact keeps_slashValidator laws slashed

private theorem keeps_slashIfSlashable (laws : Laws config Inv)
    {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (ok : slashIfSlashable config step index = .ok next) :
    Keeps Inv step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact keeps_slashValidator laws slashed
  · cases ok; exact Keeps.refl _

private theorem keeps_processAttesterSlashing (laws : Laws config Inv)
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    Keeps Inv state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step => Keeps Inv state step.1)
    (fun _ _ _ before ok => before.trans (keeps_slashIfSlashable laws ok))
    (show Keeps Inv state (state, false).1 from Keeps.refl state) folded

private theorem keeps_attestation (laws : Laws config Inv) {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    Keeps Inv state after := by
  unfold processAttestation at ok
  split at ok
  · unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have last : Keeps Inv raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]; exact keeps_of_kept laws Kept.of_data
      · cases final; exact Keeps.refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        Kept state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact Kept.of_data
    exact (keeps_of_kept laws ((flagged _ _).trans (kept_increaseBalance raisedOk))).trans last
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact keeps_of_kept laws (Kept.of_update rest)

private theorem kept_applyPendingDeposit {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks state deposit = .ok after) : Kept state after := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact Kept.refl _
  · exact kept_increaseBalance raised
  · exact kept_addValidatorToRegistry added

private theorem kept_applyDeposit {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (ok : applyDeposit config checks state pubkey credentials amount signature = .ok after) :
    Kept state after := by
  unfold applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, added, pushed⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (kept_addValidatorToRegistry added).trans Kept.of_data
      · cases ok; exact Kept.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact Kept.of_data
  · exact kept_applyPendingDeposit ok

private theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before state deposit = .ok after) : Kept state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (Kept.of_data (s := state) (t := { state with eth1DepositIndex := fun _ => next })).trans
    (kept_applyDeposit credited)

private theorem keeps_processVoluntaryExit (laws : Laws config Inv) {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks state signed = .ok after) :
    Keeps Inv state after := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact laws.exit exited

private theorem kept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    Kept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact kept_setValidator_same found set rfl rfl rfl

private theorem kept_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance state electra index = .ok after) : Kept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact Kept.of_data
  · cases ok; exact Kept.refl _

private theorem kept_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (ok : switchToCompoundingValidator state electra index = .ok after) : Kept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (kept_setValidator_same found set rfl rfl rfl).trans
    (kept_queueExcessActiveBalance queued)

private theorem keeps_requestPartialWithdrawal (laws : Laws config Inv) {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : Keeps Inv state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact (show Keeps Inv _ _ from laws.churn churned).trans (keeps_of_kept laws Kept.of_data)
  · cases ok; exact Keeps.refl _

private theorem keeps_processWithdrawalRequest (laws : Laws config Inv) {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    Keeps Inv state after := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact Keeps.refl _)
    | exact keeps_requestPartialWithdrawal laws ok
    | exact laws.exit (liftAccessor_ok.mp ok)

private theorem keeps_processConsolidationRequest (laws : Laws config Inv)
    {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config state electra request = .ok after) :
    Keeps Inv state after := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact Keeps.refl _)
    | exact keeps_of_kept laws (kept_switchToCompoundingValidator (liftAccessor_ok.mp ok))
    | exact laws.consolidate (getElem?_toNat_of_ofNatChecked (by assumption)) (by simp_all) ok

private theorem kept_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) : Kept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact Kept.of_data

private theorem keeps_processExecutionRequests (laws : Laws config Inv)
    {body : BeaconBlockBody preset fork} {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionRequests config state body electra = .ok after) :
    Keeps Inv state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (Keeps.foldlM (fun _ _ _ ok => keeps_of_kept laws (kept_processDepositRequest ok))
    deposits).trans <|
    (Keeps.foldlM (fun _ _ _ ok => keeps_processWithdrawalRequest laws ok) withdrawals).trans
      (Keeps.foldlM (fun _ _ _ ok => keeps_processConsolidationRequest laws ok) consolidations)

private theorem kept_applyWithdrawal {withdrawal : Withdrawal}
    (ok : applyWithdrawal state withdrawal = .ok after) : Kept state after := by
  unfold applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact Kept.of_data
  · exact kept_decreaseBalance ok

private theorem kept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (ok : applyExpectedWithdrawals state capella expected = .ok after) : Kept state after := by
  apply applyExpectedWithdrawals_of Kept Kept.refl (fun one two => one.trans two)
    (fun withdrawn => kept_applyWithdrawal withdrawn) ?_ ok
  intro s t frame same exit left consolidation remaining
  exact Kept.of_data (congrArg (·.data) same) frame.slot
    (fun h => ⟨congrFun exit h, congrFun left h, congrFun consolidation h,
      congrFun remaining h⟩)

private theorem kept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals state capella payload = .ok after) : Kept state after := by
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact kept_applyExpectedWithdrawals applied
    · cases ok; exact Kept.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact kept_applyExpectedWithdrawals applied

private theorem kept_executionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionPayload config engine state body bellatrix = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact Kept.of_data

private theorem kept_blockExecution (early : fork < .glamsterdam)
    {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Kept state after := by
  unfold processBlockExecution at ok
  split at ok
  · rename_i gloas
    exact absurd gloas (Nat.not_le_of_lt early)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (kept_processWithdrawals withdrawn).trans (kept_executionPayload paid)
  · dsimp only at ok
    split at ok
    · exact kept_executionPayload ok
    · cases ok; exact Kept.refl _

private theorem keeps_operations (laws : Laws config Inv) (early : fork < .glamsterdam)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after) :
    Keeps Inv state after := by
  obtain ⟨_, _, _, proposers, attesters, attested, rest⟩ :=
    processOperations_folds_of (Keeps Inv) Keeps.refl (fun one two => one.trans two)
      (fun deposited => keeps_of_kept laws (kept_processDeposit deposited))
      (keeps_processVoluntaryExit laws)
      (fun changed => keeps_of_kept laws (kept_processBlsToExecutionChange changed))
      (keeps_processExecutionRequests laws)
      (fun {state after gloas} _ => absurd gloas (Nat.not_le_of_lt early)) ok
  exact (Keeps.foldlM (fun _ _ _ ok => keeps_processProposerSlashing laws ok) proposers).trans <|
    (Keeps.foldlM (fun _ _ _ ok => keeps_processAttesterSlashing laws ok) attesters).trans <|
    (Keeps.foldlM (fun _ _ _ ok => keeps_attestation laws ok) attested).trans <|
    rest

private theorem kept_blockHeader {block : BeaconBlock preset fork}
    (ok : processBlockHeader state block = .ok after) : Kept state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact Kept.of_data

private theorem kept_randao {body : BeaconBlockBody preset fork}
    (ok : processRandao config checks state body = .ok after) : Kept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact Kept.of_data

private theorem kept_eth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : processEth1Data before state body = .ok after) : Kept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact Kept.of_update rest

private theorem kept_syncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks state altair aggregate = .ok after) :
    Kept state after := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  exact foldlM_ok_invariant (Kept state) (fun _ _ _ h ok => h.trans (by
    unfold applySyncReward at ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, raised, _, _, paid⟩ := ok
      exact (kept_increaseBalance raised).trans (kept_increaseBalance paid)
    · exact kept_decreaseBalance (liftAccessor_ok.mp ok))) (Kept.refl state) folded

/-- A block keeps an invariant of the epoch, at every fork before Gloas. -/
private theorem keeps_processBlock (laws : Laws config Inv) (early : fork < .glamsterdam)
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) : Keeps Inv state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept state input := started.step_of Kept Kept.refl
    (fun one two => one.trans two)
    (fun gloas _ => absurd gloas (Nat.not_le_of_lt early)) kept_blockHeader
    (fun _ executed => kept_blockExecution early executed) kept_randao
    (fun _ voted => kept_eth1Data voted)
  have tail : Kept last after := by
    split at synced
    · exact kept_syncAggregate synced
    · cases synced
      exact Kept.refl _
  exact (keeps_of_kept laws head).trans
    ((keeps_operations laws early operated).trans (keeps_of_kept laws tail))

/-! ### The epoch step up to the registry updates -/

private theorem kept_justification (ok : processJustificationAndFinalization state = .ok after) :
    Kept state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · subst same; exact Kept.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact Kept.of_update rest

private theorem kept_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (ok : applyAllDeltas state deltas = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state) (fun _ _ _ h ok => h.trans (by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (kept_increaseBalance raised).trans (kept_decreaseBalance lowered))) (Kept.refl state) ok

private theorem kept_rewards (ok : processRewardsAndPenalties config state = .ok after) :
    Kept state after := by
  unfold processRewardsAndPenalties at ok
  split at ok
  · cases ok; exact Kept.refl _
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact foldlM_ok_invariant (Kept state) (fun _ _ _ h ok => h.trans (kept_applyAllDeltas ok))
      (Kept.refl state) applied
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact kept_applyAllDeltas applied

private theorem kept_inactivity {altair : .altair ≤ fork}
    (ok : processInactivityUpdates config state altair = .ok after) : Kept state after := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; exact Kept.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact Kept.of_data

private theorem keeps_updateRegistryEntry (laws : Laws config Inv) {index : Nat}
    (ok : updateRegistryEntry config state index = .ok after) : Keeps Inv state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queuedOk, marked, markedOk, ok⟩ := ok
  have epochs : queued.activationEpoch = v.activationEpoch ∧ queued.exitEpoch = v.exitEpoch ∧
      queued.effectiveBalance = v.effectiveBalance := by
    unfold queueForActivation at queuedOk
    split at queuedOk
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
      obtain ⟨_, _, rfl⟩ := queuedOk
      exact ⟨rfl, rfl, rfl⟩
    · cases queuedOk; exact ⟨rfl, rfl, rfl⟩
  have first : Kept state marked :=
    kept_setValidatorAt_same found markedOk epochs.2.1 epochs.2.2 epochs.1
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact (keeps_of_kept laws first).trans (keeps_exit laws exited)
  · cases ok; exact keeps_of_kept laws first

private theorem keeps_activateValidator (laws : Laws config Inv)
    {index : ValidatorIndex} {v : Validator}
    (found : getValidator state index = .ok v) (far : v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : activateValidator state index = .ok after) : Keeps Inv state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨old, read, epoch, epochOk, set⟩ := ok
  have equal : old = v := Except.ok.inj (read.symm.trans found)
  subst equal
  have late := (computeActivationExitEpoch_ok_iff.mp (mapError_ok_iff.mp epochOk)).2
  exact keeps_of_kept laws (kept_setValidator read set rfl rfl (fun e le => by
    rw [inactive_of_far far e]
    apply inactive_of_lt
    rw [UInt64.lt_iff_toNat_lt]
    have := UInt64.le_iff_toNat_le.mp le
    change e.toNat < epoch.toNat
    omega))

private theorem keeps_updateRegistryEntryElectra (laws : Laws config Inv) {activationEpoch : Epoch}
    {index : Nat} (late : getCurrentEpoch state < activationEpoch)
    (ok : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    Keeps Inv state after ∧ after.slot = state.slot := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    refine ⟨keeps_of_kept laws (kept_setValidatorAt_same found set rfl rfl rfl), ?_⟩
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    rfl
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact ⟨laws.exit exited, (frame_initiateValidatorExit exited).slot⟩
  split at ok
  · rename_i eligible
    have set := liftAccessor_ok.mp ok
    have far := activationEpoch_of_isEligibleForActivation eligible
    refine ⟨keeps_of_kept laws (kept_setValidatorAt found set rfl rfl (fun e le => ?_)), ?_⟩
    · rw [inactive_of_far far e]
      apply inactive_of_lt
      exact UInt64.lt_of_le_of_lt le late
    · obtain ⟨_, rfl⟩ := setValidatorAt_ok set
      rfl
  · cases ok; exact ⟨Keeps.refl _, rfl⟩

/-- The registry updates keep an invariant of the epoch.

Their activations land after the current epoch, and their ejections call the exit queue. -/
private theorem keeps_processRegistryUpdates (laws : Laws config Inv)
    (ok : processRegistryUpdates config state = .ok after) : Keeps Inv state after := by
  exact processRegistryUpdates_of Keeps.refl (fun one two => one.trans two)
    (keeps_updateRegistryEntry laws) (keeps_updateRegistryEntryElectra laws)
    (keeps_activateValidator laws) ok

/-- Caching the roots of a slot keeps what the churn reads. -/
private theorem kept_processSlot (ok : processSlot state = .ok after) : Kept state after := by
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok ok
  rw [cachedEq]
  exact Kept.of_data

end Traversal

/-! ## The rest of the epoch step keeps the exits -/

/-- Each validator keeps its exit epoch, whatever happens to its effective balance. -/
private def ExitsOnly (s t : BeaconState preset fork) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    ∃ w : Validator, t.validators.data[i]? = some w ∧ w.exitEpoch = v.exitEpoch

/-- Each existing validator keeps its exit epoch. -/
private structure ExitsSame (s t : BeaconState preset fork) : Prop where
  exits : ExitsOnly s t

private theorem ExitsSame.refl (s : BeaconState preset fork) : ExitsSame s s :=
  ⟨fun _ v found => ⟨v, found, rfl⟩⟩

private theorem ExitsSame.trans {s m t : BeaconState preset fork} (one : ExitsSame s m)
    (two : ExitsSame m t) : ExitsSame s t := by
  refine ⟨?_⟩
  intro i v found
  obtain ⟨u, hu, eu⟩ := one.1 i v found
  obtain ⟨w, hw, ew⟩ := two.1 i u hu
  exact ⟨w, hw, ew.trans eu⟩

private theorem ExitsSame.of_kept {s t : BeaconState preset fork}
    (kept : Kept s t) : ExitsSame s t := by
  refine ⟨?_⟩
  intro i v found
  obtain ⟨w, hw, ew, _⟩ := kept.old i v found
  exact ⟨w, hw, ew⟩

private theorem ExitsSame.of_data {s t : BeaconState preset fork}
    (validators : t.validators.data = s.validators.data := by rfl) : ExitsSame s t :=
  ⟨fun _ v found => ⟨v, by rw [validators]; exact found, rfl⟩⟩

private theorem ExitsSame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → ExitsSame s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : ExitsSame state after :=
  foldlM_ok_invariant (ExitsSame state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (ExitsSame.refl state) ok

private theorem exitsSame_setValidatorAt {s t : BeaconState preset fork} {i : Nat}
    {old v : Validator}
    (found : getValidatorAt s i = .ok old) (set : s.setValidatorAt i v = .ok t)
    (exit : v.exitEpoch = old.exitEpoch) : ExitsOnly s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldFound : s.validators.data[i]? = some old := getValidatorAt_eq_ok_iff.mp found
  intro j w read
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
  split
  · rename_i same
    subst same
    rw [oldFound] at read
    cases read
    exact ⟨v, by simp, exit⟩
  · exact ⟨w, read, rfl⟩

private theorem exitsSame_processPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} {deposits : List PendingDeposit} {state : BeaconState preset fork}
    {processed : Gwei} {count : Nat} {postponed : Array PendingDeposit} {pass}
    (ok : passPendingDeposits config checks stop nextEpoch available state processed count
      postponed deposits = .ok pass) : ExitsSame state pass.1.state :=
  passPendingDeposits_of ExitsSame ExitsSame.refl (fun one two => one.trans two)
    (fun credited => ExitsSame.of_kept (kept_applyPendingDeposit credited)) ok

private theorem exitsSame_slashings (ok : processSlashings state = .ok after) :
    ExitsSame state after := by
  unfold processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    refine ExitsSame.foldlM (fun _ _ _ ok => ?_) applied
    unfold applySlashingPenaltyElectra at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact ExitsSame.refl _)
      | exact ExitsSame.of_kept (kept_decreaseBalance (liftAccessor_ok.mp ok))
  · refine ExitsSame.foldlM (fun _ _ _ ok => ?_) ok
    unfold applySlashingPenalty at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact ExitsSame.refl _)
      | exact ExitsSame.of_kept (kept_decreaseBalance (liftAccessor_ok.mp ok))

private theorem exitsSame_eth1Reset {before : fork < .hegota}
    (ok : processEth1DataReset before state = .ok after) : ExitsSame state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact ExitsSame.of_data

private theorem exitsSame_processEffectiveBalanceUpdates
    (ok : processEffectiveBalanceUpdates state = .ok after) : ExitsSame state after := by
  refine ⟨?_⟩
  unfold processEffectiveBalanceUpdates at ok
  exact foldlM_ok_invariant (ExitsOnly state) (fun m _ _ prior step => by
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, found, _, _, _, _, set⟩ := step
    intro i v hv
    obtain ⟨u, hu, eu⟩ := prior i v hv
    obtain ⟨w, hw, ew⟩ := exitsSame_setValidatorAt found set rfl i u hu
    exact ⟨w, hw, ew.trans eu⟩) (fun _ v found => ⟨v, found, rfl⟩) ok

/-- The epoch step reaches the state after its registry updates by steps that keep an invariant.

After that state it changes no exit. -/
private theorem processEpoch_split {Inv : BeaconState preset fork → Prop} (laws : Laws config Inv)
    (holds : Inv state)
    (ok : processEpoch config checks state = .ok after) :
    ∃ registered, Inv registered ∧ ExitsSame registered after := by
  have trace := processEpoch_trace ok
  cases trace; rename_i justified justifiedOk trace
  cases trace; rename_i scored scoredOk trace
  cases trace; rename_i rewarded rewardedOk trace
  cases trace; rename_i registered registeredOk trace
  have scoredKept : Kept justified scored := by
    have edge := EpochStage.action_cases.mp scoredOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact kept_inactivity edge
    · subst scored; exact Kept.refl _
  have head : Inv registered :=
    ((keeps_of_kept laws ((kept_justification justifiedOk).trans <|
      scoredKept.trans (kept_rewards rewardedOk))).trans
      (keeps_processRegistryUpdates laws registeredOk)) holds
  refine ⟨registered, head, ?_⟩
  apply trace.transport ExitsSame ExitsSame.refl (fun one two => one.trans two)
  intro k member a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case justification | inactivity | rewards | registry =>
    simp_all [EpochStage.middleStages, EpochStage.tailStages]
  case slashings => exact exitsSame_slashings edge
  case eth1Reset =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact exitsSame_eth1Reset edge
    · subst b; exact ExitsSame.refl _
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · unfold processPendingDeposits at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact (exitsSame_processPendingDeposits ‹_›).trans ExitsSame.of_data
    · subst b; exact ExitsSame.refl _
  case pendingConsolidations =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact ExitsSame.of_data (congrArg (·.data)
        (processPendingConsolidations_kept edge).1)
    · subst b; exact ExitsSame.refl _
  case effectiveBalances => exact exitsSame_processEffectiveBalanceUpdates edge
  all_goals
    exact ExitsSame.of_data (congrArg (·.data)
      (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-! ## Exits charged in the epoch of a source state -/

/-- Two epochs after the epoch of a source state: the last exit epoch that the reserve covers. -/
private def horizon (src : BeaconState preset fork) : Nat := (getCurrentEpoch src).toNat + 2

/-- A validator without an exit in the source has, in a later state, an exit by the horizon. -/
private def departs (src m : BeaconState preset fork) (v : ValidatorIndex) : Bool :=
  (src.validators.data[v.toNat]?.any fun w => w.exitEpoch == FAR_FUTURE_EPOCH) &&
    (m.validators.data[v.toNat]?.any fun w => decide (w.exitEpoch.toNat ≤ horizon src))

/-- The validators active in the source that have no exit there and exit by the horizon later. -/
private def departed (src m : BeaconState preset fork) : Finset ValidatorIndex :=
  (getActiveValidatorIndices src (getCurrentEpoch src)).toFinset.filter
    fun v => departs src m v = true

/-- Whether a validator departs reads only the exit epochs. -/
private theorem departs_of_exitsOnly {src m t : BeaconState preset fork} (same : ExitsOnly m t)
    (size : src.validators.data.size ≤ m.validators.data.size) (v : ValidatorIndex) :
    departs src t v = departs src m v := by
  unfold departs
  cases hs : src.validators.data[v.toNat]? with
  | none => simp
  | some a =>
    have inside := (Array.getElem?_eq_some_iff.mp hs).1
    obtain ⟨u, hu⟩ : ∃ u, m.validators.data[v.toNat]? = some u :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw, ew⟩ := same _ u hu
    simp [hu, hw, ew]

/-- Steps that keep the exit epochs keep the departed validators. -/
private theorem departed_of_exitsOnly {src m t : BeaconState preset fork} (same : ExitsOnly m t)
    (size : src.validators.data.size ≤ m.validators.data.size) :
    departed src t = departed src m := by
  unfold departed
  exact Finset.filter_congr fun v _ => by rw [departs_of_exitsOnly same size v]

/-- One validator changed: only it can join the departed validators, and only by the horizon. -/
private theorem departed_set {src m t : BeaconState preset fork} {index : ValidatorIndex}
    {nv : Validator}
    (read : ∀ i : Nat, t.validators.data[i]? =
      if index.toNat = i then some nv else m.validators.data[i]?) :
    departed src t ⊆ insert index (departed src m) ∧
      (horizon src < nv.exitEpoch.toNat → departed src t ⊆ departed src m) := by
  have other : ∀ v : ValidatorIndex, v ≠ index → departs src t v = departs src m v := by
    intro v ne
    have differ : index.toNat ≠ v.toNat := fun h => ne (UInt64.toNat_inj.mp h.symm)
    unfold departs
    rw [read, ite_eq_right differ]
  constructor
  · intro v member
    by_cases same : v = index
    · exact Finset.mem_insert.mpr (.inl same)
    · apply Finset.mem_insert_of_mem
      unfold departed at member ⊢
      rw [Finset.mem_filter] at member ⊢
      exact ⟨member.1, by rw [← other v same]; exact member.2⟩
  · intro late v member
    unfold departed at member ⊢
    rw [Finset.mem_filter] at member ⊢
    refine ⟨member.1, ?_⟩
    by_cases same : v = index
    · subst same
      exfalso
      have leaves := member.2
      unfold departs at leaves
      rw [read, ite_eq_left rfl] at leaves
      simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at leaves
      omega
    · rw [← other v same]
      exact member.2

/-- One more validator adds at most its own stake. -/
private theorem stake_insert_le {ν : Type} [DecidableEq ν] (w : ν → ℕ) (a : ν) (S : Finset ν) :
    stake w (insert a S) ≤ stake w S + w a := by
  by_cases mem : a ∈ S
  · rw [Finset.insert_eq_of_mem mem]
    omega
  · unfold stake
    rw [Finset.sum_insert mem]
    omega

/-- Setting the unset exit of a validator to an epoch after the current one.

The active set and the effective balances up to the current epoch stay. -/
private theorem exitSet_facts {m q t : BeaconState preset fork} {index : ValidatorIndex}
    {v0 : Validator}
    {e w : Epoch} (found : getValidator m index = .ok v0) (far : v0.exitEpoch = FAR_FUTURE_EPOCH)
    (set : q.setValidator index { v0 with exitEpoch := e, withdrawableEpoch := w } = .ok t)
    (validators : q.validators = m.validators) (slot : q.slot = m.slot)
    (late : (getCurrentEpoch m).toNat < e.toNat) :
    getCurrentEpoch t = getCurrentEpoch m ∧ ActiveKept (getCurrentEpoch m) m t ∧
      m.validators.data.size ≤ t.validators.data.size ∧
      (∀ (i : Nat) (v : Validator), m.validators.data[i]? = some v →
        ∃ u : Validator, t.validators.data[i]? = some u ∧
          u.effectiveBalance = v.effectiveBalance) ∧
      (∀ i : Nat, t.validators.data[i]? = if index.toNat = i then
        some { v0 with exitEpoch := e, withdrawableEpoch := w } else m.validators.data[i]?) := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have oldFound : m.validators.data[index.toNat]? = some v0 := getValidator_eq_ok_iff.mp found
  have read : ∀ i : Nat, (q.putValidator index.toNat inside
      { v0 with exitEpoch := e, withdrawableEpoch := w }).validators.data[i]? =
      if index.toNat = i then some { v0 with exitEpoch := e, withdrawableEpoch := w }
      else m.validators.data[i]? := by
    intro i
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set,
      validators]
  refine ⟨?_, ?_, ?_, ?_, read⟩
  · unfold getCurrentEpoch
    exact congrArg _ slot
  · intro E le i
    simp only [isActiveAt, read]
    split
    · rename_i same
      subst same
      rw [oldFound]
      have before := UInt64.le_iff_toNat_le.mp le
      have atE : E < e := UInt64.lt_iff_toNat_lt.mpr (by omega)
      have atFar : E < FAR_FUTURE_EPOCH := by
        rw [UInt64.lt_iff_toNat_lt]
        have := e.toNat_lt
        change E.toNat < 2 ^ 64 - 1
        omega
      simp [isActiveValidator, far, atE, atFar]
    · rfl
  · simp [BeaconState.putValidator, validators]
  · intro i v hv
    rw [read]
    split
    · rename_i same
      subst same
      rw [oldFound] at hv
      cases hv
      exact ⟨_, rfl, rfl⟩
    · exact ⟨v, hv, rfl⟩

/-! ## The balance queues from Electra -/

/-- What a balance queue can still spend on exits by a horizon epoch.

An earlier open epoch means the horizon opens with a full churn; at the horizon, what is left. -/
def potential (H : Nat) (epoch : Epoch) (left : Gwei) (rate : Nat) : Nat :=
  if epoch.toNat < H then rate else if epoch.toNat = H then left.toNat else 0

/-- A call that lands by the horizon spends its amount from the potential.

A call that lands later leaves no potential. -/
private theorem potential_spend {E first R avail amount e left : UInt64} {H : Nat}
    (queued : churnQueue E first R avail amount = .ok (e, left)) (late : H ≤ first.toNat) :
    (if e.toNat ≤ H then amount.toNat else 0) + potential H e left R.toNat ≤
      potential H E avail R.toNat := by
  obtain ⟨placed, spent, _⟩ := churnQueue_spend queued
  have hmax := Base.Uint64.toNat_max E first
  have m1 : E.toNat ≤ (max E first).toNat := by rw [hmax]; exact Nat.le_max_left _ _
  have m2 : first.toNat ≤ (max E first).toNat := by rw [hmax]; exact Nat.le_max_right _ _
  have m3 : (max E first).toNat = E.toNat ∨ (max E first).toNat = first.toNat := by
    rw [hmax]; exact max_choice _ _
  have placedNat := UInt64.le_iff_toNat_le.mp placed
  generalize max E first = M at spent m1 m2 m3 placedNat
  unfold potential
  by_cases within : e.toNat ≤ H
  · have zero : e.toNat - M.toNat = 0 := by omega
    rw [zero, Nat.zero_mul, Nat.add_zero] at spent
    rw [ite_eq_left within]
    by_cases lt : E < M
    · rw [ite_eq_left lt] at spent
      have := UInt64.lt_iff_toNat_lt.mp lt
      split_ifs <;> omega
    · rw [ite_eq_right lt] at spent
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp lt)
      split_ifs <;> omega
  · rw [ite_eq_right within]
    split_ifs <;> omega

/-- The exit churn of a source state, or nothing if it cannot be read. -/
private def exitRateOf (config : Config) (src : BeaconState preset fork) : Nat :=
  ((exitChurnLimit config src).toOption.getD 0).toNat

/-- The consolidation churn of a source state, or nothing if it cannot be read. -/
private def consolidationRateOf (config : Config) (src : BeaconState preset fork) : Nat :=
  ((getConsolidationChurnLimit config src).toOption.getD 0).toNat

/-- What the exit and consolidation queues of a state can still spend by the horizon. -/
private def queuePotential (config : Config) (electra : .pectra ≤ fork)
    (src m : BeaconState preset fork) : Nat :=
  potential (horizon src) (m.earliestExitEpoch electra) (m.exitBalanceToConsume electra)
      (exitRateOf config src) +
    potential (horizon src) (m.earliestConsolidationEpoch electra)
      (m.consolidationBalanceToConsume electra) (consolidationRateOf config src)

/-- The potential of the queues reads only their fields. -/
private theorem queuePotential_congr {electra : .pectra ≤ fork} {src s t : BeaconState preset fork}
    (same : QueuesSame s t) :
    queuePotential config electra src t = queuePotential config electra src s := by
  obtain ⟨a, b, c, d⟩ := same electra
  unfold queuePotential
  rw [a, b, c, d]

/-- From Electra: the steps of the epoch of a source state, up to its registry updates.

The epoch, the churn and the source effective balances stay.

The stake that the charges moved and the potential left fit the potential of the source. -/
private structure InvE (config : Config) (electra : .pectra ≤ fork)
    (src m : BeaconState preset fork) : Prop where
  epoch : getCurrentEpoch m = getCurrentEpoch src
  size : src.validators.data.size ≤ m.validators.data.size
  exitRate : exitChurnLimit config m = exitChurnLimit config src
  consolidationRate : getConsolidationChurnLimit config m = getConsolidationChurnLimit config src
  balances : ∀ (i : Nat) (v w : Validator), src.validators.data[i]? = some v →
    m.validators.data[i]? = some w → w.effectiveBalance = v.effectiveBalance
  budget : stake (fun v => balanceAt src v.toNat) (departed src m) +
    queuePotential config electra src m ≤ queuePotential config electra src src

/-- No validator departs between a source state and itself.

An unset exit epoch is the largest epoch, after the horizon. -/
private theorem departed_self {src : BeaconState preset fork}
    (bounded : horizon src < 2 ^ 64 - 1) : departed src src = ∅ := by
  unfold departed
  apply Finset.filter_false_of_mem
  intro v _ leaves
  unfold departs at leaves
  cases hs : src.validators.data[v.toNat]? with
  | none => simp [hs] at leaves
  | some a =>
    simp only [hs, Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at leaves
    rw [leaves.1] at leaves
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega

/-- The invariant of Electra holds at the source. -/
private theorem InvE.start (electra : .pectra ≤ fork) {src : BeaconState preset fork}
    (bounded : horizon src < 2 ^ 64 - 1) : InvE config electra src src where
  epoch := rfl
  size := Nat.le_refl _
  exitRate := rfl
  consolidationRate := rfl
  balances _ _ _ found read := by rw [found] at read; cases read; rfl
  budget := by rw [departed_self bounded]; simp

/-- A source weight is at most the effective balance it reads at a state that keeps it. -/
private theorem balanceAt_le {src m : BeaconState preset fork} {index : ValidatorIndex}
    {v0 : Validator}
    (balances : ∀ (i : Nat) (v w : Validator), src.validators.data[i]? = some v →
      m.validators.data[i]? = some w → w.effectiveBalance = v.effectiveBalance)
    (found : getValidator m index = .ok v0) :
    balanceAt src index.toNat ≤ v0.effectiveBalance.toNat := by
  unfold balanceAt
  cases hs : src.validators.data[index.toNat]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    rw [balances _ v v0 hs (getValidator_eq_ok_iff.mp found)]

/-- From Electra, every step of the epoch of the source keeps its invariant.

An exit or a consolidation that lands by the horizon spends its effective balance from its queue.

The seed lookahead puts the first epoch of a charge at the horizon or later. -/
private theorem lawsE (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat) (electra : .pectra ≤ fork)
    (src : BeaconState preset fork) : Laws config (InvE config electra src) where
  kept {s t} kept inv := by
    refine ⟨kept.epoch.trans inv.epoch, Nat.le_trans inv.size kept.size_le,
      (exitChurn_congr kept.totalActiveBalance).trans inv.exitRate,
      (consolidationChurn_congr kept.totalActiveBalance).trans inv.consolidationRate, ?_, ?_⟩
    · intro i v w hv hw
      obtain ⟨u, hu⟩ : ∃ u, s.validators.data[i]? = some u :=
        ⟨_, Array.getElem?_eq_getElem
          (by have := (Array.getElem?_eq_some_iff.mp hv).1; have := inv.size; omega)⟩
      obtain ⟨w', hw', _, bw⟩ := kept.old i u hu
      rw [hw] at hw'
      cases hw'
      exact bw.trans (inv.balances i v u hv hu)
    · rw [departed_of_exitsOnly (ExitsSame.of_kept kept).1 inv.size,
        queuePotential_congr kept.queues]
      exact inv.budget
  exit {s t index} ok inv := by
    obtain ⟨v0, found, ⟨_, rfl⟩ | ⟨far, q, e, w, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
    · exact inv
    unfold exitQueue at queue
    simp only [electra, ↓reduceDIte] at queue
    have charged := queue
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
      Except.pure, Except.ok.injEq] at queue
    obtain ⟨first, firstOk, rate, rateOk, ⟨placed, left⟩, queued, final⟩ := queue
    simp only [Prod.mk.injEq] at final
    obtain ⟨rfl, rfl⟩ := final
    have firstNat := (computeActivationExitEpoch_ok_iff.mp firstOk).2
    have atLeast := UInt64.le_iff_toNat_le.mp
      (computeExitEpochAndUpdateChurn_first firstOk charged).1
    obtain ⟨epochT, activeT, sizeT, balanceT, read⟩ :=
      exitSet_facts found far set rfl rfl (by omega)
    have total := totalActiveBalance_eq epochT activeT sizeT balanceT
    have horizonEq : horizon src = (getCurrentEpoch s).toNat + 2 := by
      unfold horizon; rw [inv.epoch]
    have rateEq : exitRateOf config src = rate.toNat := by
      unfold exitRateOf; rw [← inv.exitRate, rateOk]; rfl
    have spend := potential_spend queued (H := horizon src) (by omega)
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    refine ⟨epochT.trans inv.epoch, Nat.le_trans inv.size sizeT,
      (exitChurn_congr total).trans inv.exitRate,
      (consolidationChurn_congr total).trans inv.consolidationRate, ?_, ?_⟩
    · intro i v u hv hu
      rw [read] at hu
      split at hu
      · rename_i same
        subst same
        cases hu
        exact inv.balances _ v v0 hv (getValidator_eq_ok_iff.mp found)
      · exact inv.balances i v u hv hu
    · obtain ⟨wide, narrow⟩ := departed_set (src := src) read
      have weight := balanceAt_le inv.balances found
      have budget := inv.budget
      unfold queuePotential at budget ⊢
      rw [← rateEq] at spend
      by_cases within : placed.toNat ≤ horizon src
      · rw [ite_eq_left within] at spend
        have grow := (stake_mono (w := fun v => balanceAt src v.toNat) wide).trans
          (stake_insert_le _ index _)
        change _ + (potential (horizon src) placed left (exitRateOf config src) +
          potential (horizon src) (s.earliestConsolidationEpoch electra)
            (s.consolidationBalanceToConsume electra) (consolidationRateOf config src)) ≤ _
        omega
      · rw [ite_eq_right within] at spend
        have same := stake_mono (w := fun v => balanceAt src v.toNat)
          (narrow (by show horizon src < placed.toNat; omega))
        change _ + (potential (horizon src) placed left (exitRateOf config src) +
          potential (horizon src) (s.earliestConsolidationEpoch electra)
            (s.consolidationBalanceToConsume electra) (consolidationRateOf config src)) ≤ _
        omega
  churn {s t electra' amount e} ok inv := by
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
      Except.pure, Except.ok.injEq] at ok
    obtain ⟨first, firstOk, rate, rateOk, ⟨placed, left⟩, queued, final⟩ := ok
    simp only [Prod.mk.injEq] at final
    obtain ⟨tEq, rfl⟩ := final
    have firstNat := (computeActivationExitEpoch_ok_iff.mp firstOk).2
    have horizonEq : horizon src = (getCurrentEpoch s).toNat + 2 := by
      unfold horizon; rw [inv.epoch]
    have rateEq : exitRateOf config src = rate.toNat := by
      unfold exitRateOf; rw [← inv.exitRate, rateOk]; rfl
    have spend := potential_spend queued (H := horizon src) (by omega)
    rw [← rateEq] at spend
    have budget := inv.budget
    have dep : departed src t = departed src s :=
      departed_of_exitsOnly (ExitsSame.of_data
        (congrArg (·.data) (by rw [← tEq] : t.validators = s.validators))).1 inv.size
    have qp : queuePotential config electra src t =
        potential (horizon src) placed left (exitRateOf config src) +
          potential (horizon src) (s.earliestConsolidationEpoch electra)
            (s.consolidationBalanceToConsume electra) (consolidationRateOf config src) := by
      rw [← tEq]; rfl
    subst tEq
    refine ⟨inv.epoch, inv.size, inv.exitRate, inv.consolidationRate, inv.balances, ?_⟩
    rw [dep, qp]
    unfold queuePotential at budget ⊢
    split at spend <;> omega
  consolidate {s t electra' sourceIndex targetIndex source} found far ok inv := by
    have sameProof : electra = electra' := rfl
    subst sameProof
    simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure,
      Except.pure] at ok
    obtain ⟨⟨churned, e⟩, churn, w, _, r, set, _, _, ok⟩ := ok
    simp only [Except.ok.injEq] at ok
    have charged := churn
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq] at churn
    obtain ⟨first, firstOk, rate, rateOk, ⟨placed, left⟩, queued, final⟩ := churn
    simp only [Prod.mk.injEq] at final
    obtain ⟨rfl, rfl⟩ := final
    have firstNat := (computeActivationExitEpoch_ok_iff.mp firstOk).2
    have atLeast := UInt64.le_iff_toNat_le.mp
      (computeConsolidationEpochAndUpdateChurn_first firstOk charged).1
    have read0 : getValidator s sourceIndex = .ok source := getValidator_eq_ok_iff.mpr found
    obtain ⟨epochR, activeR, sizeR, balanceR, readR⟩ :=
      exitSet_facts read0 far set rfl rfl (by show (getCurrentEpoch s).toNat < placed.toNat; omega)
    have tVal : t.validators = r.validators := by rw [← ok]
    have tSlot : t.slot = r.slot := by rw [← ok]
    have epochT : getCurrentEpoch t = getCurrentEpoch s := by
      rw [← epochR]; unfold getCurrentEpoch; rw [tSlot]
    have activeT : ActiveKept (getCurrentEpoch s) s t := fun E le i => by
      rw [← activeR E le i]; simp only [isActiveAt, tVal]
    have sizeT : s.validators.data.size ≤ t.validators.data.size := by rw [tVal]; exact sizeR
    have balanceT : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
        ∃ u : Validator, t.validators.data[i]? = some u ∧
          u.effectiveBalance = v.effectiveBalance := by
      rw [tVal]; exact balanceR
    have read : ∀ i : Nat, t.validators.data[i]? = if sourceIndex.toNat = i then
        some { source with exitEpoch := placed, withdrawableEpoch := w }
        else s.validators.data[i]? := by
      rw [tVal]; exact readR
    have qp : queuePotential config electra src t =
        potential (horizon src) (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
          (exitRateOf config src) +
        potential (horizon src) placed left (consolidationRateOf config src) := by
      rw [← ok]
      obtain ⟨_, rfl⟩ := setValidator_ok set
      rfl
    have total := totalActiveBalance_eq epochT activeT sizeT balanceT
    have horizonEq : horizon src = (getCurrentEpoch s).toNat + 2 := by
      unfold horizon; rw [inv.epoch]
    have rateEq : consolidationRateOf config src = rate.toNat := by
      unfold consolidationRateOf; rw [← inv.consolidationRate, rateOk]; rfl
    have spend := potential_spend queued (H := horizon src) (by omega)
    refine ⟨epochT.trans inv.epoch, Nat.le_trans inv.size sizeT,
      (exitChurn_congr total).trans inv.exitRate,
      (consolidationChurn_congr total).trans inv.consolidationRate, ?_, ?_⟩
    · intro i v u hv hu
      rw [read] at hu
      split at hu
      · rename_i same
        subst same
        cases hu
        exact inv.balances _ v source hv found
      · exact inv.balances i v u hv hu
    · obtain ⟨wide, narrow⟩ := departed_set (src := src) read
      have weight := balanceAt_le inv.balances read0
      have budget := inv.budget
      rw [qp]
      unfold queuePotential at budget ⊢
      rw [← rateEq] at spend
      by_cases within : placed.toNat ≤ horizon src
      · rw [ite_eq_left within] at spend
        have grow := (stake_mono (w := fun v => balanceAt src v.toNat) wide).trans
          (stake_insert_le _ sourceIndex _)
        omega
      · rw [ite_eq_right within] at spend
        have same := stake_mono (w := fun v => balanceAt src v.toNat)
          (narrow (by show horizon src < placed.toNat; omega))
        omega

/-- From Electra: the charges of the epoch of the source move at most the churn of its queues. -/
private theorem InvE.departed_le {electra : .pectra ≤ fork} {src m : BeaconState preset fork}
    (inv : InvE config electra src m) :
    stake (fun v => balanceAt src v.toNat) (departed src m) ≤
      queuePotential config electra src src := by
  have budget := inv.budget
  omega

/-! ## The exit queue before Electra -/

/-- The exit epoch two epochs after the source. -/
private def cohortEpoch (src : BeaconState preset fork) : Epoch := UInt64.ofNat (horizon src)

/-- The positions of a registry whose exit epoch is two epochs after the source. -/
private def cohort (src m : BeaconState preset fork) : Finset Nat :=
  (Finset.range m.validators.data.size).filter fun i =>
    (m.validators.data[i]?.any fun w => w.exitEpoch == cohortEpoch src) = true

/-- The validators of a list that pass a test are as many as their positions. -/
private theorem filter_length_eq_card (p : Validator → Bool) :
    ∀ l : List Validator, (l.filter p).length =
      ((Finset.range l.length).filter fun i => (l[i]?.any p) = true).card := by
  intro l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    have inner : ((Finset.range l.length).filter fun i => ((l ++ [x])[i]?.any p) = true) =
        (Finset.range l.length).filter fun i => (l[i]?.any p) = true :=
      Finset.filter_congr fun i member => by
        rw [List.getElem?_append_left (Finset.mem_range.mp member)]
    have notMem : l.length ∉ (Finset.range l.length).filter fun i => (l[i]?.any p) = true := by
      simp
    rw [List.filter_append, List.length_append, ih, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert, inner]
    have last : ((l ++ [x])[l.length]?.any p) = p x := by simp
    rw [last]
    cases hp : p x
    · simp [hp]
    · simp [hp, Finset.card_insert_of_notMem notMem]

/-- The cohort of the horizon, counted as the exit queue counts it. -/
private theorem cohort_card (src m : BeaconState preset fork) :
    (m.validators.data.toList.filter (·.exitEpoch == cohortEpoch src)).length =
      (cohort src m).card := by
  rw [filter_length_eq_card]
  unfold cohort
  simp only [Array.length_toList, Array.getElem?_toList]

/-- Before Electra: the epoch of a source state, with the exits charged in it. -/
private structure InvP (config : Config) (src m : BeaconState preset fork) : Prop where
  epoch : getCurrentEpoch m = getCurrentEpoch src
  size : src.validators.data.size ≤ m.validators.data.size
  limit : getValidatorChurnLimit config m = getValidatorChurnLimit config src
  assigned : ∀ (i : Nat) (v w : Validator), src.validators.data[i]? = some v →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH → m.validators.data[i]? = some w → w.exitEpoch = v.exitEpoch
  late : ∀ (i : Nat) (v w : Validator), src.validators.data[i]? = some v →
    v.exitEpoch = FAR_FUTURE_EPOCH → m.validators.data[i]? = some w →
    w.exitEpoch ≠ FAR_FUTURE_EPOCH → horizon src ≤ w.exitEpoch.toNat
  cap : (cohort src m).card ≤
    max (cohort src src).card (max 1 (getValidatorChurnLimit config src).toNat)

/-- The invariant before Electra holds at the source. -/
private theorem InvP.start (src : BeaconState preset fork) : InvP config src src where
  epoch := rfl
  size := Nat.le_refl _
  limit := rfl
  assigned _ _ _ found _ read := by rw [found] at read; cases read; rfl
  late _ _ _ found far read assigned := by
    rw [found] at read; cases read; exact absurd far assigned
  cap := Nat.le_max_left _ _

/-- The horizon fits in an epoch. -/
private theorem cohortEpoch_toNat {src : BeaconState preset fork}
    (bounded : horizon src < 2 ^ 64 - 1) :
    (cohortEpoch src).toNat = horizon src := by
  unfold cohortEpoch
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- Before Electra, every step of the epoch of the source keeps its invariant.

An exit that lands at the horizon finds fewer exits there than the churn limit, or none. -/
private theorem lawsP (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat) (early : fork < .pectra)
    (src : BeaconState preset fork) (bounded : horizon src < 2 ^ 64 - 1) :
    Laws config (InvP config src) where
  kept {s t} kept inv := by
    refine ⟨kept.epoch.trans inv.epoch, Nat.le_trans inv.size kept.size_le,
      (validatorChurn_congr kept.epoch kept.active).trans inv.limit, ?_, ?_, ?_⟩
    · intro i v w hv assigned hw
      obtain ⟨u, hu⟩ : ∃ u, s.validators.data[i]? = some u :=
        ⟨_, Array.getElem?_eq_getElem
          (by have := (Array.getElem?_eq_some_iff.mp hv).1; have := inv.size; omega)⟩
      obtain ⟨w', hw', ew, _⟩ := kept.old i u hu
      rw [hw] at hw'
      cases hw'
      exact ew.trans (inv.assigned i v u hv assigned hu)
    · intro i v w hv far hw assigned
      obtain ⟨u, hu⟩ : ∃ u, s.validators.data[i]? = some u :=
        ⟨_, Array.getElem?_eq_getElem
          (by have := (Array.getElem?_eq_some_iff.mp hv).1; have := inv.size; omega)⟩
      obtain ⟨w', hw', ew, _⟩ := kept.old i u hu
      rw [hw] at hw'
      cases hw'
      rw [ew] at assigned ⊢
      exact inv.late i v u hv far hu assigned
    · have same : cohort src t = cohort src s := by
        ext i
        unfold cohort
        simp only [Finset.mem_filter, Finset.mem_range]
        by_cases old : i < s.validators.data.size
        · obtain ⟨w', hw', ew, _⟩ := kept.old i _ (Array.getElem?_eq_getElem old)
          have inside := (Array.getElem?_eq_some_iff.mp hw').1
          rw [hw', Array.getElem?_eq_getElem old]
          simp only [Option.any_some, ew, inside, old, true_and]
        · constructor
          · rintro ⟨inside, hit⟩
            exfalso
            obtain ⟨w, hw⟩ : ∃ w, t.validators.data[i]? = some w :=
              ⟨_, Array.getElem?_eq_getElem inside⟩
            rw [hw] at hit
            have far := kept.new i w (by omega) hw
            have := cohortEpoch_toNat bounded
            simp only [Option.any_some, beq_iff_eq] at hit
            rw [far] at hit
            have := congrArg UInt64.toNat hit
            have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
            omega
          · rintro ⟨inside, _⟩
            exact absurd inside old
      rw [same]
      exact inv.cap
  exit {s t index} ok inv := by
    obtain ⟨v0, found, ⟨_, rfl⟩ | ⟨far, q, e, w, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
    · exact inv
    have eLate := exitQueue_lt queue
    have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
    unfold exitQueue at queue
    simp only [notElectra, ↓reduceDIte] at queue
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨e, eOk, rfl, rfl⟩ := queue
    obtain ⟨epochT, activeT, sizeT, _, read⟩ := exitSet_facts found far set rfl rfl (by omega)
    have v0Found := getValidator_eq_ok_iff.mp found
    have horizonEq : horizon src = (getCurrentEpoch s).toNat + 2 := by
      unfold horizon; rw [inv.epoch]
    refine ⟨epochT.trans inv.epoch, Nat.le_trans inv.size sizeT,
      (validatorChurn_congr epochT activeT).trans inv.limit, ?_, ?_, ?_⟩
    · intro i v u hv assigned hu
      rw [read] at hu
      split at hu
      · rename_i same
        subst same
        exact absurd ((inv.assigned _ v v0 hv assigned v0Found).symm.trans far) assigned
      · exact inv.assigned i v u hv assigned hu
    · intro i v u hv vfar hu assigned
      rw [read] at hu
      split at hu
      · cases hu
        change horizon src ≤ e.toNat
        omega
      · exact inv.late i v u hv vfar hu assigned
    · have hits : ∀ i, i ∈ cohort src t → i = index.toNat ∨ i ∈ cohort src s := by
        intro i member
        unfold cohort at member ⊢
        simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
        rw [read] at member
        by_cases same : index.toNat = i
        · exact .inl same.symm
        · rw [ite_eq_right same] at member
          refine .inr ⟨?_, member.2⟩
          obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_any member.2)
          exact (Array.getElem?_eq_some_iff.mp hu).1
      have farHit : ¬ (s.validators.data[index.toNat]?.any
          fun w => w.exitEpoch == cohortEpoch src) = true := by
        rw [v0Found]
        simp only [Option.any_some, beq_iff_eq, far]
        intro equal
        have := congrArg UInt64.toNat equal
        rw [cohortEpoch_toNat bounded] at this
        have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        omega
      by_cases landed : e = cohortEpoch src
      · have churn := exitQueueEpoch_churn eOk (by
          rw [landed]
          intro equal
          have := congrArg UInt64.toNat equal
          rw [cohortEpoch_toNat bounded] at this
          have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
          omega)
        rw [landed, cohort_card, inv.limit] at churn
        have subset : cohort src t ⊆ insert index.toNat (cohort src s) := by
          intro i member
          rcases hits i member with same | old
          · exact Finset.mem_insert.mpr (.inl same)
          · exact Finset.mem_insert_of_mem old
        have := (Finset.card_le_card subset).trans (Finset.card_insert_le _ _)
        omega
      · have subset : cohort src t ⊆ cohort src s := by
          intro i member
          rcases hits i member with same | old
          · subst same
            exfalso
            unfold cohort at member
            simp only [Finset.mem_filter, Finset.mem_range] at member
            rw [read, ite_eq_left rfl] at member
            simp only [Option.any_some, beq_iff_eq] at member
            exact landed member.2
          · exact old
        exact (Finset.card_le_card subset).trans inv.cap
  churn {_ _ electra'} _ _ := absurd electra' (Nat.not_le_of_lt early)
  consolidate {_ _ electra'} _ _ _ _ := absurd electra' (Nat.not_le_of_lt early)

/-- Before Electra: the charges of the epoch of the source are at most one churn of exits. -/
private theorem InvP.departed_card {src m : BeaconState preset fork} (inv : InvP config src m)
    (bounded : horizon src < 2 ^ 64 - 1) :
    (departed src m).card ≤ max 1 (getValidatorChurnLimit config src).toNat := by
  have images : (departed src m).image UInt64.toNat ∪ cohort src src ⊆ cohort src m := by
    intro i member
    rcases Finset.mem_union.mp member with left | right
    · obtain ⟨v, mem, rfl⟩ := Finset.mem_image.mp left
      unfold departed at mem
      rw [Finset.mem_filter, List.mem_toFinset] at mem
      obtain ⟨active, leaves⟩ := mem
      unfold departs at leaves
      cases hs : src.validators.data[v.toNat]? with
      | none => simp [hs] at leaves
      | some a =>
        cases hm : m.validators.data[v.toNat]? with
        | none => simp [hs, hm] at leaves
        | some b =>
          simp only [hs, hm, Option.any_some, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq] at leaves
          have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
          have notFar : b.exitEpoch ≠ FAR_FUTURE_EPOCH := by
            intro equal; rw [equal] at leaves; omega
          have atLeast := inv.late _ a b hs leaves.1 hm notFar
          unfold cohort
          simp only [Finset.mem_filter, Finset.mem_range, hm, Option.any_some, beq_iff_eq]
          refine ⟨(Array.getElem?_eq_some_iff.mp hm).1, ?_⟩
          apply UInt64.toNat_inj.mp
          rw [cohortEpoch_toNat bounded]
          omega
    · unfold cohort at right ⊢
      simp only [Finset.mem_filter, Finset.mem_range] at right ⊢
      obtain ⟨inside, hit⟩ := right
      obtain ⟨a, ha⟩ : ∃ a, src.validators.data[i]? = some a :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      rw [ha] at hit
      simp only [Option.any_some, beq_iff_eq] at hit
      have assigned : a.exitEpoch ≠ FAR_FUTURE_EPOCH := by
        rw [hit]
        intro equal
        have := congrArg UInt64.toNat equal
        rw [cohortEpoch_toNat bounded] at this
        have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        omega
      obtain ⟨b, hb⟩ : ∃ b, m.validators.data[i]? = some b :=
        ⟨_, Array.getElem?_eq_getElem (by have := inv.size; omega)⟩
      refine ⟨(Array.getElem?_eq_some_iff.mp hb).1, ?_⟩
      rw [hb]
      simp only [Option.any_some, beq_iff_eq]
      rw [inv.assigned i a b ha assigned hb, hit]
  have disjoint : Disjoint ((departed src m).image UInt64.toNat) (cohort src src) := by
    rw [Finset.disjoint_left]
    intro i left right
    obtain ⟨v, member, rfl⟩ := Finset.mem_image.mp left
    unfold departed at member
    rw [Finset.mem_filter] at member
    have leaves := member.2
    unfold departs at leaves
    unfold cohort at right
    simp only [Finset.mem_filter, Finset.mem_range] at right
    cases hs : src.validators.data[v.toNat]? with
    | none => simp [hs] at leaves
    | some a =>
      simp only [hs, Option.any_some, Bool.and_eq_true, beq_iff_eq] at leaves right
      rw [leaves.1] at right
      have := congrArg UInt64.toNat right.2
      rw [cohortEpoch_toNat bounded] at this
      have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
  have injective : ((departed src m).image UInt64.toNat).card = (departed src m).card :=
    Finset.card_image_of_injective _ (fun a b h => UInt64.toNat_inj.mp h)
  have counted := Finset.card_le_card images
  rw [Finset.card_union_of_disjoint disjoint, injective] at counted
  have := inv.cap
  omega

/-! ## Runs within the epoch of the source -/

/-- A state of the fork of the source on which an invariant holds. -/
private def InvF (Inv : BeaconState preset fork → Prop) (x : ForkedBeaconState preset) : Prop :=
  ∃ s : BeaconState preset fork, x = ⟨fork, s⟩ ∧ Inv s

/-- A slot step moves the epoch on by one exactly when it reaches the first slot of an epoch. -/
private theorem epoch_next {f g : Fork} {s : BeaconState preset f} {a : BeaconState preset g}
    {next : Slot}
    (sum : next.toNat = s.slot.toNat + 1) (slot : a.slot = next) :
    (getCurrentEpoch a).toNat =
      (getCurrentEpoch s).toNat + if next % preset.SLOTS_PER_EPOCH = 0 then 1 else 0 := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot]
  by_cases h : next % preset.SLOTS_PER_EPOCH = 0
  · simpa only [h, ↓reduceIte] using nextSlot_epoch_of_boundary sum h
  · simpa only [h, ↓reduceIte, Nat.add_zero] using nextSlot_epoch_of_inside sum h

/-- The upgrades of a slot keep its slot and the activity up to its fixed epoch. -/
private theorem upgrades_kept {a : BeaconState preset fork} {z : ForkedBeaconState preset}
    (upgrades : processUpgrades config checks ⟨fork, a⟩ = .ok z) :
    z.state.slot = a.slot ∧ ActiveKept (activityFixedEpoch a) a z.state :=
  processUpgrades_induction
    (property := fun p => p.state.slot = a.slot ∧ ActiveKept (activityFixedEpoch a) a p.state)
    (fun {pre} _ ⟨slot, active⟩ stepOk => by
      have frame := upgradeFrame_upgradeNext stepOk
      have epoch : activityFixedEpoch pre.state = activityFixedEpoch a :=
        activityFixedEpoch_eq_of_slot slot
      exact ⟨frame.slot.trans slot, active.trans (epoch ▸ activeKept_upgradeNext stepOk)⟩)
    ⟨rfl, ActiveKept.refl _ _⟩ upgrades

/-- A step that stays in the epoch keeps the fork and the invariant. -/
private theorem step_within {Inv : BeaconState preset fork → Prop} (laws : Laws config Inv)
    (early : fork < .glamsterdam) {x z : ForkedBeaconState preset}
    (step : Step config checks x z) (holds : InvF Inv x)
    (same : getCurrentEpoch z.state = getCurrentEpoch x.state) : InvF Inv z := by
  obtain ⟨s, rfl, inv⟩ := holds
  cases step with
  | block engine signed due ok =>
    exact ⟨_, rfl, keeps_processBlock laws early (applySignedBlock_ok ok).2.1 inv⟩
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slotOk
    have cachedSlot : cached.slot = s.slot := processSlot_slot cachedOk
    have zSlot := (upgrades_kept upgrades).1
    have moved := epoch_next (s := s) (next := next) (a := z.state) sum zSlot
    have notLast : ¬ next % preset.SLOTS_PER_EPOCH = 0 := by
      intro last
      rw [ite_eq_left last, same] at moved
      dsimp only at moved
      omega
    unfold epochIfLast at epochedOk
    rw [ite_eq_right notLast] at epochedOk
    cases epochedOk
    rw [processUpgrades_of_not_due (upgradeDue_of_not_first notLast)] at upgrades
    cases upgrades
    have epochEq : getCurrentEpoch ({ cached with slot := next } : BeaconState preset fork) =
        getCurrentEpoch cached := by
      have moved' := epoch_next (s := s) (next := next) (a := { cached with slot := next }) sum rfl
      rw [ite_eq_right notLast] at moved'
      apply UInt64.toNat_inj.mp
      rw [moved', getCurrentEpoch_toNat, getCurrentEpoch_toNat, cachedSlot]
      simp
    exact ⟨_, rfl, laws.kept (Kept.of_epoch (s := cached) rfl epochEq)
      (laws.kept (kept_processSlot cachedOk) inv)⟩

/-- A run that ends in the epoch of its start keeps the fork and the invariant. -/
private theorem run_within {Inv : BeaconState preset fork → Prop} (laws : Laws config Inv)
    (early : fork < .glamsterdam) {x u : ForkedBeaconState preset}
    (pre : Run config checks x u) (holds : InvF Inv x)
    (same : getCurrentEpoch u.state = getCurrentEpoch x.state) : InvF Inv u := by
  induction pre with
  | nil => exact holds
  | @snoc middle last pre step ih =>
    have first := currentEpoch_le_of_chainSteps pre.chainSteps
    have second := step.chainStep.currentEpoch_le
    have midSame : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      UInt64.le_antisymm (same ▸ second) first
    exact step_within laws early step (ih midSame) (same.trans midSame.symm)

/-- A run that leaves the epoch of its start has a first step that leaves it. -/
private theorem run_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (leaves : getCurrentEpoch y.state ≠ getCurrentEpoch x.state) :
    ∃ u z, ∃ _ : Run config checks x u, ∃ _ : Step config checks u z, ∃ _ : Run config checks z y,
      getCurrentEpoch u.state = getCurrentEpoch x.state ∧
        getCurrentEpoch z.state ≠ getCurrentEpoch x.state := by
  induction tail with
  | nil => exact absurd rfl leaves
  | @snoc middle last pre step ih =>
    by_cases mid : getCurrentEpoch middle.state = getCurrentEpoch x.state
    · exact ⟨middle, last, pre, step, .nil, mid, leaves⟩
    · obtain ⟨u, z, pre', step', rest, first, second⟩ := ih mid
      exact ⟨u, z, pre', step', rest.snoc step, first, second⟩

/-- The step that leaves the epoch of the source runs the epoch step on a state of that epoch.

Its registry updates end the charges of the epoch, and no later step of it changes an exit. -/
private theorem crossing {Inv : BeaconState preset fork → Prop} (laws : Laws config Inv)
    {s : BeaconState preset fork} {z : ForkedBeaconState preset}
    (step : Step config checks ⟨fork, s⟩ z) (holds : Inv s)
    (leaves : getCurrentEpoch z.state ≠ getCurrentEpoch s) :
    ∃ a r : BeaconState preset fork, Inv r ∧ ExitsSame r a ∧
      (getCurrentEpoch a).toNat = (getCurrentEpoch s).toNat + 1 ∧
      ActiveKept (activityFixedEpoch s) s a ∧ ActiveKept (activityFixedEpoch a) a z.state ∧
      activityFixedEpoch z.state = activityFixedEpoch a := by
  cases step with
  | block engine signed due ok =>
    exfalso
    apply leaves
    unfold getCurrentEpoch
    rw [(frame_processBlock (applySignedBlock_ok ok).2.1).slot]
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have activeSA := activeKept_advanceSlot slotOk
    obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slotOk
    obtain ⟨zSlot, activeAZ⟩ := upgrades_kept upgrades
    have moved := epoch_next (s := s) (next := next) (a := z.state) sum zSlot
    have last : next % preset.SLOTS_PER_EPOCH = 0 := by
      by_contra notLast
      rw [ite_eq_right notLast] at moved
      exact leaves (UInt64.toNat_inj.mp (by omega))
    unfold epochIfLast at epochedOk
    rw [ite_eq_left last] at epochedOk
    obtain ⟨r, invR, exitsR⟩ := processEpoch_split laws
      (laws.kept (kept_processSlot cachedOk) holds) epochedOk
    have movedA := epoch_next (s := s) (next := next) (a := { epoched with slot := next }) sum rfl
    rw [ite_eq_left last] at movedA
    exact ⟨_, r, invR, exitsR.trans ExitsSame.of_data, movedA, activeSA, activeAZ,
      activityFixedEpoch_eq_of_slot zSlot⟩

/-! ## The stake that leaves the active set -/

/-- The validators active in the epoch of a state. -/
def activeSet {f : Fork} (s : BeaconState preset f) : Finset ValidatorIndex :=
  (getActiveValidatorIndices s (getCurrentEpoch s)).toFinset

/-- The validators active in a source state whose exit is set by two epochs later. -/
private def scheduled (src : BeaconState preset fork) : Finset ValidatorIndex :=
  {v ∈ activeSet src | (src.validators.data[v.toNat]?).any fun validator =>
    validator.exitEpoch.toNat ≤ (getCurrentEpoch src).toNat + 2}

/-- A validator is in the active set exactly when its position is active. -/
private theorem mem_activeSet {f : Fork} {s : BeaconState preset f} (early : f < .glamsterdam)
    {v : ValidatorIndex} :
    v ∈ activeSet s ↔ isActiveAt s (getCurrentEpoch s) v.toNat = true := by
  unfold activeSet
  rw [List.mem_toFinset, mem_getActiveValidatorIndices (s.validators.bound early),
    isActiveAt_eq_true_iff]

/-- An epoch within the seed lookahead of the current one is at most the fixed epoch. -/
theorem fixed_ge {f : Fork} (s : BeaconState preset f) {E : Epoch} {n : Nat}
    (le : E.toNat ≤ (getCurrentEpoch s).toNat + n) (small : n ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (bounded : E.toNat < 2 ^ 64 - 1) : E ≤ activityFixedEpoch s := by
  rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
  exact Nat.le_min.mpr ⟨by omega, by omega⟩

/-- A validator active in the source and not in a queried epoch by two epochs later departs.

The queried epoch is read in a later state, and is no earlier than the epoch of that state.

The validator was scheduled to exit by then, or a queue call charged its exit.

That call occurred in the source's epoch.

Those calls are the ones that an invariant of the epoch counts. -/
private theorem departing_subset {Inv : BeaconState preset fork → Prop} (laws : Laws config Inv)
    {y : ForkedBeaconState preset} {source : BeaconState preset fork}
    (tail : Run config checks ⟨fork, source⟩ y) (holds : Inv source)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat) (preGloas : y.fork < .glamsterdam)
    {Ep : Epoch} (later : getCurrentEpoch y.state ≤ Ep)
    (near : Ep.toNat ≤ (getCurrentEpoch source).toNat + 2)
    (bounded : horizon source < 2 ^ 64 - 1) :
    ∃ r a : BeaconState preset fork, Inv r ∧ ExitsSame r a ∧
      {v ∈ activeSet source | isActiveAt y.state Ep v.toNat = false} ⊆
        scheduled source ∪ departed source a := by
  have early : fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) preGloas
  have forward : (getCurrentEpoch source).toNat ≤ (getCurrentEpoch y.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have laterNat : (getCurrentEpoch y.state).toNat ≤ Ep.toNat := UInt64.le_iff_toNat_le.mp later
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  unfold horizon at bounded
  -- A source validator inactive at the queried epoch later has an exit by that epoch.
  have exitBy : ∀ v ∈ activeSet source, isActiveAt y.state Ep v.toNat = false →
      ∀ a, source.validators.data[v.toNat]? = some a →
        ∃ b, y.state.validators.data[v.toNat]? = some b ∧ b.exitEpoch.toNat ≤ Ep.toNat ∧
          (a.exitEpoch ≠ FAR_FUTURE_EPOCH → b.exitEpoch = a.exitEpoch) := by
    intro v active absent a found
    obtain ⟨b, hb, life⟩ := tail.registryLifecycle.validators v.toNat a found
    obtain ⟨a', ha', act⟩ := isActiveAt_eq_true_iff.mp ((mem_activeSet early).mp active)
    rw [found] at ha'
    cases ha'
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt] at act
    have activation : a.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      have := a.exitEpoch.toNat_lt
      rw [far] at act
      omega
    have actEq := life.activationEpoch activation
    have inactive : isActiveValidator b Ep = false := by
      simpa only [isActiveAt, hb, Option.map_some, Option.getD_some] using absent
    simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, actEq] at inactive
    exact ⟨b, hb, by omega, life.exitEpoch⟩
  -- A source validator with an exit already set leaves only if that exit is by the horizon.
  have scheduledCase : ∀ v ∈ activeSet source, isActiveAt y.state Ep v.toNat = false →
      ∀ a, source.validators.data[v.toNat]? = some a → a.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v ∈ scheduled source := by
    intro v active absent a found assigned
    obtain ⟨b, _, within, exitEq⟩ := exitBy v active absent a found
    rw [exitEq assigned] at within
    unfold scheduled
    rw [Finset.mem_filter]
    refine ⟨active, ?_⟩
    simp only [found, Option.any_some, decide_eq_true_eq]
    omega
  by_cases stays : Ep.toNat ≤ (getCurrentEpoch source).toNat + 1
  · refine ⟨source, source, holds, ExitsSame.refl _, ?_⟩
    intro v member
    rw [Finset.mem_filter] at member
    obtain ⟨active, absent⟩ := member
    obtain ⟨a, found, act⟩ := isActiveAt_eq_true_iff.mp ((mem_activeSet early).mp active)
    by_cases assigned : a.exitEpoch = FAR_FUTURE_EPOCH
    · exfalso
      have kept := activeKept_of_chainSteps tail.chainSteps Ep
        (fixed_ge source (n := 1) (by omega) lookahead (by omega)) v.toNat
      rw [kept] at absent
      simp only [isActiveAt, found, Option.map_some, Option.getD_some, isActiveValidator,
        Bool.and_eq_false_iff, Bool.and_eq_true, decide_eq_false_iff_not, decide_eq_true_eq,
        UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, assigned] at absent act
      omega
    · exact Finset.mem_union_left _ (scheduledCase v active absent a found assigned)
  by_cases same : getCurrentEpoch y.state = getCurrentEpoch source
  · -- The run stays in the epoch of the source, so the invariant holds at its end.
    obtain ⟨t, rfl, invT⟩ := run_within laws early tail ⟨source, rfl, holds⟩ same
    refine ⟨t, t, invT, ExitsSame.refl _, ?_⟩
    intro v member
    rw [Finset.mem_filter] at member
    obtain ⟨active, absent⟩ := member
    obtain ⟨a0, found, _⟩ := isActiveAt_eq_true_iff.mp ((mem_activeSet early).mp active)
    by_cases assigned : a0.exitEpoch = FAR_FUTURE_EPOCH
    swap
    · exact Finset.mem_union_left _ (scheduledCase v active absent a0 found assigned)
    apply Finset.mem_union_right
    obtain ⟨b, hb, within, _⟩ := exitBy v active absent a0 found
    unfold departed departs
    rw [Finset.mem_filter]
    refine ⟨active, ?_⟩
    change t.validators.data[v.toNat]? = some b at hb
    simp only [found, hb, Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      assigned, true_and]
    unfold horizon
    omega
  have leaves : getCurrentEpoch y.state ≠ getCurrentEpoch source := same
  obtain ⟨u, z, pre, step, rest, uEpoch, zEpoch⟩ := run_split tail leaves
  obtain ⟨s', rfl, invS⟩ := run_within laws early pre ⟨source, rfl, holds⟩ uEpoch
  change getCurrentEpoch s' = getCurrentEpoch source at uEpoch
  obtain ⟨a, r, invR, exitsR, aEpoch, activeSA, activeAZ, fixedZ⟩ :=
    crossing laws step invS (by rw [uEpoch]; exact zEpoch)
  refine ⟨r, a, invR, exitsR, ?_⟩
  have fixedS : activityFixedEpoch s' = activityFixedEpoch source := by
    unfold activityFixedEpoch; rw [uEpoch]
  intro v member
  rw [Finset.mem_filter] at member
  obtain ⟨active, absent⟩ := member
  obtain ⟨a0, found, act⟩ := isActiveAt_eq_true_iff.mp ((mem_activeSet early).mp active)
  by_cases assigned : a0.exitEpoch = FAR_FUTURE_EPOCH
  swap
  · exact Finset.mem_union_left _ (scheduledCase v active absent a0 found assigned)
  apply Finset.mem_union_right
  rw [uEpoch] at aEpoch
  -- Active at the epoch after the source, at the first state of that epoch.
  have atNext : isActiveAt a (getCurrentEpoch a) v.toNat = true := by
    have one := activeKept_of_chainSteps pre.chainSteps (getCurrentEpoch a)
      (fixed_ge source (n := 1) (by omega) lookahead (by omega)) v.toNat
    have two := activeSA (getCurrentEpoch a)
      (fixedS ▸ fixed_ge source (n := 1) (by omega) lookahead (by omega)) v.toNat
    rw [two, one, isActiveAt_eq_true_iff]
    refine ⟨a0, found, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt, assigned] at act ⊢
    omega
  -- Not active at the queried epoch, which the end of the run reads.
  have atLast : isActiveAt a Ep v.toNat = false := by
    have one := activeAZ Ep (fixed_ge a (n := 1) (by omega) lookahead (by omega)) v.toNat
    have two := activeKept_of_chainSteps rest.chainSteps Ep
      (fixedZ ▸ fixed_ge a (n := 1) (by omega) lookahead (by omega)) v.toNat
    rw [← one, ← two]
    exact absent
  obtain ⟨w, hw, actW⟩ := isActiveAt_eq_true_iff.mp atNext
  simp only [isActiveAt, hw, Option.map_some, Option.getD_some] at atLast
  simp only [isActiveValidator, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at actW atLast
  unfold departed departs
  rw [Finset.mem_filter]
  refine ⟨active, ?_⟩
  simp only [found, hw, Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    assigned, true_and]
  unfold horizon
  omega

/-- Stake already scheduled to exit, plus the initial queues' remaining potential.

The queues are read only through the two-epoch horizon.

Before Electra, the allowance counts a churn of validators at the pre-Electra balance cap. -/
def exitReserve (config : Config) (source : BeaconState preset fork) : Nat :=
  stake (fun v => balanceAt source v.toNat)
      {v ∈ activeSet source | (source.validators.data[v.toNat]?).any fun validator =>
        validator.exitEpoch.toNat ≤ (getCurrentEpoch source).toNat + 2} +
    if electra : .pectra ≤ fork then
      potential ((getCurrentEpoch source).toNat + 2)
          (source.earliestExitEpoch electra) (source.exitBalanceToConsume electra)
          ((exitChurnLimit config source).toOption.getD 0).toNat +
        potential ((getCurrentEpoch source).toNat + 2) (source.earliestConsolidationEpoch electra)
          (source.consolidationBalanceToConsume electra)
          ((getConsolidationChurnLimit config source).toOption.getD 0).toNat
    else max 1 (getValidatorChurnLimit config source).toNat * preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The stake that leaves the active set by a queried epoch within two epochs of a reachable state.

A later state reads the activity of the queried epoch, which is no earlier than its own epoch.

The bound adds scheduled exit stake to the initial queues' potential through the horizon. -/
theorem departing_stake_le_epoch {g y : ForkedBeaconState preset}
    {source : BeaconState preset fork}
    (genesis : Genesis (config := config) (checks := checks) g)
    (shared : Run config checks g ⟨fork, source⟩)
    (tail : Run config checks ⟨fork, source⟩ y)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (preGloas : y.fork < .glamsterdam)
    {Ep : Epoch} (later : getCurrentEpoch y.state ≤ Ep)
    (near : Ep.toNat ≤ (getCurrentEpoch source).toNat + 2) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeSet source | isActiveAt y.state Ep v.toNat = false} ≤
      exitReserve config source := by
  change _ ≤ stake (fun v => balanceAt source v.toNat) (scheduled source) +
    if electra : .pectra ≤ fork then queuePotential config electra source source
    else max 1 (getValidatorChurnLimit config source).toNat * preset.MAX_EFFECTIVE_BALANCE.toNat
  have early : fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) preGloas
  by_cases bounded : horizon source < 2 ^ 64 - 1
  swap
  · have sub : {v ∈ activeSet source | isActiveAt y.state Ep v.toNat = false} ⊆
        scheduled source := by
      intro v member
      rw [Finset.mem_filter] at member
      unfold scheduled
      rw [Finset.mem_filter]
      refine ⟨member.1, ?_⟩
      obtain ⟨a, found, _⟩ := isActiveAt_eq_true_iff.mp ((mem_activeSet early).mp member.1)
      simp only [found, Option.any_some, decide_eq_true_eq]
      have := a.exitEpoch.toNat_lt
      unfold horizon at bounded
      omega
    exact (stake_mono sub).trans (Nat.le_add_right _ _)
  by_cases electra : .pectra ≤ fork
  · simp only [electra, ↓reduceDIte]
    obtain ⟨r, a, invR, exitsR, sub⟩ := departing_subset (lawsE lookahead electra source) tail
      (InvE.start electra bounded) lookahead preGloas later near bounded
    have same := departed_of_exitsOnly exitsR.1 invR.size
    have bound := invR.departed_le
    have union := (stake_mono (w := fun v => balanceAt source v.toNat) sub).trans
      (stake_union_le _ _)
    rw [same] at union
    omega
  · simp only [electra, ↓reduceDIte]
    have before : fork < .pectra := Nat.lt_of_not_le electra
    obtain ⟨r, a, invR, exitsR, sub⟩ := departing_subset (lawsP lookahead before source bounded)
      tail (InvP.start source) lookahead preGloas later near bounded
    have same := departed_of_exitsOnly exitsR.1 invR.size
    have count := invR.departed_card bounded
    have capped := shared.effectiveBalance_capped_before_electra genesis before
    have each : ∀ v ∈ departed source r,
        balanceAt source v.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
      intro v _
      unfold balanceAt
      cases found : source.validators.data[v.toNat]? with
      | none => simp
      | some a =>
        simp only [Option.map_some, Option.getD_some]
        exact UInt64.le_iff_toNat_le.mp (capped a (Array.mem_of_getElem? found))
    have weight : stake (fun v => balanceAt source v.toNat) (departed source r) ≤
        (departed source r).card * preset.MAX_EFFECTIVE_BALANCE.toNat := by
      unfold stake
      calc _ ≤ ∑ _v ∈ departed source r, preset.MAX_EFFECTIVE_BALANCE.toNat :=
            Finset.sum_le_sum each
        _ = _ := by simp
    have scaled := Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE.toNat count
    have union := (stake_mono (w := fun v => balanceAt source v.toNat) sub).trans
      (stake_union_le _ _)
    rw [same] at union
    omega

end EthLib.Consensus.ExitChurn
