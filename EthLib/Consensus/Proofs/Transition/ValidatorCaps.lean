module

public import EthLib.Consensus.Proofs.Transition.Totality.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.RunKept
public import EthLib.Consensus.Proofs.Proposers
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
import EthLib.Consensus.Proofs.Transition.PendingConsolidations

/-!
# Validator effective-balance caps

Each validator's effective balance is at most the cap of its withdrawal credentials.

Genesis gives it, and every step keeps it before Gloas.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- At genesis, each validator's effective balance is at most the cap of its credentials. -/
theorem Genesis.effectiveBalance_capped {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ∀ validator ∈ g.state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset g.fork validator := by
  obtain ⟨hash, time, deposits, initialized⟩ := genesis
  exact (initializeBeaconStateFromEth1_withinBudget 0 (Nat.le_refl _) initialized).capped

/-- Unassigned validators retain their effective-balance funding and eligibility threshold. -/
private def UnassignedEligibleBalance {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.activationEpoch = FAR_FUTURE_EPOCH →
    (∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      (v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance) ∧ v.slashed = false

/-- At genesis, unassigned validators are funded and none is eligible yet. -/
private theorem genesis_unassigned_eligible_balance {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    UnassignedEligibleBalance g.state := by
  intro i v found pending
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨funded, unassigned, unslashed⟩ := initializeBeaconStateFromEth1_unassigned_eligibility
    initialized i v found pending
  refine ⟨funded, ?_, unslashed⟩
  exact fun assigned => False.elim (assigned unassigned)

/-- Ordered preset caps and retained compounding credentials make a validator's cap monotone. -/
private theorem withdrawalMaxEffectiveBalance_mono {f h : Fork} {v w : Validator}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h)
    (credentials : hasCompoundingWithdrawalCredential v = true →
      hasCompoundingWithdrawalCredential w = true) :
    withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split <;> rename_i before
  · have later : Fork.pectra ≤ h := Nat.le_trans before forks
    rw [ite_eq_left later]
    split <;> rename_i compound
    · rw [ite_eq_left (credentials compound)]
      exact UInt64.le_refl _
    · split
      · exact compounding
      · exact UInt64.le_refl _
  · split
    · split
      · exact UInt64.le_trans activation compounding
      · exact activation
    · exact UInt64.le_refl _

private theorem capped_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator}
    (capped : ∀ w ∈ s.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : s.setValidatorAt i v = .ok t) :
    ∀ w ∈ t.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  intro w member
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact capped w old
  · exact bound

/-- Cached proposers retain their registry index and assigned activation epoch. -/
private def AssignedProposers {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ fulu : .fusaka ≤ f, ∀ i ∈ (s.proposerLookahead fulu).toList,
    ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH

/-- A queued consolidation target exists at its stable index and has assigned activation. -/
private def AssignedTargets {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
    ∃ v, s.validators.data[entry.targetIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH

private theorem AssignedTargets.transfer {f : Fork} {s t : BeaconState preset f}
    (held : AssignedTargets s) (life : RegistryLifecycle s t)
    (subset : ∀ electra : .pectra ≤ f,
      ∀ entry ∈ (t.pendingConsolidations electra).data.toList,
        entry ∈ (s.pendingConsolidations electra).data.toList) : AssignedTargets t := by
  intro electra entry member
  obtain ⟨v, found, assigned⟩ := held electra entry (subset electra entry member)
  obtain ⟨w, read, kept⟩ := life.validators entry.targetIndex.toNat v found
  exact ⟨w, read, (kept.activationEpoch assigned) ▸ assigned⟩

private theorem assigned_of_active {v : Validator} {epoch : Epoch}
    (active : isActiveValidator v epoch = true) : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  intro far
  have less := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt active.1 active.2)
  rw [far] at less
  have bound := v.exitEpoch.toNat_lt
  change (2 ^ 64 - 1 : Nat) < v.exitEpoch.toNat at less
  omega

private theorem assigned_draw {f : Fork} {s : BeaconState preset f} {epoch : Epoch}
    {proposers : Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat}
    (ok : getBeaconProposerIndices s epoch = .ok proposers) :
    ∀ i ∈ proposers.toList,
      ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨active, checked, rest⟩ := bind_ok_iff.mp ok
  obtain ⟨seed, _, drawn⟩ := bind_ok_iff.mp rest
  intro i member
  have selected := mem_of_computeProposerIndices drawn i member
  have selected : i ∈ active := by
    unfold proposerCandidates at selected
    split at selected
    · exact List.mem_toArray.mp (Array.mem_filter.mp selected).1
    · exact List.mem_toArray.mp selected
  obtain ⟨v, found, active⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp selected
  exact ⟨v, found, assigned_of_active active⟩

private theorem AssignedProposers.transfer {f : Fork} {s t : BeaconState preset f}
    (held : AssignedProposers s) (life : RegistryLifecycle s t)
    (same : t.proposerLookahead = s.proposerLookahead) : AssignedProposers t := by
  intro fulu i member
  rw [same] at member
  obtain ⟨v, found, assigned⟩ := held fulu i member
  obtain ⟨w, read, kept⟩ := life.validators i.toNat v found
  exact ⟨w, read, (kept.activationEpoch assigned) ▸ assigned⟩

private theorem initialized_proposers {f : Fork} {s : BeaconState preset f}
    {lookahead : Vector ValidatorIndex
      ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)}
    (ok : initializeProposerLookahead s = .ok lookahead) :
    ∀ i ∈ lookahead.toList,
      ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨epochs, drawn, flattened⟩ := bind_ok_iff.mp ok
  cases flattened
  intro i member
  obtain ⟨epoch, member, selected⟩ := Vector.mem_flatten.mp (by simpa using member)
  obtain ⟨j, inside, rfl⟩ := List.getElem_of_mem
    (show epoch ∈ epochs.toList by simpa using member)
  have draw := vector_mapM_ok_getElem drawn j (by simpa using inside)
  obtain ⟨e, _, computed⟩ := bind_ok_iff.mp draw
  exact assigned_draw computed i (by simpa using selected)

private theorem refreshed_proposers {f : Fork} {s t : BeaconState preset f}
    {fulu : .fusaka ≤ f} (held : AssignedProposers s)
    (ok : processProposerLookahead s fulu = .ok t) : AssignedProposers t := by
  obtain ⟨epoch, _, rest⟩ := bind_ok_iff.mp ok
  obtain ⟨last, drawn, final⟩ := bind_ok_iff.mp rest
  cases final
  intro _ i member
  obtain ⟨j, inside, rfl⟩ := List.getElem_of_mem member
  simp only [Vector.getElem_toList, Vector.getElem_ofFn]
  split
  · exact held fulu _ (by simp)
  · exact assigned_draw drawn _ (by simp)

private structure CapStep (config : Config) {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop where
  capped : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) →
    ∀ v ∈ t.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset h v
  monotone : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w
  forward : getCurrentEpoch s ≤ getCurrentEpoch t
  proposers : AssignedProposers s → AssignedProposers t
  targets : AssignedTargets s → AssignedTargets t
  withdrawal : ∀ (i : Nat) (v w : Validator), s.validators.data[i]? = some v →
    t.validators.data[i]? = some w →
    (v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch) ∧
    (0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)

private theorem CapStep.refl {f : Fork} (s : BeaconState preset f) : CapStep config s s := by
  refine ⟨id, fun _ v found => ⟨v, found, UInt64.le_refl _⟩, UInt64.le_refl _, id, id, ?_⟩
  intro i v w before after
  have eq := Option.some.inj (before.symm.trans after)
  subst w
  exact ⟨fun slashed assigned => ⟨slashed, assigned, UInt64.le_refl _⟩,
    fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : CapStep config s t) (two : CapStep config t u) : CapStep config s u where
  capped := two.capped ∘ one.capped
  monotone i v found := by
    obtain ⟨w, read, first⟩ := one.monotone i v found
    obtain ⟨z, read', second⟩ := two.monotone i w read
    exact ⟨z, read', UInt64.le_trans first second⟩
  forward := UInt64.le_trans one.forward two.forward
  proposers := two.proposers ∘ one.proposers
  targets := two.targets ∘ one.targets
  withdrawal i v z before after := by
    obtain ⟨w, middle, _⟩ := one.monotone i v before
    obtain ⟨kept, newly⟩ := one.withdrawal i v w before middle
    obtain ⟨kept', newly'⟩ := two.withdrawal i w z middle after
    constructor
    · intro slashed assigned
      obtain ⟨flag, assigned', bound⟩ := kept slashed assigned
      obtain ⟨flag', assigned'', bound'⟩ := kept' flag assigned'
      exact ⟨flag', assigned'', UInt64.le_trans bound bound'⟩
    · intro delay unslashed slashed
      cases flag : w.slashed with
      | false =>
        obtain ⟨assigned, bound⟩ := newly' delay flag slashed
        have forward := UInt64.le_iff_toNat_le.mp one.forward
        exact ⟨assigned, by omega⟩
      | true =>
        obtain ⟨assigned, bound⟩ := newly delay unslashed flag
        obtain ⟨_, assigned', bound'⟩ := kept' flag assigned
        exact ⟨assigned', Nat.le_trans bound (UInt64.le_iff_toNat_le.mp bound')⟩

private theorem CapStep.data {f : Fork} {s t : BeaconState preset f}
    (same : t.validators.data = s.validators.data := by rfl)
    (slot : t.slot = s.slot := by rfl)
    (cache : t.proposerLookahead = s.proposerLookahead := by rfl)
    (targets : AssignedTargets s → AssignedTargets t := by
      intro held electra entry member
      exact ⟨_, (held electra entry member).choose_spec.1,
        (held electra entry member).choose_spec.2⟩) :
    CapStep config s t := by
  constructor
  · simpa only [same] using (id : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) → _)
  · intro i v found
    exact ⟨v, same ▸ found, UInt64.le_refl _⟩
  · rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  · exact fun held => held.transfer (.of_data same) cache
  · exact targets
  · intro i v w before after
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨fun slashed assigned => ⟨slashed, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ s a t, step s a = .ok t → CapStep config s t)
    (ok : xs.foldlM step s = .ok t) : CapStep config s t :=
  foldlM_ok_invariant (CapStep config s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

private theorem CapStep.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (found : getValidatorAt s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidatorAt i w = .ok t)
    (kept : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch := by
      intros; exact ⟨by assumption, by assumption, UInt64.le_refl _⟩)
    (newly : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      intro _ unslashed slashed
      exact Bool.noConfusion (unslashed.symm.trans slashed))
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH := by exact id) : CapStep config s t := by
  constructor
  · intro capped
    exact capped_setValidatorAt capped (bound (capped v (mem_of_getValidatorAt found))) ok
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    have read := getValidatorAt_eq_ok_iff.mp found
    intro j old located
    by_cases eq : j = i
    · subst j
      rw [read, Option.some.injEq] at located
      subst old
      exact ⟨w, by simp [BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set], monotone⟩
    · refine ⟨old, ?_, UInt64.le_refl _⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq] using located
  · obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
    exact UInt64.le_refl _
  · intro held fulu j member
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    obtain ⟨old, read, active⟩ := held fulu j member
    by_cases eq : j.toNat = i
    · have same := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans
        (eq ▸ read))
      subst old
      refine ⟨w, ?_, assigned active⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨old, ?_, active⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq] using read
  · intro held electra entry member
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    obtain ⟨old, read, active⟩ := held electra entry member
    by_cases eq : entry.targetIndex.toNat = i
    · have same := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans
        (eq ▸ read))
      subst old
      refine ⟨w, ?_, assigned active⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨old, ?_, active⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq] using read
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    intro j old final before after
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at after
    split at after
    · rename_i eq
      subst j
      have eq := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans before)
      subst old
      cases after
      exact ⟨kept, newly⟩
    · have eq := Option.some.inj (before.symm.trans after)
      subst final
      exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
        fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v w : Validator} (found : getValidator s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidator i w = .ok t)
    (kept : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch := by
      intros; exact ⟨by assumption, by assumption, UInt64.le_refl _⟩)
    (newly : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      intro _ unslashed slashed
      exact Bool.noConfusion (unslashed.symm.trans slashed))
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH := by exact id) : CapStep config s t :=
  CapStep.setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) monotone bound
    (by rwa [← setValidator_eq_setValidatorAt]) kept newly assigned

private theorem CapStep.increase {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : increaseBalance s i amount = .ok t) : CapStep config s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact CapStep.data rfl

private theorem CapStep.decrease {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : decreaseBalance s i amount = .ok t) : CapStep config s t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  exact CapStep.data rfl

private theorem CapStep.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    CapStep config s t := by
  obtain ⟨v, found, unchanged | ⟨unassigned, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact CapStep.refl _
  · have same := (exitQueue_validators queue).1
    have cache : queued.proposerLookahead = s.proposerLookahead := by
      obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
      rfl
    exact (CapStep.data (congrArg (·.data) same) (frame_exitQueue queue).slot cache
      (by obtain ⟨_, _, rfl⟩ := exitQueue_eq queue; exact id)).trans
      (CapStep.setValidator (v := v)
        (by rw [getValidator_of_validators_eq same]; exact found)
        (by exact UInt64.le_refl _) (by exact id) set
        (fun _ assigned => False.elim (assigned unassigned)))

private theorem CapStep.slash {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s i whistleblower = .ok t) : CapStep config s t := by
  obtain ⟨exitedState, v, withdrawal, marked, _, _, slashings, _, _, _, _, last,
    exited, found, summed, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have assigned (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
      v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    obtain ⟨old, read, unchanged | ⟨_, queued, epoch, withdrawable, _, add, written⟩⟩ :=
      initiateValidatorExit_ok exited
    · rw [unchanged.2] at found
      have eq := Except.ok.inj (read.symm.trans found)
      exact eq ▸ unchanged.1
    · obtain ⟨inside, rfl⟩ := setValidator_ok written
      simp only [getValidator, BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set_self,
        Except.ok.injEq] at found
      subst v
      intro far
      have sum := Base.Uint64.addChecked_ok_iff.mp add
      change epoch = FAR_FUTURE_EPOCH at far
      rw [far] at sum
      have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      rw [farNat] at sum
      omega
  have first := (CapStep.exit exited).trans
    (CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set
      (fun _ assigned => ⟨rfl, assigned, by
        apply UInt64.le_iff_toNat_le.mpr
        exact (Base.Uint64.toNat_max _ _).symm ▸ Nat.le_max_left _ _⟩)
      (fun delay _ _ => ⟨assigned delay, by
        have sum := Base.Uint64.addChecked_ok_iff.mp summed
        have epoch : getCurrentEpoch exitedState = getCurrentEpoch s := by
          rw [getCurrentEpoch, getCurrentEpoch, (frame_initiateValidatorExit exited).slot]
        change (getCurrentEpoch exitedState).toNat + _ ≤
          (max v.withdrawableEpoch withdrawal).toNat
        rw [epoch, Base.Uint64.toNat_max]
        omega⟩))
  have second := (CapStep.decrease (config := config) lowered).trans
    ((CapStep.increase raised).trans (CapStep.increase paid))
  have total := first.trans ((CapStep.data (s := marked)
    (t := { marked with slashings })).trans second)
  split
  · exact total.trans (CapStep.data rfl)
  · exact total

private theorem CapStep.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : CapStep config s t := by
  have data := addValidatorToRegistry_validators_eq_push ok
  constructor
  · intro capped v member
    rw [data, Array.mem_push] at member
    rcases member with old | rfl
    · exact capped v old
    · unfold getValidatorFromDeposit
      exact UInt64.le_iff_toNat_le.mpr (by rw [Base.Uint64.toNat_min]; exact Nat.min_le_right _ _)
  · intro i v found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨v, ?_, UInt64.le_refl _⟩
    simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found
  · rw [getCurrentEpoch, getCurrentEpoch, addValidatorToRegistry_slot ok]
    exact UInt64.le_refl _
  · have cache : t.proposerLookahead = s.proposerLookahead := by
      unfold addValidatorToRegistry at ok
      split at ok
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
        rfl
      · split at ok
        · cases ok; rfl
        · cases ok
    intro held fulu i member
    rw [cache] at member
    obtain ⟨v, found, assigned⟩ := held fulu i member
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨v, by simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found,
      assigned⟩
  · have queue : t.pendingConsolidations = s.pendingConsolidations := by
      unfold addValidatorToRegistry at ok
      split at ok
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
        rfl
      · split at ok <;> cases ok
        rfl
    intro held
    exact held.transfer (.append data) (fun _ _ member => queue ▸ member)
  · intro i v w before after
    have inside := (Array.getElem?_eq_some_iff.mp before).1
    have read : t.validators.data[i]? = some v := by
      simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using before
    have eq := Option.some.inj (read.symm.trans after)
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) : CapStep config s t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact CapStep.refl _
  · exact CapStep.increase raised
  · exact CapStep.add added

private theorem CapStep.applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : Consensus.applyDeposit config checks s key credentials amount signature = .ok t) :
    CapStep config s t := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (CapStep.add added).trans (CapStep.data rfl)
      · cases ok; exact CapStep.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact CapStep.data rfl
  · exact CapStep.deposit ok

private theorem CapStep.processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : CapStep config s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (CapStep.data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans (CapStep.applyDeposit credited)

private theorem CapStep.registryEntry {f : Fork} {s t : BeaconState preset f}
    {i : Nat} (ok : updateRegistryEntry config s i = .ok t) : CapStep config s t := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have preserved : (queued.effectiveBalance = v.effectiveBalance ∧
      queued.withdrawalCredentials = v.withdrawalCredentials) ∧
      (queued.slashed = v.slashed ∧ queued.exitEpoch = v.exitEpoch ∧
        queued.withdrawableEpoch = v.withdrawableEpoch) := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    · cases queue; exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  obtain ⟨same, records⟩ := preserved
  have cap : withdrawalMaxEffectiveBalance preset f queued =
      withdrawalMaxEffectiveBalance preset f v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
      hasCompoundingWithdrawalCredential, same.2]
    rfl
  have first := CapStep.setValidatorAt (config := config) found
    (by rw [cap]; exact UInt64.le_refl _) (by simp only [same.1, cap]; exact id) set
    (by simp only [records.1, records.2.1, records.2.2];
        exact fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩)
    (by intro _ unslashed slashed
        exact Bool.noConfusion (unslashed.symm.trans (records.1.symm.trans slashed)))
    (by unfold queueForActivation at queue
        split at queue
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
          obtain ⟨_, _, rfl⟩ := queue
          exact id
        · cases queue; exact id)
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans (CapStep.exit exited)
  · cases ok; exact first

private theorem CapStep.activate {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v : Validator} (found : getValidator s i = .ok v)
    (far : v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : activateValidator s i = .ok t) : CapStep config s t := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨old, read, _, _, set⟩ := ok
  obtain rfl : old = v := Except.ok.inj (read.symm.trans found)
  exact CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set
    (assigned := fun assigned => (assigned far).elim)

private theorem CapStep.registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {i : Nat}
    (ok : updateRegistryEntryElectra config epoch s i = .ok t) : CapStep config s t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact CapStep.setValidatorAt found (by exact UInt64.le_refl _) (by exact id) set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact CapStep.exit exited
  split at ok
  · exact CapStep.setValidatorAt found (by exact UInt64.le_refl _) (by exact id)
      (liftAccessor_ok.mp ok)
      (assigned := fun assigned => (assigned (activationEpoch_of_isEligibleForActivation
        (by assumption))).elim)
  · cases ok; exact CapStep.refl _

private theorem CapStep.registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : CapStep config s t := by
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact CapStep.fold (fun _ _ _ => CapStep.registryElectra) ok
  · rename_i notElectra
    simp only [bind_ok_iff] at ok
    obtain ⟨middle, updated, activated⟩ := ok
    have before : f < .glamsterdam :=
      Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
    have small : middle.validators.data.size < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (middle.validators.bound before) (UInt64.toNat_lt _)
    refine (CapStep.fold (fun _ _ _ => CapStep.registryEntry) updated).trans
      (foldActivateValidator_of_unassigned (CapStep config) CapStep.refl
        (fun one two => one.trans two) (fun found far ok => CapStep.activate found far ok)
        (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
        (fun i member => ?_) activated)
    obtain ⟨position, v, equal, found, eligible⟩ :=
      mem_activationQueue (List.mem_of_mem_take member)
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have exactIndex : i.toNat = position := by
      have fits : position < UInt64.size := by
        change position < 2 ^ 64
        omega
      rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
    exact ⟨v, by simp [getValidator, exactIndex, found],
      activationEpoch_of_isEligibleForActivation eligible⟩

private theorem CapStep.excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra i = .ok t) : CapStep config s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact CapStep.data rfl
  · cases ok; exact CapStep.refl _

private theorem CapStep.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator s electra i = .ok t) : CapStep config s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨v, found, _, set, queued⟩ := ok
  apply CapStep.trans (CapStep.setValidator found ?_ ?_ set) (CapStep.excess queued)
  · simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
      getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]
    simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
    by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
    · simp only [h]; exact UInt64.le_refl _
    · simp only [h]; exact order
  · intro bound
    apply UInt64.le_trans bound
    simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
      getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]
    simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
    by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
    · simp only [h]; exact UInt64.le_refl _
    · simp only [h]; exact order

private theorem CapStep.blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : CapStep config s t := by
  obtain ⟨v, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
  have before : hasCompoundingWithdrawalCredential v = false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      BLS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  have after : hasCompoundingWithdrawalCredential
      { v with withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
      false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential,
      executionCredentials_prefix, ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  apply CapStep.setValidator found ?_ ?_ set
  · simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, before, after,
      Bool.false_eq_true, ↓reduceIte]
    exact UInt64.le_refl _
  · simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, before, after,
      Bool.false_eq_true, ↓reduceIte]
    exact id

private theorem CapStep.consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (target : ∃ v, s.validators.data[targetIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    CapStep config s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, withdrawal, _, marked, set, pending, appended, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  have cache : churned.proposerLookahead = s.proposerLookahead := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churn
    obtain ⟨_, _, _, _, _, _, rest⟩ := churn
    cases rest; rfl
  have queue : churned.pendingConsolidations = s.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churn
    obtain ⟨_, _, _, _, _, _, rest⟩ := churn
    cases rest; rfl
  have first := (CapStep.data (config := config) (by rw [validators])
    (frame_computeConsolidationEpochAndUpdateChurn churn).slot cache
    (fun held => held.transfer (.of_data (congrArg (·.data) validators))
      (fun _ _ member => queue ▸ member))).trans
    (CapStep.setValidator read (by exact UInt64.le_refl _) (by exact id) set
      (fun _ assigned => False.elim (assigned far)))
  refine first.trans (CapStep.data rfl rfl rfl ?_)
  intro held witness entry member
  have data := appendWithinLimit_data appended
  change entry ∈ pending.data.toList at member
  rw [data, Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact held witness entry old
  · obtain ⟨v, foundTarget, assigned⟩ := target
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    by_cases eq : targetIndex.toNat = sourceIndex.toNat
    · have same := Option.some.inj (found.symm.trans (eq ▸ foundTarget))
      subst v
      refine ⟨{ source with exitEpoch := epoch, withdrawableEpoch := withdrawal }, ?_, assigned⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨v, ?_, assigned⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq, validators] using foundTarget

private theorem CapStep.consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t) : CapStep config s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact CapStep.refl _)
    | exact CapStep.compounding order (liftAccessor_ok.mp ok)
    | (refine CapStep.consolidate (getElem?_toNat_of_ofNatChecked (by assumption))
        (by clear ok; simp_all) ?_ ok
       refine ⟨_, getElem?_toNat_of_ofNatChecked (by assumption), ?_⟩
       apply assigned_of_active (epoch := getCurrentEpoch s)
       clear ok; simp_all)

private theorem CapStep.partialWithdrawal {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra i v amount owed = .ok t) :
    CapStep config s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact CapStep.data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
      (frame_computeExitEpochAndUpdateChurn churned).slot
      (by
        simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at churned
        obtain ⟨_, _, _, _, _, _, rest⟩ := churned
        cases rest; rfl)
      (by
        simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at churned
        obtain ⟨_, _, _, _, _, _, rest⟩ := churned
        cases rest; exact id)
  · cases ok; exact CapStep.refl _

private theorem CapStep.withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : CapStep config s t := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact CapStep.refl _)
    | exact CapStep.exit (liftAccessor_ok.mp ok)
    | exact CapStep.partialWithdrawal ok

private theorem CapStep.depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : CapStep config s t := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact CapStep.data rfl

private theorem CapStep.requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processExecutionRequests config s body electra = .ok t) : CapStep config s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  exact (CapStep.fold (fun _ _ _ => CapStep.depositRequest) deposits).trans
    ((CapStep.fold (fun _ _ _ => CapStep.withdrawalRequest) withdrawals).trans
      (CapStep.fold (fun _ _ _ => CapStep.consolidationRequest order) consolidations))

private theorem CapStep.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : CapStep config s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact CapStep.slash slashed

private theorem CapStep.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : CapStep config s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => CapStep config s step.1) ?_ (CapStep.refl s) folded
  intro step i next previous ok
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact previous.trans (CapStep.slash slashed)
  · cases ok; exact previous

private theorem CapStep.block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (early : f < .glamsterdam)
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) : CapStep config s t := by
  have same {a b : BeaconState preset f} (validators : b.validators = a.validators)
      (slot : b.slot = a.slot) (cache : b.proposerLookahead = a.proposerLookahead)
      (queue : b.pendingConsolidations = a.pendingConsolidations) :
      CapStep config a b := CapStep.data (congrArg (·.data) validators) slot cache
        (fun held => held.transfer (.of_data (congrArg (·.data) validators))
          (fun _ _ member => queue ▸ member))
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : CapStep config s input :=
    same (started.validators_eq early) (frame_operationsInput started).slot
      (started.step_of (fun a b => b.proposerLookahead = a.proposerLookahead)
        (fun _ => rfl) (fun one two => two.trans one)
        (fun gloas _ => absurd gloas (Nat.not_le_of_lt early))
        (fun headed => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed; rfl)
        (fun _ executed => processBlockExecution_proposerLookahead executed)
        (fun revealed => by
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
          rfl)
        (fun _ voted => by obtain ⟨_, _, rest⟩ := processEth1Data_eq voted; rw [← rest]))
      (started.step_of SamePendingQueue (fun _ => rfl) (fun one two => two.trans one)
        (fun gloas _ => absurd gloas (Nat.not_le_of_lt early))
        (fun headed => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed; rfl)
        (fun _ executed => SamePendingQueue.blockExecution early executed)
        (fun revealed => by
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
          rfl)
        (fun _ voted => by
          obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
          unfold SamePendingQueue
          rw [← rest]))
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of (CapStep config) CapStep.refl (fun one two => one.trans two)
      CapStep.processDeposit (fun exited => CapStep.exit (processVoluntaryExit_initiates exited))
      CapStep.blsChange (CapStep.requests order)
      (fun attested => same (by rw [processPayloadAttestation_eq attested])
        (by rw [processPayloadAttestation_eq attested])
        (by rw [processPayloadAttestation_eq attested])
        (by rw [processPayloadAttestation_eq attested])) operated
  have tail : CapStep config last t := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact same rfl rfl rfl rfl
    · cases synced
      exact CapStep.refl _
  exact head.trans <|
    (CapStep.fold (fun _ _ _ => CapStep.proposerSlashing) proposersOk).trans <|
    (CapStep.fold (fun _ _ _ => CapStep.attesterSlashing) slashingsOk).trans <|
    (CapStep.fold (fun _ _ _ attested => same (processAttestation_registry attested).1
      (frame_processAttestation attested).slot (processAttestation_proposerLookahead attested)
      (by
        by_cases electra : .pectra ≤ f
        · exact SamePendingQueue.attestation electra attested
        · funext witness; exact (electra witness).elim))
      attestedOk).trans (rest.trans tail)

private theorem CapStep.pending {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t) :
    CapStep config s t := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → CapStep config state result.1.state := by
    intro deposits
    induction deposits with
    | nil => intro state processed count postponed result ok; cases ok; exact CapStep.refl _
    | cons deposit rest ih =>
      intro state processed count postponed result ok
      unfold passPendingDeposits at ok
      simp only [bind, Except.bind, pure, Except.pure] at ok
      split at ok
      · cases ok; exact CapStep.refl _
      split at ok
      · cases ok
      split at ok
      · split at ok
        · cases ok
        rename_i credited
        split at ok
        · cases ok
        cases ok
        exact (CapStep.deposit credited).trans (ih ‹_›)
      split at ok
      · split at ok
        · cases ok
        cases ok
        exact ih ‹_›
      split at ok
      · cases ok
      split at ok
      · cases ok; exact CapStep.refl _
      split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (CapStep.deposit credited).trans (ih ‹_›)
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact (pass ‹_›).trans (CapStep.data rfl)

/-- Rounding an effective balance cannot raise the capped Pre potential. -/
private theorem pre_effective_le {largest balance effective result : Gwei}
    (ok : updatedEffectiveBalance preset largest balance effective = .ok result) :
    max result.toNat (min balance.toNat largest.toNat) ≤
      max effective.toNat (min balance.toNat largest.toNat) := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · exact Nat.le_refl _
  · have remainder : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    have rounded := UInt64.le_iff_toNat_le.mp (UInt64.sub_le remainder)
    simp only [Uint64.toNat_min]
    omega

private theorem CapStep.effective {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) : CapStep config s t := by
  unfold processEffectiveBalanceUpdates at ok
  refine CapStep.fold (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, balance, read, next, changed, set⟩ := ok
  refine CapStep.setValidatorAt found ?_ ?_ set
  · exact UInt64.le_refl _
  · intro bound
    have potential := pre_effective_le changed
    have capped := UInt64.le_iff_toNat_le.mp bound
    apply UInt64.le_iff_toNat_le.mpr
    change next.toNat ≤ (withdrawalMaxEffectiveBalance preset f v).toNat
    omega

/-- An epoch keeps the caps; only three of its stages change the validators. -/
private theorem CapStep.epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) : CapStep config s t := by
  apply (processEpoch_trace ok).transport (CapStep config) CapStep.refl (fun a b => a.trans b)
  intro k _ a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case registry => exact CapStep.registry edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact CapStep.pending edge
    · exact edge ▸ CapStep.refl _
  case effectiveBalances => exact CapStep.effective edge
  case rewards =>
    exact CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [EpochStage.Edge] at edge; rw [processRewardsAndPenalties_frame edge])
      (by rw [processRewardsAndPenalties_frame edge])
      (fun held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩)))
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member))
  case slashings =>
    exact CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [EpochStage.Edge] at edge; rw [processSlashings_frame edge])
      (by rw [processSlashings_frame edge])
      (fun held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩)))
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member))
  case pendingConsolidations =>
    have targets : AssignedTargets a → AssignedTargets b := by
      intro held
      simp only [EpochStage.Edge] at edge
      split at edge
      · intro electra entry member
        obtain ⟨result, passed, _, queue⟩ := processPendingConsolidations_pass edge
        rw [queue] at member
        have before : entry ∈ (a.pendingConsolidations electra).data.toList :=
          List.mem_of_mem_drop member
        obtain ⟨v, found, assigned⟩ := held electra entry before
        exact ⟨v, by rw [(processPendingConsolidations_kept edge).1]; exact found, assigned⟩
      · cases edge; exact held
    refine CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      ?_ ?_ targets
    · simp only [EpochStage.Edge] at edge
      split at edge
      · exact (frame_processPendingConsolidations edge).slot
      · exact edge ▸ rfl
    · simp only [EpochStage.Edge] at edge
      split at edge
      · exact processPendingConsolidations_proposerLookahead edge
      · exact edge ▸ rfl
  case proposerLookahead =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · have assigned := fun held => refreshed_proposers held edge
      simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact { CapStep.data (s := a) (t := a) with
        proposers := assigned }
    · exact edge ▸ CapStep.refl _
  all_goals
    refine CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2 ?_
      (fun held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩)))
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member))
    simp only [EpochStage.Edge] at edge
    first
    | (obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
       · rfl
       · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
         rw [← rest])
    | (split at edge
       · rw [processInactivityUpdates_frame edge]
       · exact edge ▸ rfl)
    | (split at edge
       · rw [processEth1DataReset_frame edge]
       · exact edge ▸ rfl)
    | (split at edge
       · rw [processBuilderPendingPayments_eq edge]
       · exact edge ▸ rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge; rfl)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge; rfl)
    | (split at edge
       · unfold processHistoricalSummariesUpdate at edge
         simp only [bind, Except.bind, pure, Except.pure] at edge
         repeat' (split at edge <;> try cases edge)
         all_goals rfl
       · unfold processHistoricalRootsUpdate at edge
         split at edge
         · cases edge
         simp only [bind_ok_iff, liftAccessor_ok] at edge
         obtain ⟨_, _, edge⟩ := edge
         split at edge
         · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at edge
           obtain ⟨_, _, _, _, rfl⟩ := edge
           rfl
         · cases edge; rfl)
    | (split at edge
       · subst edge; rfl
       · obtain ⟨u, computed, _, _, restored⟩ :=
           processParticipationRecordUpdates_eq (state := a) (Nat.lt_of_not_le (by assumption))
         obtain rfl := Except.ok.inj (computed.symm.trans edge)
         exact congrArg (·.proposerLookahead) restored)
    | (split at edge
       · unfold processSyncCommitteeUpdates at edge
         simp only [bind, Except.bind, pure, Except.pure] at edge
         repeat' (split at edge <;> try cases edge)
         all_goals rfl
       · exact edge ▸ rfl)
    | (split at edge
       · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
         obtain ⟨_, _, _, _, rfl⟩ := edge; rfl
       · exact edge ▸ rfl)

private theorem CapStep.slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) : CapStep config s t := by
  have later := (runKept_advanceSlot ok).later
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · have step := CapStep.epoch advance
    exact ⟨step.capped, step.monotone, later, step.proposers, step.targets, step.withdrawal⟩
  · cases advance
    exact ⟨id, fun _ v found => ⟨v, found, UInt64.le_refl _⟩, later,
      id, id, (CapStep.refl s).withdrawal⟩

private theorem CapStep.carry {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h) (slot : t.slot = s.slot := by rfl)
    (proposers : AssignedProposers s → AssignedProposers t := by
      intro _
      unfold AssignedProposers
      intro fulu
      have impossible := fulu
      simp +decide at impossible)
    (targets : AssignedTargets s → AssignedTargets t := by
      intro held
      unfold AssignedTargets
      intro electra entry member
      first
      | (have impossible := electra; simp +decide at impossible)
      | simp [carryFields] at member) : CapStep config s t where
  capped capped v member := UInt64.le_trans (capped v (same ▸ member))
    (withdrawalMaxEffectiveBalance_mono activation compounding forks id)
  monotone _i v found := ⟨v, same ▸ found,
    withdrawalMaxEffectiveBalance_mono activation compounding forks id⟩
  forward := by
    rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  proposers := proposers
  targets := targets
  withdrawal i v w before after := by
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, UInt64.le_refl _⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

private theorem CapStep.preActivation {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queuePreActivation s electra i = .ok t) : CapStep config s t := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  have changed := CapStep.setValidator (config := config) (v := v)
    (by simpa only [getValidator, BeaconState.putBalance] using found)
    (by exact UInt64.le_refl _) (by intro _; exact UInt64.zero_le) validator
  exact ⟨changed.capped, changed.monotone, changed.forward, changed.proposers,
    changed.targets, changed.withdrawal⟩

private theorem CapStep.upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) :
    CapStep config s.state t.val.state := by
  have frame := upgradeFrame_upgradeNext ok
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact CapStep.carry (upgradeToAltair_spec upgraded).1
      activation compounding (by change Fork.phase0 ≤ .altair; decide) frame.slot
  · subst ok
    exact CapStep.carry rfl activation compounding (by change Fork.altair ≤ .bellatrix; decide)
  · subst ok
    exact CapStep.carry rfl activation compounding (by change Fork.bellatrix ≤ .shapella; decide)
  · subst ok
    exact CapStep.carry rfl activation compounding (by change Fork.shapella ≤ .dencun; decide)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    have queuedStep := CapStep.fold (config := config)
      (fun _ _ _ => CapStep.preActivation) queued
    have one := (CapStep.carry (s := state) (h := .pectra) (t := _) (by rfl)
      activation compounding (by decide) (by rfl)
      (by intro _ fulu; exact (by decide : ¬ Fork.fusaka ≤ .pectra) fulu |>.elim)
      (by intro _ electra entry member
          simp [carryFields, show ¬ Fork.pectra ≤ .dencun by decide] at member)).trans queuedStep
    apply one.trans
    refine CapStep.fold (fun a index b ok => ?_) compounded
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · exact CapStep.excess (liftAccessor_ok.mp ok)
      · cases ok; exact CapStep.refl _
    · cases ok; exact CapStep.refl _
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine CapStep.carry (upgradeToFulu_spec upgraded).1
      activation compounding (by change Fork.pectra ≤ .fusaka; decide) frame.slot
      (fun _ => ?_) (fun held => ?_)
    · obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      intro _ i member
      exact initialized_proposers (liftAccessor_ok.mp initialized) i member
    · obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      intro electra entry member
      simpa [carryFields, carryRooted] using
        held (show Fork.pectra ≤ .pectra by decide) entry
          (by simpa [carryFields, carryList] using member)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

private theorem CapStep.upgrades {s t : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam) :
    CapStep config s.state t.state := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (CapStep.upgrade activation compounding nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early)).trans (ih next rest early)
  | case2 s notDue => cases ok; exact CapStep.refl _

private theorem CapStep.step {s t : ForkedBeaconState preset}
    (step : Step config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) : CapStep config s.state t.state := by
  cases step with
  | block engine signed due ok =>
    exact CapStep.block early compounding (applySignedBlock_ok ok).2.1
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (CapStep.slot slotOk).trans
      (CapStep.upgrades activation compounding upgrades early)

private theorem CapStep.run {s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) : CapStep config s.state t.state := by
  induction run with
  | nil => exact CapStep.refl _
  | snoc pre step ih =>
    exact (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)).trans
      (CapStep.step step activation compounding early)

private theorem run_assigned_proposers {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) : AssignedProposers x.state := by
  apply (CapStep.run run activation compounding early).proposers
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨before, _⟩ := initializeBeaconStateFromEth1_ok initialized
  intro fulu
  exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fulu)).elim

private theorem run_assigned_targets {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) : AssignedTargets x.state := by
  apply (CapStep.run run activation compounding early).targets
  obtain ⟨_, _, _, initialized⟩ := genesis
  obtain ⟨before, _⟩ := initializeBeaconStateFromEth1_ok initialized
  intro electra
  exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) electra)).elim

private theorem unassigned_not_consolidation_target {f : Fork} {s : BeaconState preset f}
    (held : AssignedTargets s) {electra : .pectra ≤ f} {entry : PendingConsolidation}
    (member : entry ∈ (s.pendingConsolidations electra).data.toList)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) : entry.targetIndex.toNat ≠ i := by
  intro eq
  obtain ⟨w, read, assigned⟩ := held electra entry member
  rw [eq, found, Option.some.injEq] at read
  subst w
  exact assigned unassigned

private theorem unassigned_not_cached_proposer {f : Fork} {s : BeaconState preset f}
    (held : AssignedProposers s) {fulu : .fusaka ≤ f} {proposer : ValidatorIndex}
    (member : proposer ∈ (s.proposerLookahead fulu).toList)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) : proposer.toNat ≠ i := by
  intro eq
  obtain ⟨w, read, assigned⟩ := held fulu proposer member
  rw [eq, found, Option.some.injEq] at read
  subst w
  exact assigned unassigned

private theorem run_unassigned_credit_exclusions {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) {i : Nat} {v : Validator}
    (found : x.state.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) :
    (∀ electra : .pectra ≤ x.fork,
      ∀ entry ∈ (x.state.pendingConsolidations electra).data.toList,
        entry.targetIndex.toNat ≠ i) ∧
    (∀ fulu : .fusaka ≤ x.fork,
      ∀ proposer ∈ (x.state.proposerLookahead fulu).toList, proposer.toNat ≠ i) := by
  constructor
  · intro electra entry member
    exact unassigned_not_consolidation_target
      (run_assigned_targets run genesis activation compounding early) member found unassigned
  · intro fulu proposer member
    exact unassigned_not_cached_proposer
      (run_assigned_proposers run genesis activation compounding early) member found unassigned

/-- Before Gloas, each validator reached from genesis has an effective balance at most its cap.

The preset caps are assumed in order.

`MAX_EFFECTIVE_BALANCE` is at most `MIN_ACTIVATION_BALANCE`.

`MIN_ACTIVATION_BALANCE` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`.
-/
theorem Run.effectiveBalance_capped {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) :
    ∀ v ∈ x.state.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v :=
  (CapStep.run run activation compounding early).capped genesis.effectiveBalance_capped

/-- An existing validator's cap cannot decrease along a pre-Gloas run. -/
theorem Run.validatorCap_mono {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : y.fork < .glamsterdam) (i : Nat) (v : Validator)
    (found : x.state.validators.data[i]? = some v) :
    ∃ w, y.state.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset x.fork v ≤
        withdrawalMaxEffectiveBalance preset y.fork w :=
  (CapStep.run run activation compounding early).monotone i v found

/-- New slashings delay withdrawal by the slashings-vector length from the run's start epoch.

Its exit epoch is assigned. -/
theorem Run.newly_slashed_withdrawableEpoch {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (unslashed : v.slashed = false) (slashed : w.slashed = true) :
    w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
      (getCurrentEpoch x.state).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat :=
  ((CapStep.run run activation compounding early).withdrawal i v w before after).2
    delay unslashed slashed

/-- The cap at an existing index cannot decrease during an epoch. -/
theorem processEpoch_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.epoch ok).monotone i v found

/-- The cap at an existing index cannot decrease in a proposer slashing. -/
theorem processProposerSlashing_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.proposerSlashing ok).monotone i v found

/-- The cap at an existing index cannot decrease in an attester slashing. -/
theorem processAttesterSlashing_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.attesterSlashing ok).monotone i v found

/-- The cap at an existing index cannot decrease in a deposit. -/
theorem processDeposit_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.processDeposit ok).monotone i v found

/-- The cap at an existing index cannot decrease in a voluntary exit. -/
theorem processVoluntaryExit_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.exit (processVoluntaryExit_initiates ok)).monotone i v found

/-- The cap at an existing index cannot decrease in a change of BLS credentials. -/
theorem processBlsToExecutionChange_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.blsChange ok).monotone i v found

/-- The cap at an existing index cannot decrease in a withdrawal request. -/
theorem processWithdrawalRequest_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.withdrawalRequest ok).monotone i v found

/-- The cap at an existing index cannot decrease in a consolidation request.

This needs `MIN_ACTIVATION_BALANCE` to be at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
theorem processConsolidationRequest_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.consolidationRequest compounding ok).monotone i v found

/-- Before the slashings stage, a slashed validator with an assigned exit keeps that exit.

Its withdrawable epoch cannot decrease across the preceding epoch stages. -/
theorem EpochTrace.slashed_withdrawableEpoch_mono
    {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry] s t)
    (i : Nat) (v w : Validator)
    (before : s.validators.data[i]? = some v)
    (after : t.validators.data[i]? = some w)
    (slashed : v.slashed = true) (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    w.slashed = true ∧ w.exitEpoch = v.exitEpoch ∧
      v.withdrawableEpoch ≤ w.withdrawableEpoch := by
  cases trace with | cons justified rest =>
    cases rest with | cons inactivity rest =>
      cases rest with | cons rewarded rest =>
        cases rest with | cons registered rest =>
          cases rest
          have one := (EpochStage.action_cases.mp justified).validators_eq
            ⟨nofun, nofun, nofun⟩
          have two := (EpochStage.action_cases.mp inactivity).validators_eq
            ⟨nofun, nofun, nofun⟩
          have three := (EpochStage.action_cases.mp rewarded).validators_eq
            ⟨nofun, nofun, nofun⟩
          have atRegistry := before
          rw [← one, ← two, ← three] at atRegistry
          have ok := EpochStage.action_cases.mp registered
          have kept := ((CapStep.registry ok).withdrawal i v w atRegistry after).1
            slashed assigned
          obtain ⟨last, located, life⟩ :=
            (registryLifecycle_processRegistryUpdates ok).validators i v atRegistry
          obtain rfl : last = w := Option.some.inj (located.symm.trans after)
          exact ⟨kept.1, life.exitEpoch assigned, kept.2.2⟩

end EthLib.Consensus
