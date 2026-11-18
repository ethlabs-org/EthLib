module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
import EthLib.Consensus.Proofs.Transition.EpochPassAtCall
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Producers

/-!
# Exit counts, gain rate and preset facts for the pin split

The exit queues bound the number of keys whose exit starts along a run.

A validator that a step creates has no exit epoch, so every exit that starts has a departure charge.

The gain rate of a key is at most the gain rate at the largest effective balance.

The preset facts that the pin's floors read hold for the mainnet and minimal presets.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-! ## Group C: exit counts, gain rate, new keys, preset facts (items 15, 16, new-key step, N6) -/

/-! ## A validator created in a step has no exit assigned -/

/-- Every validator from position `n` on has no exit epoch assigned. -/
private def ExitFarFrom (n : ℕ) {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ i v, n ≤ i → s.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH

private theorem ExitFarFrom.of_data {n : ℕ} {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  intro i v large found
  rw [same] at found
  exact holds i v large found

/-- A registry that does not reach position `n` has no validator from there on. -/
private theorem ExitFarFrom.of_size {n : ℕ} {f : Fork} {s : BeaconState preset f}
    (small : s.validators.data.size ≤ n) : ExitFarFrom n s := by
  intro i v large found
  have := (Array.getElem?_eq_some_iff.mp found).1
  omega

/-- A write that keeps the exit epoch of its validator keeps the later validators unassigned. -/
private theorem ExitFarFrom.of_set {n position : ℕ} {f : Fork} {s t : BeaconState preset f}
    {old v : Validator} (found : getValidatorAt s position = .ok old)
    (set : s.setValidatorAt position v = .ok t) (same : v.exitEpoch = old.exitEpoch)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro i w large got
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at got
  split at got
  · rename_i place
    subst place
    cases got
    rw [same]
    exact holds position old large (getValidatorAt_eq_ok_iff.mp found)
  · exact holds i w large got

/-- A pending deposit appends a validator with no exit epoch. -/
private theorem ExitFarFrom.of_apply {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks s deposit = .ok t) (holds : ExitFarFrom n s) :
    ExitFarFrom n t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨index, raised⟩ | ⟨_, added⟩
  · exact holds
  · exact holds.of_data (congrArg (·.data) (increaseBalance_validators raised))
  · intro i v large found
    rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push] at found
    split at found
    · cases found
      rfl
    · exact holds i v large found

private theorem ExitFarFrom.of_deposits {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : Consensus.processPendingDeposits config checks s electra = .ok t)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  obtain ⟨_, _, _, _, next, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept : ExitFarFrom n next :=
    foldlM_ok_invariant (g := Consensus.applyPendingDeposit config checks)
      (fun u : BeaconState preset f => ExitFarFrom n u)
      (fun _ _ _ before step => ExitFarFrom.of_apply step before) holds folded
  exact kept

/-- The effective-balance updates write only effective balances. -/
private theorem ExitFarFrom.of_updates {n : ℕ} {f : Fork}
    {s t : BeaconState preset f} (ok : Consensus.processEffectiveBalanceUpdates s = .ok t)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  unfold Consensus.processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun u : BeaconState preset f => ExitFarFrom n u)
    (fun _ _ _ before step => ?_) holds ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨validator, found, _, _, _, _, set⟩ := step
  exact before.of_set found set rfl

/-- An epoch appends validators only in its pending deposits, after the registry updates.

So a validator that the epoch creates has no exit epoch. -/
private theorem ExitFarFrom.of_epoch {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (ok : Consensus.processEpoch config checks s = .ok t)
    (small : s.validators.data.size ≤ n) : ExitFarFrom n t := by
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, consolidated,
    settled, updated, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
    depositedOk, consolidatedOk, settledOk, updatedOk, rest⟩ :=
    EpochTrace.through_effectiveBalances (processEpoch_trace ok)
  have keeps {k : EpochStage} {a b : BeaconState preset f}
      (other : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances)
      (computed : EpochStage.action config checks k a = .ok b) : b.validators = a.validators :=
    (EpochStage.action_cases.mp computed).records other |>.1
  -- The first six stages keep the size of the registry.
  have size : reset.validators.data.size = s.validators.data.size := by
    have one : justified.validators.data.size = s.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .justification) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        justifiedOk)
    have two : scored.validators.data.size = justified.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .inactivity) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        scoredOk)
    have three := (processRewardsAndPenalties_sameSizes
      (EpochStage.action_cases.mp rewardedOk)).1
    have four := (sameSizes_processRegistryUpdates (EpochStage.action_cases.mp registeredOk)).1
    have five := (sameSizes_processSlashings (EpochStage.action_cases.mp slashedOk)).1
    have six : reset.validators.data.size = slashed.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .eth1Reset) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        resetOk)
    omega
  have atReset : ExitFarFrom n reset := .of_size (by omega)
  -- Pending deposits append validators with no exit.
  have atDeposited : ExitFarFrom n deposited := by
    have edge := EpochStage.action_cases.mp depositedOk
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact atReset.of_deposits edge
  have atConsolidated : ExitFarFrom n consolidated :=
    atDeposited.of_data (congrArg (·.data)
      ((EpochStage.action_cases.mp consolidatedOk).validators_eq ⟨nofun, nofun, nofun⟩))
  have atSettled : ExitFarFrom n settled :=
    atConsolidated.of_data (congrArg (·.data) ((EpochStage.action_cases.mp settledOk).validators_eq
      ⟨nofun, nofun, nofun⟩))
  have atUpdated : ExitFarFrom n updated :=
    atSettled.of_updates (EpochStage.action_cases.mp updatedOk)
  -- The seven later stages keep the validators.
  have same : t.validators = updated.validators :=
    EpochTrace.transport (fun a b : BeaconState preset f => b.validators = a.validators)
      (fun _ => rfl) (fun one two => two.trans one)
      (fun k member a b computed => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        exact keeps (by rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩) computed) rest
  exact atUpdated.of_data (congrArg (·.data) same)

/-- From Electra, a fork upgrade keeps the registry. -/
private theorem upgradeNext_validators {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data = pre.state.validators.data := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · exact absurd (show Fork.pectra ≤ Fork.phase0 from electra) (by decide)
  · exact absurd (show Fork.pectra ≤ Fork.altair from electra) (by decide)
  · exact absurd (show Fork.pectra ≤ Fork.bellatrix from electra) (by decide)
  · exact absurd (show Fork.pectra ≤ Fork.shapella from electra) (by decide)
  · exact absurd (show Fork.pectra ≤ Fork.dencun from electra) (by decide)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact (upgradeHezeFields_lists _).1

/-- From Electra, a step before Gloas leaves every validator that it creates with no exit epoch. -/
private theorem ExitFarFrom.of_chainStep {a b : ForkedBeaconState preset}
    (step : ChainStep config checks a b) (electra : .pectra ≤ a.fork)
    (early : a.fork < .glamsterdam) : ExitFarFrom a.state.validators.data.size b.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slotOk
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have atEpoched : ExitFarFrom a.state.validators.data.size epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact ExitFarFrom.of_epoch electra epochedOk (by rw [cachedEq])
      · cases epochedOk
        exact .of_size (by rw [cachedEq])
    have atAdvanced : ExitFarFrom a.state.validators.data.size { epoched with slot := next } :=
      atEpoched.of_data rfl
    exact (processUpgrades_induction (config := config) (checks := checks)
      (forked := ⟨a.fork, { epoched with slot := next }⟩) (after := b)
      (property := fun post => ExitFarFrom a.state.validators.data.size post.state ∧
        .pectra ≤ post.fork)
      (fun {pre post} kept ok =>
        ⟨kept.1.of_data (upgradeNext_validators kept.2 ok),
          Nat.le_trans kept.2 (Nat.le_of_lt post.property)⟩)
      ⟨atAdvanced, electra⟩ upgrades).1
  | block engine signed validate ok =>
    obtain ⟨input, last, started, operated, -, synced⟩ :=
      processBlock_operationsInput (applySignedBlock_ok ok).2.1
    have same := OperationsInput.validators_eq early started
    have fresh := processOperations_new_validator_epochs_unassigned operated
    intro i v large found
    have lastFound : last.validators.data[i]? = some v := by
      split at synced
      · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
        exact found
      · cases synced
        exact found
    exact (fresh i v (by rw [same]; exact large) lastFound).2

/-- Along a run from Electra, a validator can gain an exit epoch only through a departure charge.

The charge is at that exit epoch. -/
private theorem Run.charge_of_exit {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (i : ℕ) (unset : ∀ v, x.state.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH)
    (v : Validator) (found : y.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ c ∈ tail.departureCharges, c.index = i ∧ c.epoch = v.exitEpoch.toNat := by
  induction tail generalizing v with
  | nil => exact absurd (unset v found) assigned
  | @snoc middle last pre step ih =>
    have middleEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have middleElectra : .pectra ≤ middle.fork :=
      Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    cases present : middle.state.validators.data[i]? with
    | none =>
      have outside : middle.state.validators.data.size ≤ i :=
        Array.getElem?_eq_none_iff.mp present
      exact absurd (ExitFarFrom.of_chainStep step.chainStep middleElectra middleEarly i v outside
        found) assigned
    | some w =>
      by_cases pending : w.exitEpoch = FAR_FUTURE_EPOCH
      · obtain ⟨charge, member, index, epoch⟩ :=
          (Run.nil.snoc step).departure_charge_of_assigned i w v present found pending assigned
        exact ⟨charge, List.mem_append_right _ member, index, epoch⟩
      · obtain ⟨charge, member, index, epoch⟩ :=
          ih middleEarly w present pending
        obtain ⟨u, usedFound, kept⟩ :=
          (RegistryLifecycle.chainStep step.chainStep).validators i w present
        have same : u = v := Option.some.inj (usedFound.symm.trans found)
        refine ⟨charge, List.mem_append_left _ member, index, ?_⟩
        rw [epoch, ← same, kept.exitEpoch pending]

/-- Every departure charge of a run reads the effective balance of a state on its balance path.

It reads it at the charged position. -/
private theorem Run.charge_amount_mem {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (c : DepartureCharge) (member : c ∈ tail.departureCharges) :
    ∃ z ∈ tail.balancePath, effectiveAt z c.index = c.amount := by
  induction tail with
  | nil => simp [Run.departureCharges] at member
  | @snoc middle last pre step ih =>
    rcases List.mem_append.mp member with earlier | latest
    · obtain ⟨z, inPath, same⟩ := ih earlier
      exact ⟨z, by simp [Run.balancePath, inPath], same⟩
    · obtain ⟨⟨old, i⟩, present, added⟩ := List.mem_filterMap.mp latest
      dsimp only at added
      split at added
      · cases added
      · split at added
        · cases Option.some.inj added
          refine ⟨middle, ?_, ?_⟩
          · exact List.mem_append_right _ (List.mem_of_mem_head? step.balancePath_ends.1)
          · have found := (List.mem_zipIdx_iff_getElem?.mp present)
            rw [Array.getElem?_toList] at found
            simp [effectiveAt, found]
        · cases added

/-- The input of a step of a run lies on the run's balance path.

Its fork is no earlier than the run's first. -/
private theorem Run.input_mem_path {x y u w : ForkedBeaconState preset}
    {tail : Run config checks x y} {step : Step config checks u w} (member : tail.Contains step) :
    u ∈ tail.balancePath ∧ x.fork ≤ u.fork := by
  induction member with
  | last pre step =>
    refine ⟨?_, fork_le_of_chainSteps pre.chainSteps⟩
    exact List.mem_append_right _ (List.mem_of_mem_head? step.balancePath_ends.1)
  | earlier member next ih =>
    exact ⟨List.mem_append_left _ ih.1, ih.2⟩

/-- C1' (item 15, corrected).

Count the keys whose exit starts along C's run, with an exit epoch at most `high + 1`.

Each has an effective balance of at least `bound` along the run.

Each spends at least `bound` of the exit and consolidation queues' room up to epoch `high + 1`.

So their number times `bound` is at most the carry of both queues plus their churn per epoch.

`window` is `departure_charges_le_window_electra_cap` (DepartureQueue).

That is the private lemma `departure_charges_le_window_electra`.

It takes the exit cap `exitCap` in place of `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.

The integrator discharges it. -/
theorem Run.exits_started_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high bound churn : ℕ)
    (consolidationChurn : ℕ) (positive : 0 < bound)
    (churnOk : ∀ z ∈ tail.balancePath, ∀ c : Gwei,
      (if .pectra ≤ z.fork then exitChurnLimit config z.state else .ok 0) = .ok c →
        c.toNat ≤ churn)
    (consolidationChurnOk : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ consolidationChurn)
    (window : ∀ {x y : ForkedBeaconState preset} (tail : Run config checks x y)
      (electra : .pectra ≤ x.fork), y.fork < .glamsterdam → ∀ (high exitCap cap : ℕ),
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), tail.Contains step →
        ∀ rate : Gwei, exitChurnLimit config u.state = .ok rate → rate.toNat ≤ exitCap) →
      (∀ site ∈ tail.consolidationSites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) →
      ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
        (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
          (x.state.exitBalanceToConsume electra).toNat else 0) +
        (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
          (x.state.consolidationBalanceToConsume electra).toNat else 0) +
        (high + 2 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestExitEpoch electra).toNat) * exitCap +
        (high + 2 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestConsolidationEpoch electra).toNat) * cap) :
    ((Finset.range y.state.validators.data.size).filter fun i =>
      ((x.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH = FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH ≠ FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch.toNat)).getD 0 ≤ high + 1 ∧
      ∀ z ∈ tail.balancePath, bound ≤ effectiveAt z i).card * bound ≤
      (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
        (x.state.exitBalanceToConsume electra).toNat else 0) +
      (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
        (x.state.consolidationBalanceToConsume electra).toNat else 0) +
      (high + 2 - max (getCurrentEpoch x.state).toNat (x.state.earliestExitEpoch electra).toNat) *
        churn +
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (x.state.earliestConsolidationEpoch electra).toNat) * consolidationChurn := by
  classical
  have _ := positive
  refine Nat.le_trans ?_ (window tail electra early high churn consolidationChurn ?_
    consolidationChurnOk)
  swap
  · -- The input of each step lies on the balance path, at a fork from Electra.
    intro u w step member rate computed
    obtain ⟨onPath, forks⟩ := Run.input_mem_path member
    have fromElectra : .pectra ≤ u.fork := Nat.le_trans electra forks
    exact churnOk u onPath rate (by simpa only [fromElectra, ↓reduceIte] using computed)
  set kept := tail.departureCharges.filter fun c => c.epoch ≤ high + 1 with kept_def
  set chosen := (Finset.range y.state.validators.data.size).filter fun i =>
      ((x.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH = FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH ≠ FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch.toNat)).getD 0 ≤ high + 1 ∧
      ∀ z ∈ tail.balancePath, bound ≤ effectiveAt z i with chosen_def
  -- Each chosen key has a charge in the window at its position.
  have charged : ∀ i ∈ chosen, ∃ c ∈ kept, c.index = i := by
    intro i member
    simp only [chosen_def, Finset.mem_filter, Finset.mem_range] at member
    obtain ⟨inside, unset, assigned, within, _⟩ := member
    obtain ⟨current, found⟩ := Option.isSome_iff_exists.mp
      (by simpa using inside : (y.state.validators.data[i]?).isSome)
    simp only [found, Option.map_some, Option.getD_some] at assigned within
    obtain ⟨c, listed, index, epoch⟩ := Run.charge_of_exit tail electra early i
      (fun w located => by simpa [located] using unset) current found assigned
    exact ⟨c, List.mem_filter.mpr ⟨listed, by simpa [epoch] using within⟩, index⟩
  -- Those charges each spend at least `bound`.
  let owned := kept.filter fun c => decide (c.index ∈ chosen)
  have cardLe : chosen.card ≤ owned.length := by
    have covered : chosen ⊆ (owned.map (·.index)).toFinset := by
      intro i member
      obtain ⟨c, listed, index⟩ := charged i member
      simp only [List.mem_toFinset, List.mem_map, owned, List.mem_filter, decide_eq_true_eq]
      exact ⟨c, ⟨listed, index ▸ member⟩, index⟩
    exact (Finset.card_le_card covered).trans ((List.toFinset_card_le _).trans (by simp))
  have enough : ∀ a ∈ owned.map (·.amount), bound ≤ a := by
    intro a member
    obtain ⟨c, listed, rfl⟩ := List.mem_map.mp member
    simp only [owned, List.mem_filter, decide_eq_true_eq, kept_def] at listed
    obtain ⟨⟨inPath, -⟩, chosenKey⟩ := listed
    obtain ⟨z, onPath, amount⟩ := Run.charge_amount_mem tail c inPath
    simp only [chosen_def, Finset.mem_filter] at chosenKey
    rw [← amount]
    exact chosenKey.2.2.2.2 z onPath
  have owns : owned.length * bound ≤ (owned.map (·.amount)).sum := by
    simpa using List.length_nsmul_le_sum _ _ enough
  have sub : (owned.map (·.amount)).sum ≤ (kept.map (·.amount)).sum :=
    ((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _
  exact (Nat.mul_le_mul_right bound cardLe).trans (owns.trans sub)

/-! ## A potential that retains a decreasing floor -/

/-- One epoch keeps the fraction of the potential that the floor keeps, up to a rounding error.

The floor `φj` never rises, and stays within three halves of its start `φ0`.

The potential `dj` keeps the fraction `φj1 / φj` of itself, less the error `e`.

Then `d0` keeps the fraction `φj1 / φ0` of itself after `j + 1` epochs, less `3 e (j + 1) / 2` over
`φ0`. -/
private theorem chain_step (φ0 φj φj1 d0 dj dj1 e j : ℕ) (pos : 0 < φj) (anti : φj1 ≤ φj)
    (band : 2 * φ0 ≤ 3 * φj) (ih : 2 * d0 * φj ≤ 2 * dj * φ0 + 3 * e * j)
    (step : dj * φj1 ≤ dj1 * φj + e) :
    2 * d0 * φj1 ≤ 2 * dj1 * φ0 + 3 * e * (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc 2 * d0 * φj1 * φj = (2 * d0 * φj) * φj1 := by ring
    _ ≤ (2 * dj * φ0 + 3 * e * j) * φj1 := Nat.mul_le_mul_right _ ih
    _ = 2 * φ0 * (dj * φj1) + 3 * e * j * φj1 := by ring
    _ ≤ 2 * φ0 * (dj1 * φj + e) + 3 * e * j * φj := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ step
        · exact Nat.mul_le_mul_left _ anti
    _ = 2 * dj1 * φ0 * φj + 2 * φ0 * e + 3 * e * j * φj := by ring
    _ ≤ 2 * dj1 * φ0 * φj + 3 * φj * e + 3 * e * j * φj := by
        have := Nat.mul_le_mul_right e band
        omega
    _ = (2 * dj1 * φ0 + 3 * e * (j + 1)) * φj := by ring

/-! ## One epoch of a key against the floor path -/

/-- One epoch of a key keeps the fraction of its potential that the floor keeps.

The potential is the least of the balance and `K`, plus the downward band.

The epoch loses at most its pass.

The pass is charged at the effective balance `EB`.

That balance lies within the band above the balance, and below the cap.

The pass rate is at most `EB * (pen + 1) / φt`.

Here `φt = φt1 + pen` is the floor before the epoch, and `φt1` the floor after it.

The error is `K + band`, from the rounding. -/
private theorem step_arith (b' b cap K band pass X φt φt1 pen EB : ℕ)
    (hcap : K ≤ cap)
    (seg : min b' cap ≤ b + pass + X)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap)
    (pr : pass * φt ≤ EB * (pen + 1))
    (ph : φt = φt1 + pen) (hφ : 1 ≤ φt1) :
    (min b' K + band) * φt1 ≤ (min b K + band) * φt + (K + band) + X * φt := by
  set C := min b' cap with hC
  have hEB : EB ≤ C + band := by
    rcases le_total b' cap with h | h
    · have : C = b' := min_eq_left h
      omega
    · have : C = cap := min_eq_right h
      omega
  have hcle : min b' K ≤ C := by
    apply le_min (min_le_left _ _)
    exact (min_le_right _ _).trans hcap
  -- the key's balance after the epoch, scaled
  have bound : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := by
    have h1 : C * φt ≤ (b + pass + X) * φt := Nat.mul_le_mul_right _ seg
    have h2 : pass * φt ≤ (C + band) * (pen + 1) :=
      pr.trans (Nat.mul_le_mul_right _ hEB)
    nlinarith
  by_cases big : K ≤ b
  · have : min b K = K := min_eq_right big
    rw [this]
    have : min b' K ≤ K := min_le_right _ _
    have : φt1 ≤ φt := by omega
    nlinarith
  · have small : b < K := Nat.lt_of_not_ge big
    have : min b K = b := min_eq_left small.le
    rw [this]
    -- c ≤ C, and the bound on C·φt1
    set c := min b' K with hc
    have hcK : c ≤ K := min_le_right _ _
    have key : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := bound
    -- (C + band) * (pen + 1) = (C + band) * pen + (C + band)
    have e1 : (C + band) * (pen + 1) = (C + band) * pen + (C + band) := by ring
    -- C * φt - (C+band) pen = C * φt1 - band * pen
    have e2 : C * φt = C * φt1 + C * pen := by rw [ph]; ring
    have lower : (C + band) * φt1 ≤ (b + band) * φt + (C + band) + X * φt := by
      rw [ph] at key ⊢
      nlinarith
    -- replace C by c: C could exceed K, then use the shape of the loss
    by_cases cK : C ≤ K
    · have hcC : c = C := le_antisymm hcle (le_min (min_le_left _ _) cK)
      rw [hcC]
      have : (C + band) ≤ (K + band) := by omega
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      have h3 : C * φt1 ≤ b * φt + C + band * (pen + 1) + X * φt := by
        rw [ph] at key
        nlinarith
      have h4 : K * φt1 + C ≤ C * φt1 + K := by
        have : K * (φt1 - 1) ≤ C * (φt1 - 1) := Nat.mul_le_mul_right _ above.le
        have e1 : K * (φt1 - 1) + K = K * φt1 := by
          have := Nat.mul_le_mul_left K hφ
          rw [Nat.mul_sub]; omega
        have e2 : C * (φt1 - 1) + C = C * φt1 := by
          have := Nat.mul_le_mul_left C hφ
          rw [Nat.mul_sub]; omega
        omega
      have h5 : (c + band) * φt1 ≤ (K + band) * φt1 := Nat.mul_le_mul_right _ (by omega)
      rw [ph]
      nlinarith

/-- One epoch of a key, with the initial penalty of a slashing in it.

The penalty is at most `EB / Q`, and the epoch is charged `Bq` for it, with `K + band ≤ Q * Bq`.

The floor after the epoch stays at least `6 Q` and within three halves of the floor before. -/
private theorem step_arith_slash (b' b cap K band pass X sl Q Bq φt φt1 pen EB : ℕ)
    (hcap : K ≤ cap) (hQ : 2 ≤ Q) (hB : K + band ≤ Q * Bq)
    (seg : min b' cap ≤ b + pass + X + sl) (hsl : Q * sl ≤ EB)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap)
    (pr : pass * φt ≤ EB * (pen + 1))
    (ph : φt = φt1 + pen) (hφ : 6 * Q ≤ φt1) (hband : 2 * φt ≤ 3 * φt1) :
    (min b' K + band) * φt1 ≤
      (min b K + band) * φt + (K + band) + (X + (if sl = 0 then 0 else Bq)) * φt := by
  by_cases noSlash : sl = 0
  · subst noSlash
    simp only [ite_true, Nat.add_zero, Nat.add_zero] at seg ⊢
    have := step_arith b' b cap K band pass X φt φt1 pen EB hcap (by simpa using seg) hyst
      hcapEB pr ph (by omega)
    simpa using this
  · simp only [noSlash, ite_false]
    set C := min b' cap with hC
    have hEB : EB ≤ C + band := by
      rcases le_total b' cap with h | h
      · have : C = b' := min_eq_left h
        omega
      · have : C = cap := min_eq_right h
        omega
    have hcle : min b' K ≤ C := le_min (min_le_left _ _) ((min_le_right _ _).trans hcap)
    by_cases cK : C ≤ K
    · -- the penalty is at most `Bq`, and the case is that without slashing
      have slB : sl ≤ Bq := by
        have : Q * sl ≤ Q * Bq := by omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      have := step_arith b' b cap K band pass (X + sl) φt φt1 pen EB hcap
        (by omega) hyst hcapEB pr ph (by omega)
      have h2 : (X + sl) * φt ≤ (X + Bq) * φt := Nat.mul_le_mul_right _ (by omega)
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      by_cases big : K ≤ b
      · have : min b K = K := min_eq_right big
        rw [this]
        have : min b' K ≤ K := min_le_right _ _
        have : φt1 ≤ φt := by omega
        nlinarith
      · have small : b < K := Nat.lt_of_not_ge big
        have : min b K = b := min_eq_left small.le
        rw [this]
        have hc : min b' K ≤ K := min_le_right _ _
        obtain ⟨h, hh⟩ : ∃ h, Q * φt1 = h + Q + φt := by
          refine ⟨Q * φt1 - Q - φt, ?_⟩
          have : 3 * (Q * φt1) ≥ 2 * Q * φt := by nlinarith
          have : Q * φt1 ≥ Q + φt := by nlinarith
          omega
        have h1 : Q * C * φt ≤ Q * b * φt + Q * (C + band) * (pen + 1) + Q * X * φt +
            (C + band) * φt := by
          have a1 : C * φt ≤ (b + pass + X + sl) * φt := Nat.mul_le_mul_right _ seg
          have a2 : pass * φt ≤ (C + band) * (pen + 1) := pr.trans (Nat.mul_le_mul_right _ hEB)
          have a3 : Q * sl ≤ C + band := hsl.trans hEB
          have a4 : Q * (sl * φt) ≤ (C + band) * φt := by
            rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ a3
          have a5 : Q * (pass * φt) ≤ Q * ((C + band) * (pen + 1)) := Nat.mul_le_mul_left _ a2
          have a6 : Q * (C * φt) ≤ Q * ((b + pass + X + sl) * φt) := Nat.mul_le_mul_left _ a1
          have a7 : Q * ((b + pass + X + sl) * φt) =
              Q * (b * φt) + Q * (pass * φt) + Q * (X * φt) + Q * (sl * φt) := by ring
          have a8 : Q * C * φt = Q * (C * φt) := by ring
          have a9 : Q * b * φt = Q * (b * φt) := by ring
          have a10 : Q * (C + band) * (pen + 1) = Q * ((C + band) * (pen + 1)) := by ring
          have a11 : Q * X * φt = Q * (X * φt) := by ring
          rw [a8, a9, a10, a11]
          omega
        have e1 : Q * C * φt = Q * C * φt1 + Q * C * pen := by rw [ph]; ring
        have e2 : Q * (C + band) * (pen + 1) =
            Q * C * pen + Q * C + Q * band * pen + Q * band := by ring
        have e3 : C * (Q * φt1) = C * h + C * Q + C * φt := by rw [hh]; ring
        have e4 : (C + band) * φt = C * φt + band * φt := by ring
        have hC : C * h ≤ Q * b * φt + Q * band * pen + Q * band + Q * X * φt + band * φt := by
          linarith [h1, e1, e2, e3, e4]
        have h2 : K * h ≤ C * h := Nat.mul_le_mul_right _ above.le
        have e5 : K * (Q * φt1) = K * h + K * Q + K * φt := by rw [hh]; ring
        have e6 : Q * band * φt = Q * band * φt1 + Q * band * pen := by rw [ph]; ring
        have h3 : Q * K * φt1 + Q * band * φt1 ≤
            Q * b * φt + Q * band * φt + Q * (K + band) + Q * X * φt + (K + band) * φt := by
          have e7 : (K + band) * φt = K * φt + band * φt := by ring
          have e8 : Q * (K + band) = Q * K + Q * band := by ring
          linarith [hC, h2, e5, e6, e7, e8]
        have h4 : (K + band) * φt ≤ Q * Bq * φt := Nat.mul_le_mul_right _ hB
        have h5 : (min b' K + band) * φt1 ≤ (K + band) * φt1 := Nat.mul_le_mul_right _ (by omega)
        have h6 : Q * ((K + band) * φt1) ≤
            Q * ((b + band) * φt + (K + band) + (X + Bq) * φt) := by
          have e9 : Q * ((K + band) * φt1) = Q * K * φt1 + Q * band * φt1 := by ring
          have e10 : Q * ((b + band) * φt + (K + band) + (X + Bq) * φt) =
              Q * b * φt + Q * band * φt + Q * (K + band) + Q * X * φt + Q * Bq * φt := by ring
          rw [e9, e10]
          omega
        have h7 := Nat.le_of_mul_le_mul_left h6 (by omega)
        omega

/-! ## The state before a new key is scheduled -/

/-- One step of a chain moves the current epoch on by at most one. -/
private theorem ChainStep.epoch_le_succ {a b : ForkedBeaconState preset}
    (step : ChainStep config checks a b) :
    (getCurrentEpoch b.state).toNat ≤ (getCurrentEpoch a.state).toNat + 1 := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have kept := processUpgrades_slot upgrades
    have next := advanceSlot_slot slotOk
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    simp only at kept next ⊢
    rw [kept, next]
    by_cases zero : preset.SLOTS_PER_EPOCH.toNat = 0
    · simp [zero]
    · have positive : 1 ≤ preset.SLOTS_PER_EPOCH.toNat := Nat.pos_of_ne_zero zero
      calc (a.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat
          ≤ (a.state.slot.toNat + preset.SLOTS_PER_EPOCH.toNat) /
              preset.SLOTS_PER_EPOCH.toNat :=
            Nat.div_le_div_right (Nat.add_le_add_left positive _)
        _ = a.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 :=
            Nat.add_div_right _ positive
  | block engine signed validate ok =>
    have same := processBlock_slot (applySignedBlock_ok ok).2.1
    simp only [getCurrentEpoch, same]
    exact Nat.le_succ _

/-- A run that starts at or before an epoch and ends at or after it passes a state of that epoch. -/
private theorem Run.exists_epoch_split {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (k : ℕ)
    (low : (getCurrentEpoch x.state).toNat ≤ k) (high : k ≤ (getCurrentEpoch y.state).toNat) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y),
      (getCurrentEpoch z.state).toNat = k ∧ tail = pre.append post := by
  induction tail with
  | nil => exact ⟨x, .nil, .nil, by omega, rfl⟩
  | @snoc middle last pre step ih =>
    by_cases inside : k ≤ (getCurrentEpoch middle.state).toNat
    · obtain ⟨z, a, b, epoch, split⟩ := ih inside
      refine ⟨z, a, b.snoc step, epoch, ?_⟩
      rw [split]
      rfl
    · have bound := ChainStep.epoch_le_succ step.chainStep
      exact ⟨last, pre.snoc step, .nil, by omega, rfl⟩

/-- A key that is active at the end of a run is scheduled two epochs before its activation.

It is not active by the epoch after the start of the run.

At the state `z` that the run reaches in that epoch, the key holds its activation epoch `A`.

Activity up to `A` is fixed at `z`, since the seed lookahead is at least three epochs. -/
private theorem Run.start_state {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (window : preset.ExitWindowFixed) (i : ℕ)
    (pending : ∀ v, x.state.validators.data[i]? = some v →
      (getCurrentEpoch x.state).toNat + 1 < v.activationEpoch.toNat)
    (active : isActiveAt y.state (getCurrentEpoch y.state) i = true) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y)
      (v0 vy : Validator), tail = pre.append post ∧ z.state.validators.data[i]? = some v0 ∧
      y.state.validators.data[i]? = some vy ∧ v0.activationEpoch = vy.activationEpoch ∧
      (getCurrentEpoch z.state).toNat + 2 = vy.activationEpoch.toNat ∧
      vy.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat ∧
      (getCurrentEpoch y.state).toNat < vy.exitEpoch.toNat := by
  obtain ⟨vy, foundY, activeY⟩ := isActiveAt_eq_true_iff.mp active
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeY
  have lowY := UInt64.le_iff_toNat_le.mp activeY.1
  have highY := UInt64.lt_iff_toNat_lt.mp activeY.2
  have exitBound := vy.exitEpoch.toNat_lt
  have fixedWindow := window.lookahead
  -- Activity at the epoch `A` of the key, as the end state reads it.
  have activeAtA : isActiveAt y.state vy.activationEpoch i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨vy, foundY, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨UInt64.le_refl _, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
  have kept (h : ForkedBeaconState preset) (run : Run config checks h y)
      (le : vy.activationEpoch.toNat ≤ (getCurrentEpoch h.state).toNat +
        preset.MAX_SEED_LOOKAHEAD.toNat) :
      isActiveAt h.state vy.activationEpoch i = true := by
    have bound : vy.activationEpoch ≤ activityFixedEpoch h.state := by
      rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
      omega
    rw [← activeKept_of_chainSteps run.chainSteps _ bound]
    exact activeAtA
  -- The key is not active by the epoch after the start of the run.
  have later : (getCurrentEpoch x.state).toNat + 1 < vy.activationEpoch.toNat := by
    by_contra early
    have atX := kept x tail (by omega)
    obtain ⟨vx, foundX, activeX⟩ := isActiveAt_eq_true_iff.mp atX
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeX
    have := pending vx foundX
    have := UInt64.le_iff_toNat_le.mp activeX.1
    omega
  have startEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  obtain ⟨z, pre, post, epoch, split⟩ :=
    Run.exists_epoch_split tail (vy.activationEpoch.toNat - 2) (by omega) (by omega)
  have atZ := kept z post (by omega)
  obtain ⟨v0, foundZ, activeZ⟩ := isActiveAt_eq_true_iff.mp atZ
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeZ
  have assigned : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have := UInt64.le_iff_toNat_le.mp activeZ.1
    rw [far] at this
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  obtain ⟨w, foundW, life⟩ := post.registryLifecycle.validators i v0 foundZ
  have same : w = vy := Option.some.inj (foundW.symm.trans foundY)
  subst same
  exact ⟨z, pre, post, v0, w, split, foundZ, foundY, (life.activationEpoch assigned).symm,
    by omega, lowY, highY⟩

/-! ## Hypotheses of the new key's floor -/

/-- A key scheduled for activation holds the maximum effective balance and is unslashed (prover E).

The key has an assigned activation or eligibility epoch.

It is at least two epochs before its activation.

Then its balance is at least its effective balance, which is at least `MAX_EFFECTIVE_BALANCE`. -/
def ScheduledEligibleBalanceElectra {f : Fork} (s : BeaconState preset f) : Prop :=
  .pectra ≤ f → ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
    (v.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH) →
    getCurrentEpoch s + 1 < v.activationEpoch →
    (∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance ∧ v.slashed = false

/-- The invariant of a scheduled key holds at every state reached from genesis (prover E). -/
def EligibleBalanceStatement (preset : Preset) (config : Config) (checks : SignatureChecks) :
    Prop :=
  ∀ {g x : ForkedBeaconState preset} (_run : Run config checks g x)
    (_genesis : Genesis (config := config) (checks := checks) g)
    (_activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (_compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (_aligned : MaxEffectiveBalancesAligned preset) (_early : x.fork < .glamsterdam)
    (_finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH),
    ScheduledEligibleBalanceElectra x.state

/-- The cap of a key at a state, `0` past the registry (prover D's `capAt`). -/
def keyCapAt (z : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  ((z.state.validators.data[i]?).map fun v =>
    (withdrawalMaxEffectiveBalance preset z.fork v).toNat).getD 0

/-- H4: a balance floor along a run gives an effective balance floor.

Suppose the key's balance stays at least `floor` at every state of the run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three numbers.

They are its effective balance at the start, `capLow`, and `floor` less one increment. -/
def EffectiveFloorStatement (preset : Preset) (config : Config) (checks : SignatureChecks) :
    Prop :=
  ∀ {x y : ForkedBeaconState preset} (_tail : Run config checks x y)
    (_early : y.fork < .glamsterdam)
    (_fulu : .fusaka ≤ x.fork) (_bands : preset.IncrementWithinUpwardBand) (i : ℕ)
    (_inside : i < x.state.validators.data.size) (floor capLow : ℕ)
    (_balanceFloor : ∀ z ∈ _tail.balancePath, floor ≤ actualBalanceAt z i)
    (_capFloor : ∀ z ∈ _tail.balancePath, capLow ≤ keyCapAt z i),
    min (effectiveAt x i) (min capLow (floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i

/-- Right after a slot step that moves the epoch on, the effective balances lie within the bands.

The step ran the epoch transition, and its upgrades keep the bands. -/
def EpochStartHysteresis (preset : Preset) (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {a b : ForkedBeaconState preset} (_step : Step config checks a b),
    getCurrentEpoch a.state < getCurrentEpoch b.state → Hysteresis b.state

open DirectSafety.Apriori in
/-- From Electra, the ceiling of a window grows with the epoch of the window.

It is `stakeCeilingAt_mono` (PinDriftBound, private). -/
def CeilingMonoStatement (preset : Preset) (config : Config) : Prop :=
  ∀ {x : ForkedBeaconState preset} {high : ℕ} (_electra : .pectra ≤ x.fork) {s t : ℕ},
    s ≤ t → stakeCeilingAt config x high s ≤ stakeCeilingAt config x high t

open DirectSafety.Apriori in
/-- The floor of a window falls with the epoch of the window.

It is `stakeFloorAt_anti` (PinDriftBound, private). -/
def FloorAntiStatement (preset : Preset) (config : Config) : Prop :=
  ∀ {x : ForkedBeaconState preset} {high s t : ℕ},
    s ≤ t → stakeFloorAt config x high t ≤ stakeFloorAt config x high s

/-! ## The scores along a run -/

open DirectSafety.Apriori in
/-- On a run from `x` from Altair, each inactivity score of a state is small, new positions too.

It is `scoresBelowAt_run` (Branch.lean) for every position of the registry.

The score is at most `sigma + bias * t`, with `sigma` the start score that the floor reads.

Here `t` is the number of epochs from `x`, so the number of updates of the scores so far.

A position that the run adds starts with the score zero.

It then rises by at most the bias per epoch. -/
def RunScoresStatement (preset : Preset) (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {x y : ForkedBeaconState preset} (_run : Run config checks x y) (_altair : .altair ≤ x.fork)
    (_early : y.fork < .glamsterdam) (_era : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (later : .altair ≤ y.fork) {i : ℕ} {score : UInt64}
    (_found : (y.state.inactivityScores later).data[i]? = some score),
    score.toNat ≤ startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat)

/-! ## The floor of one epoch of a key -/

/-- The sync debit of one key in one event (PinDriftBound's private `syncDebit`, verbatim). -/
def keySyncDebit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The rate at which one rewards pass can debit a key, read at the last state of the epoch.

It is PinDriftBound's private `passPenaltyRate`, verbatim. -/
def passRate (config : Config) (z : ForkedBeaconState preset) (v : ℕ) : ℕ :=
  let total := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (∑ i ∈ (Finset.range z.state.validators.data.size).filter
        (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
      ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
  let score := if altair : .altair ≤ z.fork then
      (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
      effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
    effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat)

open DirectSafety.Apriori.Internal Classical in
/-- The rewards pass debits a key at most its pass rate at the last state of the epoch.

It is the instance of `segment_passDebit_le` (PinDriftBound, private) at the last step of a segment.

The segment `pre` stays in the epoch of `m`, and the slot step `ok` leaves it.

The pass is a debit only when it reads a total active balance at `z`.

Otherwise it records no penalty. -/
def PassBoundStatement (preset : Preset) (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {m z n : ForkedBeaconState preset} (pre : Run config checks m z)
    (ok : advanceSlotAcross config checks z = .ok n),
    .altair ≤ m.fork → n.fork < .glamsterdam →
    getCurrentEpoch z.state = getCurrentEpoch m.state →
    (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
    ∀ (i : ℕ) {events : List (BalanceEvent preset)},
      (pre.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat = .ok events →
      (events.map (penaltyDebit i)).sum ≤
        if ∃ total, getTotalActiveBalance z.state = .ok total then passRate config z i else 0

open DirectSafety.Apriori.Internal Classical in
/-- The floor of one key over a run that crosses at most one epoch boundary.

The run starts at `m`, reached from genesis, and ends at `n`, from Fulu and before Gloas.

It stays in the epoch of `m`.

Or it ends with the slot step that leaves that epoch, at the first slot of the next epoch.

The key must be assigned an activation at `m`, and not exit by the epoch after that of `m`.

If it is slashed at `m`, its delayed slashing penalty must not be due by the epoch of `n`.

Take any `C` below the key's largest effective balance at `m`.

The least of the balance at `m` and `C` is at most the balance at `n`, plus its debits.

The first debit is the pass at the last state `z` of the first epoch, if the run crosses its end.

The pass is a debit only when it reads a total active balance there.

Otherwise it records no penalty.

The others are the key's sync debits and its payments from the queue of partial withdrawals.

The last is its initial slashing penalty, if the run slashes it.

That penalty is the effective balance at `m` over the slashing quotient.

The effective balance changes only at the boundary, after any slashing before it. -/
def EpochFloorStatement (preset : Preset) (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {g m n : ForkedBeaconState preset} (_shared : Run config checks g m)
    (_genesis : Genesis (config := config) (checks := checks) g) (_caps : CapOrder preset)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (_vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat)
    (_positive :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat)
    (r : Run config checks m n),
    .fusaka ≤ m.fork → n.fork < .glamsterdam →
    (getCurrentEpoch n.state = getCurrentEpoch m.state ∨
      ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z)
        (ok : advanceSlotAcross config checks z = .ok n),
        r = pre.snoc (Step.slot ok) ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
          (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1) →
    ∀ (i : ℕ) (val : Validator), m.state.validators.data[i]? = some val →
    val.activationEpoch ≠ FAR_FUTURE_EPOCH →
    (∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat) →
    (val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat) →
    ∀ C : ℕ, C ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat →
    ∀ {events : List (BalanceEvent preset)},
      r.balanceEvents (getCurrentEpoch m.state).toNat = .ok events →
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      min (actualBalanceAt m i) C ≤ actualBalanceAt n i +
        (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
            ∃ total, getTotalActiveBalance z.state = .ok total then passRate config z i else 0) +
        (events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then effectiveAt m i /
            (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0)

/-! ## The pass rate against the floor path -/

section FloorPath

open DirectSafety.Apriori

/-- The base-reward part of the pass rate fits the base-reward part of the floor's penalty.

The pass reads the root of a total at least that of the floor.

The floor's penalty is read at a weight at least the floor.

The constants satisfy `a * d + b * d ≤ c * b`, which leaves room for the rounding. -/
private theorem pass_first (a b c d BRF EB φ w s T : ℕ) (hb : 0 < b) (hd : 0 < d) (hs : 0 < s)
    (sT : s ≤ T) (sφ : s ≤ φ) (hw : φ ≤ w) (hBRF : 1 ≤ BRF) (ratio : a * d + b * d ≤ c * b) :
    a * BRF * EB / (b * T) * φ ≤ EB * (c * BRF * w / (d * s)) := by
  set Q1 := a * BRF * EB / (b * T) with hQ1
  set P := c * BRF * w / (d * s) with hP
  have h1 : Q1 * (b * T) ≤ a * BRF * EB := Nat.div_mul_le_self _ _
  have h2 : c * BRF * w < (P + 1) * (d * s) := by
    have := Nat.lt_mul_div_succ (c * BRF * w) (Nat.mul_pos hd hs)
    rw [← hP] at this
    linarith
  have step1 : Q1 * φ * (b * d * s) ≤ a * d * BRF * EB * φ := by
    calc Q1 * φ * (b * d * s) = (Q1 * (b * s)) * φ * d := by ring
      _ ≤ (Q1 * (b * T)) * φ * d := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ sT)
      _ ≤ (a * BRF * EB) * φ * d := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ h1
      _ = a * d * BRF * EB * φ := by ring
  have step2 : b * EB * (d * s) ≤ b * d * BRF * EB * φ := by
    have : d * s ≤ d * (BRF * φ) :=
      Nat.mul_le_mul_left _ (sφ.trans (Nat.le_mul_of_pos_left _ hBRF))
    calc b * EB * (d * s) ≤ b * EB * (d * (BRF * φ)) := Nat.mul_le_mul_left _ this
      _ = b * d * BRF * EB * φ := by ring
  have step3 : (a * d + b * d) * BRF * EB * φ ≤ b * EB * (c * BRF * w) := by
    calc (a * d + b * d) * BRF * EB * φ ≤ (c * b) * BRF * EB * φ := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact ratio
      _ ≤ (c * b) * BRF * EB * w := Nat.mul_le_mul_left _ hw
      _ = b * EB * (c * BRF * w) := by ring
  have step4 : b * EB * (c * BRF * w) ≤ b * EB * (P * (d * s)) + b * EB * (d * s) := by
    have : c * BRF * w ≤ P * (d * s) + d * s := by linarith
    calc b * EB * (c * BRF * w) ≤ b * EB * (P * (d * s) + d * s) := Nat.mul_le_mul_left _ this
      _ = b * EB * (P * (d * s)) + b * EB * (d * s) := by ring
  have key : Q1 * φ * (b * d * s) ≤ EB * P * (b * d * s) := by
    have e : (a * d + b * d) * BRF * EB * φ = a * d * BRF * EB * φ + b * d * BRF * EB * φ := by ring
    have e2 : b * EB * (P * (d * s)) = EB * P * (b * d * s) := by ring
    omega
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos (Nat.mul_pos hb hd) hs)

/-- The leak part of the pass rate fits the leak part of the floor's penalty.

The divisor of the penalty is at most the divisor of the pass.

The score of the pass is at most that of the penalty, and the rounding costs one. -/
private theorem pass_second (bias IPQ IPD EB score S' φ w : ℕ) (hIPD : 0 < IPD)
    (div : IPD ≤ bias * IPQ) (sc : score + bias ≤ S') (hw : φ ≤ w) :
    EB * (score + bias) / (bias * IPQ) * φ ≤ EB * (w * S' / IPD + 1) := by
  set Q2 := EB * (score + bias) / (bias * IPQ) with hQ2
  set R := w * S' / IPD with hR
  have h0 : Q2 ≤ EB * (score + bias) / IPD := Nat.div_le_div_left div hIPD
  have h1 : (EB * (score + bias) / IPD) * IPD ≤ EB * (score + bias) := Nat.div_mul_le_self _ _
  have h2 : w * S' < (R + 1) * IPD := by
    have := Nat.lt_mul_div_succ (w * S') hIPD
    rw [← hR] at this
    linarith
  have key : Q2 * φ * IPD ≤ EB * (R + 1) * IPD := by
    calc Q2 * φ * IPD ≤ (EB * (score + bias) / IPD) * φ * IPD :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
      _ = ((EB * (score + bias) / IPD) * IPD) * φ := by ring
      _ ≤ (EB * (score + bias)) * φ := Nat.mul_le_mul_right _ h1
      _ ≤ (EB * S') * w := Nat.mul_le_mul (Nat.mul_le_mul_left _ sc) hw
      _ = EB * (w * S') := by ring
      _ ≤ EB * ((R + 1) * IPD) := Nat.mul_le_mul_left _ h2.le
      _ = EB * (R + 1) * IPD := by ring
  exact Nat.le_of_mul_le_mul_right key hIPD
/-- The floor path falls by the penalty of its epoch. -/
private theorem floor_succ (x : ForkedBeaconState preset) (high t : ℕ) :
    stakeFloorAt config x high (t + 1) = stakeFloorAt config x high t -
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by
  rfl

/-- The pass rate of a key against the fall of the floor path.

The floor lies below the total active balance read by the pass, and below the weight of the penalty.

The floor after the epoch is positive, so its fall is the penalty.

The score of the key at the pass, plus the bias, is within that of the penalty.

The rate times the floor is at most the key's effective balance times the fall, plus one. -/
private theorem passRate_mul_le {x z : ForkedBeaconState preset} (high t i : ℕ)
    (total : Gwei) (totalOk : getTotalActiveBalance z.state = .ok total)
    (floor : stakeFloorAt config x high t ≤ total.toNat)
    (floorLe : stakeFloorAt config x high t ≤
      stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (positive : 0 < stakeFloorAt config x high (t + 1))
    (divisor : 0 < inactivityPenaltyDivisor preset config)
    (factor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat)
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤
        startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) :
    passRate config z i * stakeFloorAt config x high t ≤
      effectiveAt z i *
        (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) + 1) := by
  have succ := floor_succ (config := config) x high t
  have eq : stakeFloorAt config x high t = stakeFloorAt config x high (t + 1) +
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by
    omega
  have pen : stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) =
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by omega
  rw [pen]
  have totalValue := getTotalActiveBalance_toNat totalOk
  have fpos : 0 < stakeFloorAt config x high t := by omega
  have rootPos : 0 < (stakeFloorAt config x high t).sqrt := Nat.sqrt_pos.mpr fpos
  have roots := Nat.sqrt_le_sqrt floor
  have quotient : inactivityPenaltyDivisor preset config ≤ config.INACTIVITY_SCORE_BIAS.toNat *
      (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat := by
    unfold inactivityPenaltyDivisor
    apply Nat.mul_le_mul_left
    simp only [EthLib.Consensus.parameters]
    split_ifs <;> omega
  have first := pass_first (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat)
    WEIGHT_DENOMINATOR.toNat (3 + BASE_REWARDS_PER_EPOCH.toNat) BASE_REWARDS_PER_EPOCH.toNat
    preset.BASE_REWARD_FACTOR.toNat (effectiveAt z i) (stakeFloorAt config x high t)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (stakeFloorAt config x high t).sqrt total.toNat.sqrt (by decide) (by decide) rootPos
    roots (Nat.sqrt_le_self _) floorLe factor (by decide)
  have second := pass_second config.INACTIVITY_SCORE_BIAS.toNat
    (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat
    (inactivityPenaltyDivisor preset config) (effectiveAt z i) _
    (startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1))
    (stakeFloorAt config x high t)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) divisor quotient scored floorLe
  unfold passRate epochPenalty
  dsimp only
  rw [totalValue] at first
  rw [add_mul]
  linarith

end FloorPath

/-! ## One epoch of a new key -/

section Epoch

open DirectSafety.Apriori DirectSafety.Apriori.Internal

/-- Every fork from Fulu to before Gloas has the slashing quotient of Fulu. -/
private theorem mspq_eq (f : Fork) (h1 : .fusaka ≤ f) (h2 : f < .glamsterdam) :
    (EthLib.Consensus.parameters preset f).MIN_SLASHING_PENALTY_QUOTIENT =
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT := by
  cases f <;> first | rfl | (exfalso; revert h1 h2; decide)

/-- One epoch with no pass, and the penalty of a slashing in it. -/
private theorem same_arith (b' b cap K band X sl Q Bq EB : ℕ)
    (hcap : K ≤ cap) (hQ : 2 ≤ Q) (hB : K + band ≤ Q * Bq)
    (seg : min b' cap ≤ b + X + sl) (hsl : Q * sl ≤ EB)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap) :
    min b' K ≤ b + X + (if sl = 0 then 0 else Bq) := by
  by_cases z : sl = 0
  · subst z
    simp only [ite_true] at *
    have : min b' K ≤ min b' cap := min_le_min_left _ hcap
    omega
  · simp only [z, ite_false]
    set C := min b' cap with hC
    have hEB : EB ≤ C + band := by
      rcases le_total b' cap with h | h
      · have : C = b' := min_eq_left h
        omega
      · have : C = cap := min_eq_right h
        omega
    by_cases cK : C ≤ K
    · have hcle : min b' K ≤ C := le_min (min_le_left _ _) ((min_le_right _ _).trans hcap)
      have slB : sl ≤ Bq := by
        have : Q * sl ≤ Q * Bq := by omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      have : min b' K = K := by
        apply min_eq_right
        have := min_le_left b' cap
        omega
      rw [this]
      have : Q * sl ≤ Q * (Bq + (C - K)) := by
        have h1 : Q * (C - K) ≥ C - K := Nat.le_mul_of_pos_left _ (by omega)
        have : Q * (Bq + (C - K)) = Q * Bq + Q * (C - K) := by ring
        omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega

/-- The charge for the slashing of a key: the rounded-up initial penalty of the least stake. -/
private def newBq (preset : Preset) : ℕ :=
  (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
    (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat

/-- The standing hypotheses of the floor of a new key.

They are the guard and the facts that it reads.

They also hold the preset facts, and the statements that the floor takes as hypotheses. -/
private structure Ctx (config : Config) (checks : SignatureChecks) {preset : Preset}
    (g x : ForkedBeaconState preset) (high : ℕ) where
  shared : Run config checks g x
  genesis : Genesis (config := config) (checks := checks) g
  parameters : DirectSafety.Parameters preset
  caps : CapOrder preset
  aligned : MaxEffectiveBalancesAligned preset
  twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  electra : .pectra ≤ x.fork
  fulu : .fusaka ≤ x.fork
  guard : aprioriGuardAt config x high
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
  big : 9 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
    stakeFloorAt config x high 0
  factor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat
  quotientTwo :
    2 ≤ (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  margin : 2400 * (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
      preset.MAX_EFFECTIVE_BALANCE.toNat /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - 1) + 2400 * preset.downwardBand + 2400 * newBq preset ≤
    1591 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
  room : 600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0
  epochFloor : EpochFloorStatement preset config checks
  scores : RunScoresStatement preset config checks
  hysteresis : EpochStartHysteresis preset config checks
  mono : CeilingMonoStatement preset config
  anti : FloorAntiStatement preset config

/-- The total active balance of a state of a run lies between the floor and the ceiling.

It is `total_within_guard` (PinDriftBound, private) at the index of the state. -/
private theorem Ctx.total_bounds {g x z : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (run : Run config checks x z) (early : z.fork < .glamsterdam)
    (within : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    stakeFloorAt config x high (ix x z) ≤ total.toNat ∧
      total.toNat ≤ stakeCeilingAt config x high (ix x z) := by
  obtain ⟨ceiling, -, floor⟩ := ceilingFloor_electra c.shared run high
    ⟨c.genesis, c.parameters, c.caps, c.aligned, early, within, c.guard⟩ c.twoSlots c.electra
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps run.chainSteps) early
  have unit := (ceiling_unit_of_guard c.shared c.genesis c.aligned xEarly c.electra c.guard).trans
    (c.mono c.electra (Nat.zero_le (ix x z)))
  refine ⟨floor total totalOk, ?_⟩
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [value]
  exact max_le unit ceiling

/-- Along the window, the floor stays within three halves of its start.

The start floor is below the stake at the start, which the funded stake covers.

The funded stake is below the first ceiling, which is below the last.

The guard asks that twice the last ceiling be at most three times the last floor. -/
private theorem Ctx.ratio {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (early : x.fork < .glamsterdam) {s : ℕ}
    (inside : s ≤ high + 1 - (getCurrentEpoch x.state).toNat)
    (within : (getCurrentEpoch x.state).toNat ≤ high + 1) :
    2 * stakeFloorAt config x high 0 ≤ 3 * stakeFloorAt config x high s := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge c.electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id c.guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  have first : stakeFloorAt config x high 0 ≤ stakeCeilingAt config x high 0 :=
    (floor_initial_le_reference x high).trans
      ((funding_active_le x early (c.shared.pubkeysDistinct c.genesis)).trans
        (funded_le_ceiling_initial c.electra))
  have anti : stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high s := c.anti inside
  have mono : stakeCeilingAt config x high 0 ≤
      stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) :=
    c.mono c.electra (Nat.zero_le _)
  have ratio' : 2 * stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) := by
    simpa [stakeCeilingAt, stakeFloorAt, zero] using ratio
  omega

/-- The debits of key `i` in a list of events: its sync debits and its partial payments. -/
private def keyDebits (i : ℕ) (events : List (BalanceEvent preset)) : ℕ :=
  (events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum

private theorem keyDebits_append (i : ℕ) (a b : List (BalanceEvent preset)) :
    keyDebits i (a ++ b) = keyDebits i a + keyDebits i b := by
  simp only [keyDebits, List.map_append, List.sum_append]
  omega

/-- The key is charged `newBq` once it is slashed. -/
private def slashedCharge (preset : Preset) (s : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  if ∃ w, s.state.validators.data[i]? = some w ∧ w.slashed = true then newBq preset else 0

/-- The potential claim at an epoch start `m`, along a run `rm` from the start `z` of the climb.

The potential of the key keeps the fraction of the floor that the floor keeps since `z`.

The potential counts the debits of the key and its slashing charge along `rm`. -/
private def EpochClaim (x z : ForkedBeaconState preset) (high i : ℕ) {m : ForkedBeaconState preset}
    (rm : Run config checks z m) : Prop :=
  ∃ events, rm.balanceEvents high = .ok events ∧
    2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      2 * (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
          keyDebits i events + slashedCharge preset m i) *
        stakeFloorAt config x high ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat)

/-- Every cap is at least `MAX_EFFECTIVE_BALANCE`. -/
private theorem minimum_cap (caps : CapOrder preset) {h : Fork} (v : Validator) :
    preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split
  · split
    · exact UInt64.le_trans caps.activation caps.compounding
    · exact caps.activation
  · exact UInt64.le_refl _

/-- The rounded-up quotient `Bq` covers its numerator. -/
private theorem ceil_div_cover (a Q : ℕ) (positive : 0 < Q) : a ≤ Q * ((a + Q - 1) / Q) := by
  have h1 := Nat.div_add_mod (a + Q - 1) Q
  have h2 := Nat.mod_lt (a + Q - 1) positive
  omega

/-- The floor of a new key over one epoch that a slot step ends.

The potential of a key is the least of its balance and `MAX_EFFECTIVE_BALANCE`, plus the band.

The potential at the start keeps the fraction of the floor, less the rounding error.

It is charged the key's sync debits, its partial payments, and its slashing, once. -/
private theorem Ctx.cross {g x m n z : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    (pre : Run config checks m z) (ok : advanceSlotAcross config checks z = .ok n)
    (early : n.fork < .glamsterdam)
    (within : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (same : getCurrentEpoch z.state = getCurrentEpoch m.state)
    (step : (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    {events : List (BalanceEvent preset)}
    (replayed : (pre.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat =
      .ok events) :
    (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
        (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) +
        ((events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
          (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
            then (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
              (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
                1) /
              (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
            else 0)) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := by
  classical
  have mz := fork_le_of_chainSteps pre.chainSteps
  have hxm := fork_le_of_chainSteps hm.chainSteps
  have zn : z.fork ≤ n.fork := (Step.slot ok).chainStep.fork_le
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt (Nat.le_trans mz zn) early
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans c.fulu hxm
  have shared' := c.shared.append hm
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hm.chainSteps)
  have capLe : preset.MAX_EFFECTIVE_BALANCE.toNat ≤
      (withdrawalMaxEffectiveBalance preset m.fork val).toNat :=
    UInt64.le_iff_toNat_le.mp (minimum_cap c.caps val)
  have positiveQ :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    have := c.quotientTwo
    omega
  obtain ⟨z', pre', post', hr, hz', ineq⟩ := c.epochFloor shared' c.genesis c.caps c.delay
    c.vector positiveQ (pre.snoc (Step.slot ok)) fuluM early
    (Or.inr ⟨z, pre, ok, rfl, same, step⟩) i val found activated exit slashedCond
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat le_rfl replayed
  have zForkLe : z'.fork ≤ n.fork := fork_le_of_chainSteps post'.chainSteps
  have z'Early : z'.fork < .glamsterdam := Nat.lt_of_le_of_lt zForkLe early
  have z'x : Run config checks x z' := hm.append pre'
  have z'epoch : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch m.state).toNat :=
    congrArg UInt64.toNat hz'
  have nz' := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post'.chainSteps)
  have insideM : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have effEq : effectiveAt z' i = effectiveAt m i :=
    run_same_epoch_effective pre' z'Early hz' i insideM
  have altairX : .altair ≤ x.fork := Nat.le_trans (by decide) c.fulu
  have altairZ : .altair ≤ z'.fork :=
    Nat.le_trans altairX (Nat.le_trans hxm (fork_le_of_chainSteps pre'.chainSteps))
  have pass : (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then passRate config z' i else 0) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      effectiveAt m i * (stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) -
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) + 1) := by
    by_cases h : ∃ total, getTotalActiveBalance z'.state = .ok total
    · obtain ⟨total, totalOk⟩ := h
      have lt : getCurrentEpoch m.state < getCurrentEpoch n.state :=
        UInt64.lt_iff_toNat_lt.mpr (by omega)
      rw [ite_eq_left ⟨lt, total, totalOk⟩]
      have bounds := c.total_bounds z'x z'Early (by omega) totalOk
      have ixeq : ix x z' = (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat := by
        simp only [ix]
        omega
      rw [ixeq] at bounds
      have positive : 0 < stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) :=
        c.guard.2.2.2.2.2.2.2.2.2.2.2.1 _ (by unfold driftHorizon; omega)
      have divisor : 0 < inactivityPenaltyDivisor preset config := c.guard.2.2.2.2.2.2.1
      have scored : (if altair : .altair ≤ z'.fork then
          (((z'.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
            config.INACTIVITY_SCORE_BIAS.toNat ≤ startInactivityScore config x +
          config.INACTIVITY_SCORE_BIAS.toNat * ((getCurrentEpoch m.state).toNat -
            (getCurrentEpoch x.state).toNat + 1) := by
        rw [dite_eq_left altairZ]
        have grow : config.INACTIVITY_SCORE_BIAS.toNat ≤ config.INACTIVITY_SCORE_BIAS.toNat *
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        cases found' : (z'.state.inactivityScores altairZ).data[i]? with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          omega
        | some score =>
          have := c.scores z'x altairX z'Early (Or.inl c.electra) altairZ found'
          simp only [Option.map_some, Option.getD_some]
          have e : (getCurrentEpoch z'.state).toNat - (getCurrentEpoch x.state).toNat =
              (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat := by omega
          rw [e] at this
          rw [Nat.mul_add, Nat.mul_one]
          omega
      have := passRate_mul_le (config := config) (x := x) (z := z') high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) i total totalOk
        bounds.1 (by omega) positive divisor c.factor scored
      rw [effEq] at this
      exact this
    · rw [ite_eq_right (fun h' => h h'.2)]
      simp
  rw [mspq_eq m.fork fuluM mEarly] at ineq
  set K := preset.MAX_EFFECTIVE_BALANCE.toNat with hK
  set Q := (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    with hQ
  set band := preset.downwardBand with hband
  set t := (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat with ht
  set Bq := (K + band + Q - 1) / Q with hBq
  have hB : K + band ≤ Q * Bq := ceil_div_cover _ _ positiveQ
  have hanti : stakeFloorAt config x high (t + 1) ≤ stakeFloorAt config x high t :=
    c.anti (Nat.le_succ t)
  have hzero : stakeFloorAt config x high t ≤ stakeFloorAt config x high 0 :=
    c.anti (Nat.zero_le t)
  have nWithin := step
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans hxm (Nat.le_trans mz zn)) early
  have ratio := c.ratio xEarly (s := t + 1) (by omega) cxIn
  have roomT := c.room
  have hφ : 6 * Q ≤ stakeFloorAt config x high (t + 1) := by
    have := c.big
    omega
  have hband' : 2 * stakeFloorAt config x high t ≤ 3 * stakeFloorAt config x high (t + 1) := by
    omega
  have capEB : effectiveAt m i ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat := by
    have := Run.effectiveBalance_capped shared' c.genesis c.caps.activation c.caps.compounding
      mEarly val (Array.mem_of_getElem? found)
    have e : effectiveAt m i = val.effectiveBalance.toNat := by simp [effectiveAt, found]
    rw [e]
    exact UInt64.le_iff_toNat_le.mp this
  have bound := step_arith_slash (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then passRate config z' i else 0)
    ((events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (stakeFloorAt config x high t) (stakeFloorAt config x high (t + 1))
    (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1)) (effectiveAt m i)
    capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp])
    hyst capEB pass (by omega) hφ hband'
  have charge : (if (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
        w.slashed = true then effectiveAt m i / Q else 0) = 0 then 0 else Bq) ≤
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then Bq else 0) := by
    by_cases h : val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
      w.slashed = true
    · rw [ite_eq_left h, ite_eq_left h]
      by_cases e : effectiveAt m i / Q = 0 <;> simp [e]
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  have mul := Nat.mul_le_mul_right (stakeFloorAt config x high t)
    (Nat.add_le_add_left charge ((events.map (keySyncDebit i)).sum +
      (events.map (floorPartialDebit i.toUInt64)).sum))
  linarith

/-- The floor of a new key over a run inside one epoch.

The least of its balance and `MAX_EFFECTIVE_BALANCE` at the start is at most its balance at the end.

It is charged the key's sync debits, its partial payments, and its slashing, once. -/
private theorem Ctx.inside {g x m n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m) (seg : Run config checks m n)
    (early : n.fork < .glamsterdam)
    (same : getCurrentEpoch n.state = getCurrentEpoch m.state)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    {events : List (BalanceEvent preset)}
    (replayed : seg.balanceEvents (getCurrentEpoch m.state).toNat = .ok events) :
    min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt n i +
      ((events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
              1) / (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0)) := by
  classical
  have hxm := fork_le_of_chainSteps hm.chainSteps
  have mn := fork_le_of_chainSteps seg.chainSteps
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt mn early
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans c.fulu hxm
  have shared' := c.shared.append hm
  have capLe : preset.MAX_EFFECTIVE_BALANCE.toNat ≤
      (withdrawalMaxEffectiveBalance preset m.fork val).toNat :=
    UInt64.le_iff_toNat_le.mp (minimum_cap c.caps val)
  have positiveQ :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    have := c.quotientTwo
    omega
  obtain ⟨z', pre', post', hr, hz', ineq⟩ := c.epochFloor shared' c.genesis c.caps c.delay
    c.vector positiveQ seg fuluM early (Or.inl same) i val found activated exit slashedCond
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat le_rfl replayed
  rw [mspq_eq m.fork fuluM mEarly] at ineq
  have noPass : ¬ (getCurrentEpoch m.state < getCurrentEpoch n.state ∧
      ∃ total, getTotalActiveBalance z'.state = .ok total) := by
    intro h
    rw [same] at h
    exact UInt64.lt_irrefl _ h.1
  rw [ite_eq_right noPass] at ineq
  set K := preset.MAX_EFFECTIVE_BALANCE.toNat with hK
  set Q := (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    with hQ
  set band := preset.downwardBand with hband
  set Bq := (K + band + Q - 1) / Q with hBq
  have hB : K + band ≤ Q * Bq := ceil_div_cover _ _ positiveQ
  have capEB : effectiveAt m i ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat := by
    have := Run.effectiveBalance_capped shared' c.genesis c.caps.activation c.caps.compounding
      mEarly val (Array.mem_of_getElem? found)
    have e : effectiveAt m i = val.effectiveBalance.toNat := by simp [effectiveAt, found]
    rw [e]
    exact UInt64.le_iff_toNat_le.mp this
  have bound := same_arith (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    ((events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (effectiveAt m i) capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp]) hyst capEB
  have charge : (if (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
        w.slashed = true then effectiveAt m i / Q else 0) = 0 then 0 else Bq) ≤
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then Bq else 0) := by
    by_cases h : val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
      w.slashed = true
    · rw [ite_eq_left h, ite_eq_left h]
      by_cases e : effectiveAt m i / Q = 0 <;> simp [e]
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  omega

/-- A run from an epoch to a later one has a slot step that leaves a given epoch between them. -/
private theorem Run.cross_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (k : ℕ) (low : (getCurrentEpoch x.state).toNat ≤ k) (high : k < (getCurrentEpoch y.state).toNat) :
    ∃ (z n : ForkedBeaconState preset) (pre : Run config checks x z)
      (ok : advanceSlotAcross config checks z = .ok n) (rest : Run config checks n y),
      tail = (pre.snoc (Step.slot ok)).append rest ∧ (getCurrentEpoch z.state).toNat = k ∧
        (getCurrentEpoch n.state).toNat = k + 1 := by
  induction tail with
  | nil => omega
  | @snoc middle last pre step ih =>
    by_cases inside : k < (getCurrentEpoch middle.state).toNat
    · obtain ⟨z, n, a, ok, rest, split, hz, hn⟩ := ih inside
      refine ⟨z, n, a, ok, rest.snoc step, ?_, hz, hn⟩
      rw [split]
      rfl
    · have bound := ChainStep.epoch_le_succ step.chainStep
      cases step with
      | slot ok => exact ⟨middle, last, pre, ok, .nil, rfl, by omega, by omega⟩
      | @block fork before after engine signed due ok =>
        have same := processBlock_slot (applySignedBlock_ok ok).2.1
        have e : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
          simp only [getCurrentEpoch, same]
        simp only at high inside
        omega

/-- Right after an epoch transition, the effective balance of a key is within the band above its
balance. -/
private theorem Ctx.hyst_start {g x m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    (hyst : Hysteresis m.state) {i : ℕ} {val : Validator}
    (found : m.state.validators.data[i]? = some val) :
    effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand := by
  have matched := (run_justified_separated (c.shared.append hm) c.genesis).1.balancesMatch
  have lt : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have lt' : i < m.state.balances.data.size := by
    unfold BalancesMatch at matched
    omega
  have bal : m.state.balances.data[i]? = some m.state.balances.data[i] :=
    Array.getElem?_eq_getElem lt'
  have := hyst.down i val _ found bal
  simp only [effectiveAt, actualBalanceAt, found, bal, Option.map_some, Option.getD_some]
  exact this

/-- The arithmetic of the last step of the floor of a new key.

The potential keeps `2/3` of its start, less the rounding, and the rounding is below the room.

The preset fact `margin` then leaves the floor of the pin. -/
private theorem final_arith (K band Bq B S C φ0 φk J J' T : ℕ)
    (h1 : 2 * (K + band) * φk ≤ 2 * (B + band + C) * φ0 + 3 * (K + band) * J)
    (h2 : 2 * φ0 ≤ 3 * φk) (hJ : J ≤ J') (room : 400 * J' ≤ φ0) (pos : 0 < φ0)
    (hC : C ≤ S + Bq)
    (margin : 2400 * T + 2400 * band + 2400 * Bq ≤ 1591 * (K + band)) : T ≤ B + S := by
  have a1 : 6 * (K + band) * φk ≤ 6 * (B + band + C) * φ0 + 9 * (K + band) * J := by nlinarith
  have a2 : 4 * (K + band) * φ0 ≤ 6 * (K + band) * φk := by nlinarith
  have a3 : 9 * (K + band) * J * 400 ≤ 9 * (K + band) * φ0 := by
    have : J * 400 ≤ φ0 := by omega
    nlinarith
  have a4 : 1600 * (K + band) * φ0 ≤ 2400 * (B + band + C) * φ0 + 9 * (K + band) * φ0 := by
    nlinarith
  have a5 : 1600 * (K + band) ≤ 2400 * (B + band + C) + 9 * (K + band) := by
    have := Nat.le_of_mul_le_mul_right (a := 1600 * (K + band))
      (b := 2400 * (B + band + C) + 9 * (K + band)) (c := φ0) (by nlinarith) pos
    exact this
  omega

/-- A key slashed on the climb is not due its delayed penalty within the window.

It was unslashed at the start `z` of the climb, so its withdrawal waits a whole slashings vector. -/
private theorem Ctx.slashed_window {g x z m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z) (rm : Run config checks z m)
    (mEarly : m.fork < .glamsterdam) (i : ℕ) (v0 val : Validator)
    (found0 : z.state.validators.data[i]? = some v0) (found : m.state.validators.data[i]? = some val)
    (unslashed0 : v0.slashed = false) (epoch : ℕ) (inside : epoch ≤ high + 1) :
    val.slashed = true →
      epoch + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat := by
  intro flag
  have lower := rm.newly_slashed_withdrawableEpoch c.caps.activation c.caps.compounding
    mEarly c.delay i v0 val found0 found unslashed0 flag
  have window := c.guard.2.2.2.2.2.2.2.2.2.2.1
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  unfold driftHorizon at window
  omega

/-- The slashing charge of a run adds the charge of its slashing. -/
private theorem slashedCharge_run {m n : ForkedBeaconState preset} (seg : Run config checks m n)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val) :
    slashedCharge preset n i = slashedCharge preset m i +
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then newBq preset else 0) := by
  classical
  unfold slashedCharge
  by_cases flag : val.slashed = true
  · obtain ⟨w', wFound', wFlag⟩ := seg.slashedPersistence i val found flag
    have : ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true := ⟨w', wFound', wFlag⟩
    have fm : ∃ w, m.state.validators.data[i]? = some w ∧ w.slashed = true := ⟨val, found, flag⟩
    simp [this, fm, flag]
  · have flag' : val.slashed = false := by simpa using flag
    have fm : ¬ ∃ w, m.state.validators.data[i]? = some w ∧ w.slashed = true := by
      rintro ⟨w', h, hf⟩
      rw [found] at h
      cases h
      exact flag hf
    simp [fm, flag']

/-- The potential claim passes the slot step that ends an epoch.

The step is the cross of one epoch, so the claim holds for the next epoch start, one epoch on. -/
private theorem Ctx.advance {g x z m p n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z) (rm : Run config checks z m)
    (ins : Run config checks m p) (ok : advanceSlotAcross config checks p = .ok n)
    (early : n.fork < .glamsterdam) (within : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (same : getCurrentEpoch p.state = getCurrentEpoch m.state)
    (step : (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    (claim : EpochClaim (config := config) (checks := checks) x z high i rm) :
    EpochClaim (config := config) (checks := checks) x z high i
      (rm.append (ins.snoc (Step.slot ok))) := by
  classical
  obtain ⟨events, replay, ih⟩ := claim
  have mp := fork_le_of_chainSteps ins.chainSteps
  have pn : p.fork ≤ n.fork := (Step.slot ok).chainStep.fork_le
  have hm : Run config checks x m := hz.append rm
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt (Nat.le_trans mp pn) early
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hm.chainSteps)
  have zm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rm.chainSteps)
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  -- the events of the segment
  obtain ⟨eseg, hseg⟩ := (ins.snoc (Step.slot ok)).balanceEvents_ok early high
  have local_ : (ins.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat = .ok eseg := by
    rw [← balanceEvents_eq_of_endpoint_le (ins.snoc (Step.slot ok)) within (by omega)]
    exact hseg
  have whole := balanceEvents_append rm (ins.snoc (Step.slot ok)) high replay hseg
  have crossed := Ctx.cross c hm ins ok early within same step i val found activated exit
    slashedCond hyst local_
  have charge := slashedCharge_run (ins.snoc (Step.slot ok)) i val found
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hm.chainSteps) (Nat.le_trans mp pn))
      early
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have pos : 0 < stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    c.guard.2.2.2.2.2.2.2.2.2.2.2.1 _ (by unfold driftHorizon; omega)
  have hanti : stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    c.anti (Nat.le_succ _)
  have hzero : stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
        stakeFloorAt config x high 0 := c.anti (Nat.zero_le _)
  have ratio := c.ratio xEarly (s := (getCurrentEpoch m.state).toNat -
    (getCurrentEpoch x.state).toNat) (by omega) cxIn
  have band : 2 * stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := by omega
  have e1 : (getCurrentEpoch n.state).toNat - (getCurrentEpoch x.state).toNat =
      (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1 := by omega
  refine ⟨events ++ eseg, whole, ?_⟩
  rw [e1, charge, keyDebits_append]
  have crossed' : (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat +
        preset.downwardBand) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
        (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) +
        (keyDebits i eseg + (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
            w.slashed = true then newBq preset else 0)) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := crossed
  have mono : (keyDebits i events + slashedCharge preset m i) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (keyDebits i events + slashedCharge preset m i) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    Nat.mul_le_mul_left _ hanti
  have stepIneq := chain_step (stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1))
    (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
    (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      keyDebits i events + slashedCharge preset m i)
    (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      (keyDebits i events + keyDebits i eseg) +
      (slashedCharge preset m i + (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? =
        some w ∧ w.slashed = true then newBq preset else 0)))
    (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
    ((getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat) pos hanti band ih
    (by nlinarith [crossed', mono])
  have e2 : (getCurrentEpoch n.state).toNat - (getCurrentEpoch z.state).toNat =
      (getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat + 1 := by omega
  rw [e2]
  exact stepIneq

/-- The potential claim carries over the slot step that ends the epoch of a climb state.

The new epoch start also lies within the band of hysteresis, since the step ran the transition. -/
private theorem Ctx.inv_step {g x z y q p' m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (ok : advanceSlotAcross config checks q = .ok p') (rest : Run config checks p' y)
    (rm : Run config checks z m) (ins : Run config checks m q)
    (cm : getCurrentEpoch m.state = getCurrentEpoch q.state)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    (claim : EpochClaim (config := config) (checks := checks) x z high i rm)
    (stepQ : (getCurrentEpoch p'.state).toNat = (getCurrentEpoch q.state).toNat + 1) :
    EpochClaim (config := config) (checks := checks) x z high i
      (rm.append (ins.snoc (Step.slot ok))) ∧
    effectiveAt p' i ≤ actualBalanceAt p' i + preset.downwardBand := by
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  have pEarly : p'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have cmN : (getCurrentEpoch m.state).toNat = (getCurrentEpoch q.state).toNat :=
    congrArg UInt64.toNat cm
  obtain ⟨val, found, life⟩ := rm.registryLifecycle.validators i v0 found0
  have activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [life.activationEpoch activated0]
    exact activated0
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps ins.chainSteps)
      (Step.slot ok).chainStep.fork_le) pEarly
  have slashedCond := c.slashed_window hz rm mEarly i v0 val found0 found unslashed0
    (getCurrentEpoch p'.state).toNat (by omega)
  have sameQ : getCurrentEpoch q.state = getCurrentEpoch m.state := cm.symm
  have stepP : (getCurrentEpoch p'.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
    omega
  have exit' : ∀ w, p'.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat := fun w hw => by
    have := exitLate p' rest w hw
    omega
  have claim' := Ctx.advance c hz rm ins ok pEarly (by omega) sameQ stepP i val found
    activated exit' slashedCond hyst claim
  obtain ⟨val', found', -⟩ := (rm.append (ins.snoc (Step.slot ok))).registryLifecycle.validators
    i v0 found0
  have lt : getCurrentEpoch q.state < getCurrentEpoch p'.state :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  exact ⟨claim', Ctx.hyst_start c (hz.append (rm.append (ins.snoc (Step.slot ok))))
    (c.hysteresis (Step.slot ok) lt) found'⟩

/-- The potential claim holds at the start of the epoch of every state of the climb.

The climb runs from `z`, where the key holds the maximum effective balance and is unslashed.

The key never exits before the end `y` of the climb.

The state `p` reaches `y`, so it ends no later than `y`. -/
private theorem Ctx.inv {g x z y : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    {p : ForkedBeaconState preset} (rp : Run config checks z p) :
    ∀ (_rest : Run config checks p y), ∃ (m : ForkedBeaconState preset)
      (rm : Run config checks z m) (ins : Run config checks m p),
      rp = rm.append ins ∧ getCurrentEpoch m.state = getCurrentEpoch p.state ∧
      effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand ∧
      EpochClaim (config := config) (checks := checks) x z high i rm := by
  induction rp with
  | nil =>
    intro _
    refine ⟨z, .nil, .nil, rfl, rfl, hystZ, [], rfl, ?_⟩
    have unflagged : ¬ ∃ w, z.state.validators.data[i]? = some w ∧ w.slashed = true := by
      rintro ⟨w, h, hf⟩
      rw [found0] at h
      cases h
      rw [unslashed0] at hf
      cases hf
    have charge : slashedCharge preset z i = 0 := by simp [slashedCharge, unflagged]
    rw [charge, min_eq_right bal0]
    simp [keyDebits]
  | @snoc q p' pre step ih =>
    intro rest
    obtain ⟨m, rm, ins, eq, cm, hyst, claim⟩ := ih ((Run.nil.snoc step).append rest)
    by_cases same : getCurrentEpoch p'.state = getCurrentEpoch q.state
    · refine ⟨m, rm, ins.snoc step, ?_, cm.trans same.symm, hyst, claim⟩
      rw [eq]
      rfl
    · have bound := ChainStep.epoch_le_succ step.chainStep
      have order := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
      have differ : (getCurrentEpoch p'.state).toNat ≠ (getCurrentEpoch q.state).toNat :=
        fun h => same (UInt64.toNat_inj.mp h)
      cases step with
      | @block fork before after engine signed due ok =>
        exfalso
        apply same
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      | slot ok =>
        obtain ⟨claim', hystP⟩ := Ctx.inv_step c hz early within i v0 found0 unslashed0 activated0
          exitLate ok rest rm ins cm hyst claim (by omega)
        refine ⟨p', rm.append (ins.snoc (Step.slot ok)), .nil, ?_, rfl, hystP, claim'⟩
        rw [eq]
        rfl

/-- The arithmetic of the climb: the potential claim gives the floor of the pin.

The claim starts at the epoch `cz` and ends at the epoch `ck`, within the window. -/
private theorem Ctx.arith {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (xEarly : x.fork < .glamsterdam) (cz ck : ℕ)
    (xz : (getCurrentEpoch x.state).toNat ≤ cz) (zk : cz ≤ ck) (inside : ck ≤ high + 1)
    (B kd sc : ℕ) (hsc : sc ≤ newBq preset)
    (claim : 2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat) ≤
      2 * (B + preset.downwardBand + (kd + sc)) *
        stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) * (ck - cz)) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ B + kd := by
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have ratio0 := c.ratio xEarly (s := cz - (getCurrentEpoch x.state).toNat) (by omega) cxIn
  have ratioK := c.ratio xEarly (s := ck - (getCurrentEpoch x.state).toNat) (by omega) cxIn
  have hzero : stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high 0 := c.anti (Nat.zero_le _)
  have roomT := c.room
  have unitJ : 1 ≤ high + 2 - (getCurrentEpoch x.state).toNat := by omega
  have phi : 2 * stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat) := by omega
  exact final_arith preset.MAX_EFFECTIVE_BALANCE.toNat preset.downwardBand (newBq preset) B kd
    (kd + sc) (stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat)) (ck - cz)
    (high + 2 - (getCurrentEpoch x.state).toNat) _ claim phi (by omega) (by omega) (by omega)
    (by omega) c.margin

/-- The least of a key's balance and the maximum, plus the debits, stays above the floor of the pin.

The state `p` lies on the climb, before its end `y`, so the key cannot yet have exited.

The least stake of the key is `2/3` of the maximum less the slashing quotient and the band. -/
private theorem Ctx.claimAt {g x z y p : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (rp : Run config checks z p) (rest : Run config checks p y)
    (lt : (getCurrentEpoch p.state).toNat < (getCurrentEpoch y.state).toNat) :
    ∃ events, rp.balanceEvents high = .ok events ∧
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i events := by
  classical
  obtain ⟨m, rm, ins, eq, cm, hyst, events, replay, ih⟩ :=
    c.inv hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate rp rest
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps ins.chainSteps) pEarly
  have hm : Run config checks x m := hz.append rm
  obtain ⟨val, found, life⟩ := rm.registryLifecycle.validators i v0 found0
  have activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [life.activationEpoch activated0]
    exact activated0
  have cmN : (getCurrentEpoch m.state).toNat = (getCurrentEpoch p.state).toNat :=
    congrArg UInt64.toNat cm
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  obtain ⟨eins, hins⟩ := ins.balanceEvents_ok pEarly high
  have local_ : ins.balanceEvents (getCurrentEpoch m.state).toNat = .ok eins := by
    rw [← balanceEvents_eq_of_endpoint_le (high := high)
      (localHigh := (getCurrentEpoch m.state).toNat) ins (by omega) (by omega)]
    exact hins
  have exit' : ∀ w, p.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat := fun w hw => by
    have := exitLate p rest w hw
    omega
  have slashedCond := c.slashed_window hz rm mEarly i v0 val found0 found unslashed0
    (getCurrentEpoch p.state).toNat (by omega)
  have inside := Ctx.inside c hm ins pEarly cm.symm i val found activated exit' slashedCond hyst
    local_
  have charge := slashedCharge_run ins i val found
  have whole := balanceEvents_append rm ins high replay hins
  refine ⟨events ++ eins, by rw [eq]; exact whole, ?_⟩
  -- the arithmetic of the climb
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  have zm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rm.chainSteps)
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps)
      (Nat.le_trans (fork_le_of_chainSteps rm.chainSteps) (fork_le_of_chainSteps ins.chainSteps)))
      pEarly
  have e2 : min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt p i +
      (keyDebits i eins + (if val.slashed = false ∧ ∃ w, p.state.validators.data[i]? = some w ∧
        w.slashed = true then newBq preset else 0)) := by
    have := inside
    unfold keyDebits
    unfold newBq
    simpa using this
  have step : min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat +
      preset.downwardBand + keyDebits i events + slashedCharge preset m i ≤
      actualBalanceAt p i + preset.downwardBand + keyDebits i (events ++ eins) +
        slashedCharge preset p i := by
    rw [keyDebits_append, charge]
    omega
  have chargeLe : slashedCharge preset p i ≤ newBq preset := by
    unfold slashedCharge
    split <;> omega
  have h1 : 2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
      stakeFloorAt config x high
        ((getCurrentEpoch p.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      2 * (actualBalanceAt p i + preset.downwardBand +
        (keyDebits i (events ++ eins) + slashedCharge preset p i)) *
        stakeFloorAt config x high
          ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        ((getCurrentEpoch p.state).toNat - (getCurrentEpoch z.state).toNat) := by
    rw [← cmN]
    refine ih.trans ?_
    have := Nat.mul_le_mul_right (stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat))
      (Nat.mul_le_mul_left 2 step)
    have e : actualBalanceAt p i + preset.downwardBand + keyDebits i (events ++ eins) +
        slashedCharge preset p i = actualBalanceAt p i + preset.downwardBand +
          (keyDebits i (events ++ eins) + slashedCharge preset p i) := by omega
    rw [e] at this
    omega
  exact c.arith xEarly (getCurrentEpoch z.state).toNat (getCurrentEpoch p.state).toNat xz
    (by omega) (by omega) _ _ _ chargeLe h1

/-- A state on the balance path of a run is a state of the run, or the state inside a slot step.

The state inside a slot step comes after the slot and its epoch transition, before the upgrades. -/
private theorem Run.mem_balancePath_split {z w : ForkedBeaconState preset}
    (r : Run config checks z w) {p : ForkedBeaconState preset} (member : p ∈ r.balancePath) :
    (∃ (rp : Run config checks z p) (rest : Run config checks p w), r = rp.append rest) ∨
    (∃ (q n : ForkedBeaconState preset) (rq : Run config checks z q)
      (ok : advanceSlotAcross config checks q = .ok n) (rest : Run config checks n w)
      (adv : BeaconState preset q.fork), r = (rq.snoc (Step.slot ok)).append rest ∧
        advanceSlot config checks q.state = .ok adv ∧ p = ⟨q.fork, adv⟩ ∧
        processUpgrades config checks ⟨q.fork, adv⟩ = .ok n) := by
  induction r with
  | nil =>
    simp only [Run.balancePath, List.mem_singleton] at member
    subst member
    exact .inl ⟨.nil, .nil, rfl⟩
  | @snoc q last pre step ih =>
    simp only [Run.balancePath, List.mem_append] at member
    rcases member with member | member
    · rcases ih member with ⟨rp, rest, eq⟩ | ⟨q', n, rq, ok, rest, adv, eq, adv_ok, hp, up⟩
      · exact .inl ⟨rp, rest.snoc step, by rw [eq]; rfl⟩
      · exact .inr ⟨q', n, rq, ok, rest.snoc step, adv, by rw [eq]; rfl, adv_ok, hp, up⟩
    · cases step with
      | block engine signed due ok =>
        simp only [Step.balancePath, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .inl ⟨pre, (Run.nil.snoc (.block engine signed due ok)), rfl⟩
        · exact .inl ⟨pre.snoc (.block engine signed due ok), .nil, rfl⟩
      | slot ok =>
        have unfold_ok := ok
        obtain ⟨adv, advOk, upgrades⟩ := bind_ok_iff.mp unfold_ok
        simp only [Step.balancePath, advOk, Except.toOption, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl | rfl
        · exact .inl ⟨pre, (Run.nil.snoc (.slot ok)), rfl⟩
        · exact .inr ⟨_, last, pre, ok, .nil, adv, rfl, advOk, rfl, upgrades⟩
        · exact .inl ⟨pre.snoc (.slot ok), .nil, rfl⟩

private theorem keyDebits_le_of_prefix (i : ℕ) {a b : List (BalanceEvent preset)} (h : a <+: b) :
    keyDebits i a ≤ keyDebits i b := by
  obtain ⟨t, rfl⟩ := h
  rw [keyDebits_append]
  omega

/-- A state of the climb that precedes its end has the floor of the pin, up to the debits of the
run that contains it. -/
private theorem Ctx.floorRun {g x z y p w : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (rp : Run config checks z p) (rest : Run config checks p w) (restY : Run config checks p y)
    (lt : (getCurrentEpoch p.state).toNat < (getCurrentEpoch y.state).toNat)
    {Ef : List (BalanceEvent preset)} (hEf : (rp.append rest).balanceEvents high = .ok Ef) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
  obtain ⟨events, replay, bound⟩ := c.claimAt hz early within i v0 found0 unslashed0 activated0
    bal0 hystZ exitLate rp restY lt
  obtain ⟨before, beforeOk, prefix_⟩ := Run.balanceEvents_prefix rp rest high Ef hEf
  rw [replay] at beforeOk
  cases beforeOk
  have := keyDebits_le_of_prefix i prefix_
  omega

/-- The end of the climb, the first state of the last epoch, has the floor of the pin too. -/
private theorem Ctx.claimEnd {g x z y zz n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (pre0 : Run config checks z zz) (ok : advanceSlotAcross config checks zz = .ok n)
    (rest0 : Run config checks n y)
    (stepN : (getCurrentEpoch n.state).toNat = (getCurrentEpoch zz.state).toNat + 1)
    {Ef : List (BalanceEvent preset)}
    (hEf : (pre0.snoc (Step.slot ok)).balanceEvents high = .ok Ef) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt n i + keyDebits i Ef := by
  obtain ⟨m, rm, ins, eq, cm, hyst, claim⟩ := c.inv hz early within i v0 found0 unslashed0
    activated0 bal0 hystZ exitLate pre0 ((Run.nil.snoc (Step.slot ok)).append rest0)
  obtain ⟨claim', -⟩ := Ctx.inv_step c hz early within i v0 found0 unslashed0 activated0
    exitLate ok rest0 rm ins cm hyst claim stepN
  obtain ⟨events, replay, ineq⟩ := claim'
  have same : pre0.snoc (Step.slot ok) = rm.append (ins.snoc (Step.slot ok)) := by
    rw [eq]
    rfl
  rw [same, replay] at hEf
  cases hEf
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  have zk := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
    (pre0.snoc (Step.slot ok)).chainSteps)
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps)
      (fork_le_of_chainSteps (pre0.snoc (Step.slot ok)).chainSteps)) nEarly
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have chargeLe : slashedCharge preset n i ≤ newBq preset := by
    unfold slashedCharge
    split <;> omega
  have := c.arith xEarly (getCurrentEpoch z.state).toNat (getCurrentEpoch n.state).toNat xz zk
    (by omega) (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat) (keyDebits i Ef) _
    chargeLe
    (by
      have e : min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
          (keyDebits i Ef + slashedCharge preset n i) =
          min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            keyDebits i Ef + slashedCharge preset n i := by omega
      rw [e]
      exact ineq)
  have := Nat.min_le_left (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat
  omega

/-- The state inside a slot step has the registry and the balances of the state after its upgrades.

The upgrades after Electra and before Gloas keep both. -/
private theorem mid_data {s n : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : n.fork < .glamsterdam)
    (upgrades : processUpgrades config checks s = .ok n) :
    n.state.validators.data = s.state.validators.data ∧
      n.state.balances.data = s.state.balances.data := by
  have target : .pectra ≤ n.fork := Nat.le_trans electra (processUpgrades_fork_le upgrades)
  obtain ⟨validators, balances, -⟩ := processUpgrades_retained_data electra early upgrades target
  exact ⟨validators, balances⟩

/-- Every state on the balance path of the climb has the key, and the floor of the pin. -/
private theorem Ctx.floors {g x z y zz n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (pre0 : Run config checks z zz) (ok : advanceSlotAcross config checks zz = .ok n)
    (rest0 : Run config checks n y)
    (stepN : (getCurrentEpoch n.state).toNat = (getCurrentEpoch zz.state).toNat + 1)
    {Ef : List (BalanceEvent preset)}
    (hEf : (pre0.snoc (Step.slot ok)).balanceEvents high = .ok Ef) :
    ∀ p ∈ (pre0.snoc (Step.slot ok)).balancePath,
      (∃ val, p.state.validators.data[i]? = some val) ∧
        2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
          preset.MAX_EFFECTIVE_BALANCE.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
          preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
  have nY := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  -- a state of the run before the last step
  have runState : ∀ (p : ForkedBeaconState preset) (rp : Run config checks z p)
      (rest : Run config checks p zz), pre0 = rp.append rest →
      (∃ val, p.state.validators.data[i]? = some val) ∧
        2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
          preset.MAX_EFFECTIVE_BALANCE.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
          preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
    intro p rp rest eq
    have pz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
    obtain ⟨val, found, -⟩ := rp.registryLifecycle.validators i v0 found0
    refine ⟨⟨val, found⟩, ?_⟩
    refine c.floorRun hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate rp
      (rest.snoc (Step.slot ok)) ((rest.snoc (Step.slot ok)).append rest0) (by omega) ?_
    rw [eq] at hEf
    exact hEf
  intro p member
  simp only [Run.balancePath, List.mem_append] at member
  rcases member with member | member
  · rcases Run.mem_balancePath_split pre0 member with ⟨rp, rest, eq⟩ |
      ⟨q, n', rq, ok', rest, adv, eq, advOk, hp, upgrades⟩
    · exact runState p rp rest eq
    · have step := runState n' (rq.snoc (Step.slot ok')) rest eq
      have qFork : x.fork ≤ q.fork :=
        Nat.le_trans (fork_le_of_chainSteps hz.chainSteps) (fork_le_of_chainSteps rq.chainSteps)
      have n'Early : n'.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps)
          (Nat.lt_of_le_of_lt (fork_le_of_chainSteps (Run.nil.snoc (Step.slot ok)).chainSteps)
            nEarly)
      have data := mid_data (config := config) (checks := checks) (s := ⟨q.fork, adv⟩)
        (Nat.le_trans c.electra qFork) n'Early upgrades
      subst hp
      obtain ⟨⟨val, found⟩, bound⟩ := step
      refine ⟨⟨val, ?_⟩, ?_⟩
      · simpa [data.1] using found
      · have : actualBalanceAt ⟨q.fork, adv⟩ i = actualBalanceAt n' i := by
          simp only [actualBalanceAt, data.2]
        rw [this]
        exact bound
  · obtain ⟨adv, advOk, upgrades⟩ := bind_ok_iff.mp ok
    simp only [Step.balancePath, advOk, Except.toOption, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact runState _ pre0 .nil rfl
    · have zzFork : .pectra ≤ zz.fork := Nat.le_trans c.electra
        (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps) (fork_le_of_chainSteps pre0.chainSteps))
      have data := mid_data (config := config) (checks := checks) (s := ⟨zz.fork, adv⟩) zzFork
        nEarly upgrades
      obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      refine ⟨⟨val, ?_⟩, ?_⟩
      · simpa [data.1] using found
      · have := c.claimEnd hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate
          pre0 ok rest0 stepN hEf
        have e : actualBalanceAt ⟨zz.fork, adv⟩ i = actualBalanceAt n i := by
          simp only [actualBalanceAt, data.2]
        rw [e]
        exact this
    · obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      exact ⟨⟨val, found⟩, c.claimEnd hz early within i v0 found0 unslashed0 activated0 bal0 hystZ
        exitLate pre0 ok rest0 stepN hEf⟩

end Epoch

/-! ## C3: the effective balance of a new key -/

/-- The preset facts that the floor of a new key reads.

The slashings vector has at least four epochs, and the base reward factor is positive.

The slashing quotient is at least two.

The margin leaves room for the rounding of the climb after the loss of a third of the stake.

The margin reads the maximum effective balance, the band, and the slashing quotient. -/
def NewKeyPresetFacts (preset : Preset) : Prop :=
  4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ∧ 1 ≤ preset.BASE_REWARD_FACTOR.toNat ∧
  2 ≤ (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
  2400 * (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
      preset.MAX_EFFECTIVE_BALANCE.toNat /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - 1) + 2400 * preset.downwardBand +
    2400 * ((preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat) ≤
    1591 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)

/-- The preset facts of the floor of a new key, mainnet. -/
theorem newKeyPresetFacts_mainnet : NewKeyPresetFacts Preset.mainnet := by
  unfold NewKeyPresetFacts
  decide

/-- The preset facts of the floor of a new key, minimal. -/
theorem newKeyPresetFacts_minimal : NewKeyPresetFacts Preset.minimal := by
  unfold NewKeyPresetFacts
  decide

/-- C2 (item 16).

Every key's gain rate is at most the gain rate at the largest effective balance.

The effective balance of a key is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
theorem gain_le_capMax (perIncrement eb : ℕ)
    (capped : eb ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    eb / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
          WEIGHT_DENOMINATOR.toNat :=
  Nat.div_le_div_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right capped)))

/-- C4 (preset facts, mainnet).

The slashing quotients are large enough, and the ejection balance exceeds an increment.

The ejection balance less an increment fits below two thirds of the activation balance.

That bound is less the slashing penalty, the downward band and an increment. -/
theorem preset_facts_mainnet :
    4 ≤ (parameters Preset.mainnet .fusaka).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
    2 ≤ (parameters Preset.mainnet .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat < Config.mainnet.EJECTION_BALANCE.toNat ∧
    Config.mainnet.EJECTION_BALANCE.toNat - Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * Preset.mainnet.MIN_ACTIVATION_BALANCE.toNat / 3 -
        Preset.mainnet.MIN_ACTIVATION_BALANCE.toNat /
          (parameters Preset.mainnet .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        Preset.mainnet.downwardBand - Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  decide

/-- C4 (preset facts, minimal preset).

The same four facts as for the mainnet preset. -/
theorem preset_facts_minimal :
    4 ≤ (parameters Preset.minimal .fusaka).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
    2 ≤ (parameters Preset.minimal .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat < Config.minimal.EJECTION_BALANCE.toNat ∧
    Config.minimal.EJECTION_BALANCE.toNat - Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * Preset.minimal.MIN_ACTIVATION_BALANCE.toNat / 3 -
        Preset.minimal.MIN_ACTIVATION_BALANCE.toNat /
          (parameters Preset.minimal .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        Preset.minimal.downwardBand - Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  decide

end EthLib.Consensus.Models.Network.PinSplit
