module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling

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

/-- Potentials that retain a decreasing floor, up to a rounding error per epoch.

The floor `φ` never rises, and stays within three halves of its start.

Each potential `d` keeps a fraction `φ (t + 1) / φ t` of the one before, less an error `e`.

So `d j` keeps the fraction `φ j / φ 0` of `d 0`, less `3 e j / 2` over `φ 0`. -/
private theorem retain_arith (φ d : ℕ → ℕ) (e T : ℕ) (pos : ∀ t < T, 0 < φ t)
    (anti : ∀ t < T, φ (t + 1) ≤ φ t) (band : ∀ t ≤ T, 2 * φ 0 ≤ 3 * φ t)
    (step : ∀ t < T, d t * φ (t + 1) ≤ d (t + 1) * φ t + e) :
    ∀ j ≤ T, 2 * d 0 * φ j ≤ 2 * d j * φ 0 + 3 * e * j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hlt : j < T := hj
    have ih' := ih (Nat.le_of_lt hlt)
    have p := pos j hlt
    have a := anti j hlt
    have b := band j (Nat.le_of_lt hlt)
    have s := step j hlt
    refine Nat.le_of_mul_le_mul_right ?_ p
    calc 2 * d 0 * φ (j + 1) * φ j = (2 * d 0 * φ j) * φ (j + 1) := by ring
      _ ≤ (2 * d j * φ 0 + 3 * e * j) * φ (j + 1) := Nat.mul_le_mul_right _ ih'
      _ = 2 * φ 0 * (d j * φ (j + 1)) + 3 * e * j * φ (j + 1) := by ring
      _ ≤ 2 * φ 0 * (d (j + 1) * φ j + e) + 3 * e * j * φ j := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left _ s
          · exact Nat.mul_le_mul_left _ a
      _ = 2 * d (j + 1) * φ 0 * φ j + 2 * φ 0 * e + 3 * e * j * φ j := by ring
      _ ≤ 2 * d (j + 1) * φ 0 * φ j + 3 * φ j * e + 3 * e * j * φ j := by
          have := Nat.mul_le_mul_right e b
          omega
      _ = (2 * d (j + 1) * φ 0 + 3 * e * (j + 1)) * φ j := by ring

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

open DirectSafety.Apriori.Internal in
/-- The floor of one key over a run that crosses at most one epoch boundary.

The run starts at `m` and ends at `n`, from Fulu and before Gloas.

The key must be assigned an activation at `m`, and not exit by the epoch of `n`.

If it is slashed at `m`, its delayed slashing penalty must not be due by the epoch of `n`.

Take any `C` below the key's largest effective balance at `m`.

The least of the balance at `m` and `C` is at most the balance at `n`, plus its debits.

The first debit is the pass at the last state `z` of the first epoch, if the run crosses its end.

The others are the key's sync debits and its payments from the queue of partial withdrawals.

The last is its initial slashing penalty, if the run slashes it.

That penalty is the effective balance at `m` over the slashing quotient.

The effective balance changes only at the end of an epoch, after any slashing in it. -/
def EpochFloorStatement (preset : Preset) (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {m n : ForkedBeaconState preset} (r : Run config checks m n),
    .fusaka ≤ m.fork → n.fork < .glamsterdam →
    (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch m.state).toNat + 1 →
    ∀ (i : ℕ) (val : Validator), m.state.validators.data[i]? = some val →
    val.activationEpoch ≠ FAR_FUTURE_EPOCH →
    (∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch n.state).toNat < w.exitEpoch.toNat) →
    (val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat) →
    ∀ C : ℕ, C ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat →
    ∀ {events : List (BalanceEvent preset)},
      r.balanceEvents (getCurrentEpoch m.state).toNat = .ok events →
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      min (actualBalanceAt m i) C ≤ actualBalanceAt n i +
        (if getCurrentEpoch m.state < getCurrentEpoch n.state then passRate config z i else 0) +
        (events.map (keySyncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then effectiveAt m i /
            (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0)

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
