module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Credits to keys that exit, along a run

A key that has exited and is not yet withdrawable earns no deposit credit.

Its pending deposits are postponed until it is withdrawable.

A block deposit from Electra only queues the deposit, so it leaves every balance alone.

An epoch's pending deposits leave its balance alone (`processPendingDeposits_exited_balance`).

Along a run the key keeps its exit, and its withdrawable epoch does not fall.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-! ## Deposits leave the balance of an exiting key alone -/

/-- The statement of PinDriftBound's private `processPendingDeposits_exited_balance`.

From Electra, the pending deposits of an epoch leave a key's balance alone.

This holds while the key exits and is not yet withdrawable. -/
def PendingDepositsKeepExited (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {fork : Fork} {state after : BeaconState preset fork} {electra : .pectra ≤ fork},
    processPendingDeposits config checks state electra = .ok after →
    ∀ {i : ℕ} {v : Validator}, state.validators.data[i]? = some v →
      v.exitEpoch.toNat < 2 ^ 64 - 1 →
      (getCurrentEpoch state).toNat < v.withdrawableEpoch.toNat →
      after.balances.data[i]? = state.balances.data[i]?

/-- Every exiting key of the first state keeps its balance in the second state. -/
private def KeepsExiting {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v → v.exitEpoch.toNat < 2 ^ 64 - 1 →
    (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat →
    t.balances.data[i]? = s.balances.data[i]?

/-- Every deposit event of the list leaves the balance of an exiting key alone. -/
private def Quiet (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source = .deposits → KeepsExiting e.before.state e.after.state

private theorem quiet_nil : Quiet ([] : List (BalanceEvent preset)) := fun _ mem => by
  simp at mem

private theorem quiet_carry {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (ok : carryBalance action pre = .ok post) : Quiet post.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact initial

private theorem quiet_record {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (keeps : source = .deposits → ∀ t, action pre.1 = .ok t → KeepsExiting pre.1 t)
    (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
  intro e member sourceEq
  rcases List.mem_append.mp member with old | new
  · exact initial e old sourceEq
  · obtain rfl := List.mem_singleton.mp new
    exact keeps sourceEq t actionOk

/-- From Electra, a block deposit leaves every balance of the registry alone. -/
private theorem processDeposit_keeps {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) {before : f < .hegota} {dep : Deposit}
    (ok : processDeposit config checks before s dep = .ok t) : KeepsExiting s t := by
  intro i v found _ _
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, pending, rfl | added, rfl⟩ |
      ⟨early, _⟩
  · rfl
  · rfl
  · exact (addValidatorToRegistry_kept (Nat.le_trans (by decide) electra) added inside).2.1
  · exact absurd (Nat.lt_of_lt_of_le early electra) (Nat.lt_irrefl _)

/-- From Electra, the deposit events of a block replay leave the balance of an exiting key alone. -/
private theorem blockReplay_quiet {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : Quiet post.2 := by
  have ordinary {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (initial : Quiet pre.2)
      (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 :=
    quiet_record initial (fun eq => absurd eq notDeposit) ok
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headedOk, rest⟩ := bind_ok_iff.mp ok
  have headedQuiet := quiet_carry quiet_nil headedOk
  simp only [bellatrix, ↓reduceDIte] at rest
  obtain ⟨executed, executedOk, rest⟩ := bind_ok_iff.mp rest
  have executedQuiet := ordinary (by decide : BalanceSource.withdrawals ≠ .deposits)
    headedQuiet executedOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have randaoQuiet := quiet_carry executedQuiet randaoOk
  have votedQuiet := quiet_carry randaoQuiet votedOk
  have proposedQuiet := foldlM_ok_invariant (fun p => Quiet p.2)
    (fun _ _ _ h ok => ordinary (by decide : BalanceSource.slashings ≠ .deposits) h ok)
    votedQuiet proposedOk
  have attestedQuiet := foldlM_ok_invariant (fun p => Quiet p.2)
    (fun _ _ _ h ok => ordinary (by decide : BalanceSource.slashings ≠ .deposits) h ok)
    proposedQuiet attestedOk
  have rewardedQuiet := foldlM_ok_invariant (fun p => Quiet p.2)
    (fun _ _ _ h ok => ordinary (by decide : BalanceSource.rewards ≠ .deposits) h ok)
    attestedQuiet rewardedOk
  have depositedQuiet := foldlM_ok_invariant (fun p => Quiet p.2)
    (fun _ _ _ h ok => quiet_record h
      (fun _ _ actionOk => processDeposit_keeps electra actionOk) ok)
    rewardedQuiet depositOk
  have exitedQuiet := quiet_carry depositedQuiet exitOk
  have changedQuiet := quiet_carry exitedQuiet changedOk
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
    requested, consolidations, rest⟩ := rest
  have depositsQuiet := quiet_carry changedQuiet depositRequestOk
  have withdrawalsQuiet := quiet_carry depositsQuiet withdrawalOk
  have requestedQuiet := foldlM_ok_invariant (fun p => Quiet p.2)
    (fun _ _ _ h ok => ordinary (by decide : BalanceSource.excess ≠ .deposits) h ok)
    withdrawalsQuiet consolidations
  simp only [altair, ↓reduceDIte] at rest
  exact ordinary (by decide : BalanceSource.sync ≠ .deposits) requestedQuiet rest

/-- The deposit events of an epoch replay leave the balance of an exiting key alone.

The pending deposits of an epoch are the only deposit events of the replay. -/
private theorem epochReplay_quiet (exitedBalance : PendingDepositsKeepExited (preset := preset)
      config checks)
    {f : Fork} {s : BeaconState preset f} {post : BalanceReplay preset f}
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    Quiet post.2 := by
  refine (epochBalanceReplay_trace ok).transport
    (fun a b : BalanceReplay preset f => Quiet a.2 → Quiet b.2)
    (fun _ => id) (fun one two held => two (one held)) ?_ quiet_nil
  intro k member pre after step held
  cases k <;> simp only [epochReplayAction] at step
  case justification | registry => exact quiet_carry held step
  case inactivity | eth1Reset =>
    split at step
    · exact quiet_carry held step
    · cases step; exact held
  case rewards =>
    exact replayRewards_induction (fun pre => Quiet pre.2)
      (fun prior ok => quiet_record prior (fun eq => by cases eq) ok)
      (fun penalty prior ok => quiet_record prior
        (fun eq => by rcases penalty with rfl | rfl <;> cases eq) ok) held step
  case slashings => exact quiet_record held (fun eq => by cases eq) step
  case pendingDeposits =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨deposited, depositedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        intro i v found exited withdrawable
        exact exitedBalance depositedOk found exited withdrawable
    · cases step; exact held
  case pendingConsolidations =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨consolidated, consolidatedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        cases sourceEq
    · cases step; exact held
  all_goals simp [EpochStage.prefixStages] at member

/-- The deposit events of a step leave the balance of an exiting key alone. -/
private theorem step_quiet (exitedBalance : PendingDepositsKeepExited (preset := preset)
      config checks)
    {x y : ForkedBeaconState preset} (step : Step config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    Quiet events := by
  cases step with
  | block engine signed due ok =>
    exact blockReplay_quiet electra early engine _ _ (Step.balanceEvents_block early replayed)
  | slot ok =>
    obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
      Step.balanceEvents_slot ok early replayed
    have crossed : Quiet crossings := fun e member sourceEq => by
      cases (upgradeBalanceReplay_crossing crossingOk e member).symm.trans sourceEq
    rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, rfl, -⟩
    · exact crossed
    · intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact epochReplay_quiet exitedBalance recordOk e old sourceEq
      · exact crossed e new sourceEq

/-- The deposit events of a run leave the balance of an exiting key alone. -/
private theorem run_quiet (exitedBalance : PendingDepositsKeepExited (preset := preset)
      config checks)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    Quiet events := by
  induction tail generalizing events with
  | nil => cases replayed; exact quiet_nil
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have priorQuiet := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have inFork : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact priorQuiet e old sourceEq
      · exact step_quiet exitedBalance step inFork early addedOk e new sourceEq
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      exact priorQuiet

/-! ## Group A: credits to exiting keys -/

/-- A1 (item 14, run lift).

Along C's run, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

`exitedBalance` is PinDriftBound's private `processPendingDeposits_exited_balance`.

`kept` is the run-level withdrawable-kept fact at the state before each event.

It says that an assigned exit stays (`RegistryLifecycle`).

It says that once the exit is set, the withdrawable epoch only rises (`WithdrawableKept`).

The private sources of these facts are `WithdrawalKept` in PendingConsolidations.

The other private source is `Lives` in BranchLedger.

It also says that the epoch of each event's state is at most the run's last epoch. -/
theorem Run.exiting_deposit_credit_zero {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (exitedBalance : PendingDepositsKeepExited (preset := preset) config checks)
    (kept : ∀ e ∈ events, RegistryLifecycle x.state e.before.state ∧
      WithdrawableKept x.state e.before.state ∧
      getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (keyCredit i)).sum = 0 := by
  have quiet := run_quiet exitedBalance tail electra early high replayed
  apply List.sum_eq_zero
  intro n member
  obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
  simp only [decide_eq_true_eq] at sourceEq
  obtain ⟨life, withdrawal, epoch⟩ := kept e inEvents
  obtain ⟨w, read, lifecycle⟩ := life.validators i v found
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    rw [far] at exited
    exact absurd exited (Nat.lt_irrefl _)
  have sameExit := lifecycle.exitEpoch assigned
  have later := UInt64.le_iff_toNat_le.mp (withdrawal i v w found read assigned).1
  have now := UInt64.le_iff_toNat_le.mp epoch
  have keeps := quiet e inEvents sourceEq i w read (by rw [sameExit]; exact exited)
    (by omega)
  simp [keyCredit, actualBalanceAt, keeps]

end EthLib.Consensus.Models.Network.PinSplit
