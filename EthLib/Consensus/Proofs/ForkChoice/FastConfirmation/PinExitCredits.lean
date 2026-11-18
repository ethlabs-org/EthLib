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

/-- A property of the events of a block replay that each recorded event keeps.

Every operation of a block records an event of its own source.

The deposits of the block are the only events of the source `.deposits`.

No operation of a block records the source `.consolidations`. -/
private theorem blockReplay_invariant {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (P : List (BalanceEvent preset) → Prop) (nil : P [])
    (ordinary : ∀ (l : List (BalanceEvent preset)) (e : BalanceEvent preset),
      e.source ≠ .deposits → e.source ≠ .consolidations → P l → P (l ++ [e]))
    (deposit : ∀ (l : List (BalanceEvent preset)) (s t : BeaconState preset f)
      (before : f < .hegota) (dep : Deposit) (credit debit : ℕ), P l →
      processDeposit config checks before s dep = .ok t →
      P (l ++ [⟨.deposits, ⟨f, s⟩, ⟨f, t⟩, credit, debit⟩]))
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : P post.2 := by
  have carry {pre post : BalanceReplay preset f}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (initial : P pre.2) (ok : carryBalance action pre = .ok post) : P post.2 := by
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact initial
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (notConsolidation : source ≠ .consolidations)
      (initial : P pre.2) (ok : recordBalance source limits action pre = .ok post) :
      P post.2 := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
    exact ordinary _ _ notDeposit notConsolidation initial
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headedOk, rest⟩ := bind_ok_iff.mp ok
  have headedQuiet := carry nil headedOk
  simp only [bellatrix, ↓reduceDIte] at rest
  obtain ⟨executed, executedOk, rest⟩ := bind_ok_iff.mp rest
  have executedQuiet := record (by decide : BalanceSource.withdrawals ≠ .deposits)
    (by decide) headedQuiet executedOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have randaoQuiet := carry executedQuiet randaoOk
  have votedQuiet := carry randaoQuiet votedOk
  have proposedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    votedQuiet proposedOk
  have attestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    proposedQuiet attestedOk
  have rewardedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.rewards ≠ .deposits) (by decide) h ok)
    attestedQuiet rewardedOk
  have depositedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun pre dep post h ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
      exact deposit _ _ _ _ _ _ _ h actionOk)
    rewardedQuiet depositOk
  have exitedQuiet := carry depositedQuiet exitOk
  have changedQuiet := carry exitedQuiet changedOk
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
    requested, consolidations, rest⟩ := rest
  have depositsQuiet := carry changedQuiet depositRequestOk
  have withdrawalsQuiet := carry depositsQuiet withdrawalOk
  have requestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.excess ≠ .deposits) (by decide) h ok)
    withdrawalsQuiet consolidations
  simp only [altair, ↓reduceDIte] at rest
  exact record (by decide : BalanceSource.sync ≠ .deposits) (by decide) requestedQuiet rest

/-- From Electra, the deposit events of a block replay leave the balance of an exiting key alone. -/
private theorem blockReplay_quiet {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : Quiet post.2 :=
  blockReplay_invariant electra early Quiet quiet_nil
    (fun l e notDeposit _ held e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · exact absurd ((List.mem_singleton.mp new) ▸ sourceEq) notDeposit)
    (fun l s t _ dep credit debit held computed e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        exact processDeposit_keeps electra computed)
    engine s block ok

/-- No operation of a block records a consolidation event. -/
private theorem blockReplay_noConsolidations {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam) (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : ∀ e ∈ post.2, e.source ≠ .consolidations :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source ≠ .consolidations)
    (fun _ h => by simp at h)
    (fun l e _ notConsolidation held e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · exact (List.mem_singleton.mp new) ▸ notConsolidation)
    (fun l s t _ dep credit debit held _ e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · obtain rfl := List.mem_singleton.mp new
        exact fun eq => by cases eq)
    engine s block ok

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

/-! ## Consolidation credits of one pass -/

/-- The stake that a pending consolidation can move at a pass: the source's effective balance.

It counts only a source that is unslashed and can withdraw by the next epoch.

A pass reads the other sources without moving anything. -/
def sourceBound {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some v => if v.slashed = false ∧ v.withdrawableEpoch ≤ next then v.effectiveBalance.toNat else 0
  | none => 0

/-- The credits of the balances from one state to another, over the later balances. -/
private def credited {f : Fork} (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

private theorem credited_trans {f : Fork} {a b c : BeaconState preset f}
    (ab : b.balances.data.size = a.balances.data.size)
    (bc : c.balances.data.size = b.balances.data.size) :
    credited a c ≤ credited a b + credited b c := by
  unfold credited
  rw [bc, ab, ← ab, ← Finset.sum_add_distrib]
  rw [ab, bc] at *
  apply Finset.sum_le_sum
  intro j _
  omega

/-- One transfer of a pass credits at most the amount moved. -/
private theorem credited_transfer {f : Fork} {s lowered raised : BeaconState preset f}
    {source target : ValidatorIndex} {moved : Gwei}
    (lowerOk : decreaseBalance s source moved = .ok lowered)
    (raiseOk : increaseBalance lowered target moved = .ok raised) :
    credited s raised ≤ moved.toNat := by
  have sizes := (sameSizes_increaseBalance raiseOk).2.trans (sameSizes_decreaseBalance lowerOk).2
  unfold credited
  have pointwise : ∀ j, actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j ≤
      if target.toNat = j then moved.toNat else 0 := by
    intro j
    by_cases inside : j < s.balances.data.size
    · obtain ⟨balance, found⟩ : ∃ balance, s.balances.data[j]? = some balance :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨down, downFound, downEq⟩ := balance_decreaseBalance lowerOk found
      obtain ⟨up, upFound, upEq⟩ := balance_increaseBalance raiseOk downFound
      simp only [actualBalanceAt, found, upFound, Option.map_some, Option.getD_some]
      split at downEq <;> split at upEq <;> split <;> omega
    · have missing : s.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      have outside : raised.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      simp [actualBalanceAt, missing, outside]
  calc ∑ j ∈ Finset.range raised.balances.data.size,
        (actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j)
      ≤ ∑ j ∈ Finset.range raised.balances.data.size, if target.toNat = j then moved.toNat else 0 :=
        Finset.sum_le_sum fun j _ => pointwise j
    _ ≤ moved.toNat := by
        rw [Finset.sum_ite_eq]
        split <;> omega

/-- A pass credits at most the effective balances of the unslashed due sources it reads.

It keeps the registry and the number of balances. -/
private theorem pass_credits_le {f : Fork} (next : Epoch) :
    ∀ (items : List PendingConsolidation) {s t : BeaconState preset f} {read : ℕ},
      passPendingConsolidations next s items = .ok (t, read) →
      t.validators = s.validators ∧ t.balances.data.size = s.balances.data.size ∧
        credited s t ≤ ((items.take read).map (sourceBound s next)).sum
  | [], s, t, read, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    refine ⟨rfl, rfl, ?_⟩
    simp [credited, actualBalanceAt]
  | c :: rest, s, t, read, computed => by
    simp only [passPendingConsolidations, liftAccessor, bind_ok_iff, mapError_ok_iff] at computed
    obtain ⟨source, sourceRead, computed⟩ := computed
    have found := getValidator_eq_ok_iff.mp sourceRead
    have bound : sourceBound s next c = if source.slashed = false ∧ source.withdrawableEpoch ≤ next
        then source.effectiveBalance.toNat else 0 := by
      simp [sourceBound, found]
    by_cases slashed : source.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at computed
      obtain ⟨⟨state', read'⟩, passed, rfl, rfl⟩ := computed
      obtain ⟨validators, sizes, credits⟩ := pass_credits_le next rest passed
      refine ⟨validators, sizes, ?_⟩
      simpa [bound, slashed, List.take_succ_cons] using credits
    · replace slashed : source.slashed = false := by simpa using slashed
      by_cases early : next < source.withdrawableEpoch
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨rfl, rfl⟩ := computed
        refine ⟨rfl, rfl, ?_⟩
        simp [credited, actualBalanceAt]
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, bind_ok_iff,
          mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨balance, balanceOk, lowered, loweredOk, raised, raisedOk,
          ⟨state', read'⟩, passed, rfl, rfl⟩ := computed
        obtain ⟨validators, sizes, credits⟩ := pass_credits_le next rest passed
        have sameValidators := (increaseBalance_validators raisedOk).trans
          (decreaseBalance_validators loweredOk)
        have step := credited_transfer loweredOk raisedOk
        have sizeStep := (sameSizes_increaseBalance raisedOk).2.trans
          (sameSizes_decreaseBalance loweredOk).2
        have moved : (min balance source.effectiveBalance).toNat ≤
            source.effectiveBalance.toNat := by
          rw [Uint64.toNat_min]; exact Nat.min_le_right _ _
        have restBound : ((rest.take read').map (sourceBound raised next)) =
            ((rest.take read').map (sourceBound s next)) := by
          congr 1
          funext d
          simp only [sourceBound, sameValidators]
        refine ⟨validators.trans sameValidators, sizes.trans sizeStep, ?_⟩
        have total := credited_trans (a := s) (b := raised) (c := state') sizeStep sizes
        rw [restBound] at credits
        have isDue : sourceBound s next c = source.effectiveBalance.toNat := by
          rw [bound]; simp [slashed, UInt64.not_lt.mp early]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, isDue]
        omega

/-! ## The queue of pending consolidations over a block -/

/-- The queue only grows at its end inside a block.

Each new entry has a source whose exit is assigned after the current epoch. -/
private def Grows {f : Fork} (s t : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∃ added : List PendingConsolidation,
    (t.pendingConsolidations electra).data.toList =
      (s.pendingConsolidations electra).data.toList ++ added ∧
    ∀ c ∈ added, ∃ w, t.validators.data[c.sourceIndex.toNat]? = some w ∧
      getCurrentEpoch s < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

private theorem Grows.of_same {f : Fork} {s t : BeaconState preset f}
    (queue : .pectra ≤ f → SamePendingQueue s t) : Grows s t := by
  intro electra
  refine ⟨[], ?_, fun _ member => by simp at member⟩
  rw [show t.pendingConsolidations electra = s.pendingConsolidations electra from
    congrFun (queue electra) electra, List.append_nil]

private theorem Grows.trans {f : Fork} {s u t : BeaconState preset f}
    (one : Grows s u) (two : Grows u t) (life : RegistryLifecycle u t)
    (slot : u.slot = s.slot) : Grows s t := by
  intro electra
  obtain ⟨added, queue, new⟩ := one electra
  obtain ⟨added', queue', new'⟩ := two electra
  have epoch : getCurrentEpoch u = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  refine ⟨added ++ added', by rw [queue', queue, List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
  · obtain ⟨w, read, later, assigned⟩ := new' c fresh
    exact ⟨w, read, epoch ▸ later, assigned⟩

/-- A block step: master's frame and lifecycle, and the growth of the queue. -/
private def GrowStep {f : Fork} (s t : BeaconState preset f) : Prop :=
  Frame s t ∧ RegistryLifecycle s t ∧ Grows s t

private theorem GrowStep.of_same {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (life : RegistryLifecycle s t) (queue : .pectra ≤ f → SamePendingQueue s t) :
    GrowStep s t :=
  ⟨frame, life, Grows.of_same queue⟩

private theorem GrowStep.of_data {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (same : t.validators.data = s.validators.data)
    (queue : .pectra ≤ f → SamePendingQueue s t) : GrowStep s t :=
  GrowStep.of_same frame (RegistryLifecycle.of_data same) queue

private theorem GrowStep.refl {f : Fork} (s : BeaconState preset f) : GrowStep s s :=
  GrowStep.of_data (Frame.refl s) rfl fun _ => rfl

private theorem GrowStep.trans {f : Fork} {s u t : BeaconState preset f}
    (one : GrowStep s u) (two : GrowStep u t) : GrowStep s t :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.trans two.2.2 two.2.1 one.1.slot⟩

private theorem GrowStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → GrowStep a b)
    (ok : xs.foldlM step s = .ok t) : GrowStep s t :=
  foldlM_ok_invariant (GrowStep s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) (GrowStep.refl s) ok

section GrowSteps

variable {f : Fork} {s t : BeaconState preset f}

private theorem growStep_processProposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processProposerSlashing ok).toFrame
    (registryLifecycle_processProposerSlashing ok) (fun _ => SamePendingQueue.proposer ok)

private theorem growStep_processAttesterSlashing {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processAttesterSlashing ok).toFrame
    (registryLifecycle_processAttesterSlashing ok) (fun _ => SamePendingQueue.attester ok)

private theorem growStep_processAttestation {attestation : Attestation preset f} {parent : Slot}
    (ok : processAttestation config checks s parent attestation = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processAttestation ok)
    (congrArg (·.data) (processAttestation_registry ok).1)
    (fun electra => SamePendingQueue.attestation electra ok)

private theorem growStep_processDeposit {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processDeposit ok).toFrame (registryLifecycle_processDeposit ok)
    (fun electra => SamePendingQueue.deposit electra ok)

private theorem growStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processVoluntaryExit ok).toFrame
    (registryLifecycle_processVoluntaryExit ok) (fun _ => SamePendingQueue.voluntary ok)

private theorem growStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processBlsToExecutionChange ok).toFrame
    (registryLifecycle_processBlsToExecutionChange ok) (fun _ => SamePendingQueue.bls ok)

private theorem growStep_processDepositRequest {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processDepositRequest ok).toFrame
    (congrArg (·.data) (processDepositRequest_ok ok).2.1)
    (fun _ => SamePendingQueue.depositRequest ok)

private theorem growStep_processWithdrawalRequest {electra : .pectra ≤ f}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processWithdrawalRequest ok).toFrame
    (registryLifecycle_processWithdrawalRequest ok)
    (fun _ => SamePendingQueue.withdrawalRequest ok)

/-- A queued consolidation assigns its source an exit after the current epoch. -/
private theorem grows_queueConsolidation {electra : .pectra ≤ f}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Grows s t := by
  obtain ⟨churned, written, epoch, withdrawal, -, assigned, later, -, set, validators, pushed⟩ :=
    queueConsolidation_queued delay ok
  intro electra'
  refine ⟨[⟨sourceIndex, targetIndex⟩], ?_, fun c member => ?_⟩
  · exact pushed
  · rw [List.mem_singleton] at member
    subst member
    rw [validators]
    exact ⟨_, getValidator_eq_ok_iff.mp (getValidator_setValidator_self set), later, assigned⟩

/-- A consolidation request switches credentials or queues a consolidation. -/
private theorem growStep_processConsolidationRequest {electra : .pectra ≤ f}
    {request : ConsolidationRequest}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config s electra request = .ok t) : GrowStep s t := by
  have frame := (frame_processConsolidationRequest ok).toFrame
  have life := registryLifecycle_processConsolidationRequest ok
  suffices new : Grows s t from ⟨frame, life, new⟩
  clear frame life
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals try first
    | (cases ok; done)
    | (cases ok; exact Grows.of_same fun _ => rfl)
    | exact Grows.of_same fun _ => SamePendingQueue.compounding (liftAccessor_ok.mp ok)
  exact grows_queueConsolidation delay ok

private theorem growStep_processExecutionRequests {body : BeaconBlockBody preset f}
    {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config s body electra = .ok t) : GrowStep s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processDepositRequest ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processWithdrawalRequest ok) withdrawals).trans
      (GrowStep.fold (fun _ _ _ ok => growStep_processConsolidationRequest delay ok)
        consolidations)

private theorem growStep_processOperations {body : BeaconBlockBody preset f} {parent : Slot}
    (early : f < .glamsterdam) (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processOperations config checks s body parent = .ok t) :
    GrowStep s t := by
  unfold processOperations at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have c : GrowStep exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact GrowStep.fold (fun _ _ _ ok => growStep_processBlsToExecutionChange ok) changes
    · cases changes; exact GrowStep.refl _
  have r : GrowStep changed t := by
    split at requests
    · exact growStep_processExecutionRequests delay requests
    · cases requests; exact GrowStep.refl _
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processProposerSlashing ok) proposers).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttesterSlashing ok) attesters).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttestation ok) attested).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processDeposit ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processVoluntaryExit ok) exits).trans <|
    c.trans r

/-- A block from Altair and before Gloas keeps the frame and the lifecycle.

It also grows the queue. -/
private theorem growStep_processBlock {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processBlock config checks engine s block = .ok t) : GrowStep s t := by
  unfold processBlock at ok
  simp only [altair, ↓reduceDIte] at ok
  unfold processBlockAltair at ok
  simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at ok
  obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
    votedOk, operated, operatedOk, synced⟩ := ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at paidOk
  cases paidOk
  have header : GrowStep s headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact GrowStep.of_data (frame_processBlockHeader headedOk).toFrame rfl fun _ => rfl
  have e : GrowStep headed executed := by
    split at executedOk
    · exact GrowStep.of_data (frame_processBlockExecution executedOk).toFrame
        (congrArg (·.data) (processBlockExecution_validators executedOk))
        (fun _ => SamePendingQueue.blockExecution early executedOk)
    · cases executedOk; exact GrowStep.refl _
  have randao : GrowStep executed revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    exact GrowStep.of_data (frame_processRandao revealedOk).toFrame rfl fun _ => rfl
  have v : GrowStep revealed voted := by
    split at votedOk
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact GrowStep.of_data (frame_processEth1Data votedOk).toFrame (by rw [← rest])
        (fun _ => by unfold SamePendingQueue; rw [← rest])
    · cases votedOk; exact GrowStep.refl _
  have sync : GrowStep operated t := by
    have frame := (frame_processSyncAggregate synced).toFrame
    obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
    exact GrowStep.of_data frame rfl fun _ => rfl
  exact header.trans <| e.trans <| randao.trans <| v.trans <|
    (growStep_processOperations early delay operatedOk).trans sync

end GrowSteps

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
