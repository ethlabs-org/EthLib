module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.FirstDrop
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Credits
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.DirectSafety.Provenance
import EthLib.Consensus.Proofs.Transition.ChainRoots

/-!
# The floor of one epoch of a key, through any slashing of the key

A run of a key from Fulu crosses at most one epoch boundary, by its last step.

The balance of the key at the end, plus its debits, is at least the least of its balance at the start and any cap below its largest effective balance.

The debits are the pass of the rewards at the last state of the first epoch, the sync penalties of the key, and its payments from the queue of partial withdrawals.

A slash in the run adds the initial slashing penalty, over the slashing quotient, at the effective balance at the start.

The effective balance changes only at the end of an epoch, after any slashing in it, so it is the same at every slash of the run.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

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

open DirectSafety.Apriori.Internal in
/-- A trace from an account keeps the floor, less the penalty of a slash if it holds one.

The penalty is the slash term of the trace at the high-water mark of the slash. -/
private theorem FloorTrace.slashed_balance_floor {low base quotient : ℕ} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (initial : low ≤ a.balance + a.debt) :
    low ≤ b.balance + b.debt +
      b.slashedHigh.elim 0 (fun h => base / quotient + (h - base)) := by
  induction trace with
  | nil => exact Nat.le_trans initial (Nat.le_add_right _ _)
  | credit prior paid ih =>
    dsimp only at *
    omega
  | debit prior paid ih =>
    dsimp only at *
    omega
  | sweep prior paid ih =>
    dsimp only at *
    omega
  | update prior backed ih => exact ih
  | slash prior unused paid cap ih =>
    rename_i b balance penalty
    dsimp only at *
    rw [unused] at ih
    simp only [Option.elim] at ih ⊢
    omega

/-- Every fork from Fulu on has the slashing quotient of Electra. -/
private theorem mspq_fusaka {f : Fork} (h : .fusaka ≤ f) :
    (EthLib.Consensus.parameters preset f).MIN_SLASHING_PENALTY_QUOTIENT =
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT := by
  have pectra : .pectra ≤ f := Nat.le_trans (by decide) h
  have pectra' : .pectra ≤ Fork.fusaka := by decide
  simp [EthLib.Consensus.parameters, ge_iff_le, pectra, pectra']

open Classical DirectSafety.Apriori.Internal in
/-- The floor of one epoch of a key, through any slashing of the key.

The pass of the rewards at the last state of the first epoch is the hypothesis `pass`. -/
theorem epochFloor (pass : PassBoundStatement preset config checks) :
    EpochFloorStatement preset config checks := by
  intro g m n shared genesis caps delay vector positive r hm hn shape i val hval hact hexit hslash
    C hC events replayed
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r.chainSteps) hn
  have inside : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp hval).1
  obtain ⟨iv, rfl⟩ : ∃ iv : ValidatorIndex, iv.toNat = i :=
    ⟨i.toUInt64, toNat_toUInt64_of_lt (m.state.validators.bound mEarly) inside⟩
  have altair : .altair ≤ m.fork := Nat.le_trans (by decide) hm
  have mn : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch n.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r.chainSteps)
  have endEpoch : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch m.state).toNat + 1 := by
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · rw [same]; omega
    · omega
  -- Every step of the run starts in the epoch of `m`, at a fork from Fulu.
  have starts : ∀ {a b : ForkedBeaconState preset} (pre' : Run config checks m a)
      (step : Step config checks a b) (post : Run config checks b n),
      (pre'.snoc step).append post = r → getCurrentEpoch a.state = getCurrentEpoch m.state ∧
        .fusaka ≤ a.fork ∧ b.fork < .glamsterdam := by
    intro a b pre' step post split
    have lo := currentEpoch_le_of_chainSteps pre'.chainSteps
    have hi := currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps
    have forkLo := fork_le_of_chainSteps pre'.chainSteps
    have forkHi := fork_le_of_chainSteps post.chainSteps
    refine ⟨?_, Nat.le_trans hm forkLo, Nat.lt_of_le_of_lt forkHi hn⟩
    have member : r.Contains step := by
      rw [← split, Run.contains_append]
      exact .inl (.last _ _)
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · exact UInt64.le_antisymm (same ▸ hi) lo
    · subst req
      cases member with
      | last => exact hz
      | earlier member _ =>
        obtain ⟨_, q, _⟩ := pre.contains_split step member
        exact UInt64.le_antisymm
          (hz ▸ currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append q).chainSteps) lo
  obtain ⟨z, pre, post, hsplit, hz, hpen⟩ : ∃ (z : ForkedBeaconState preset)
      (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      (events.map (penaltyDebit iv.toNat)).sum ≤
        (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
            ∃ total, getTotalActiveBalance z.state = .ok total then
          passRate config z iv.toNat else 0) := by
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · refine ⟨n, r, .nil, rfl, same, ?_⟩
      have free := (epoch_sync_data r altair hn same _ replayed).2.1
      have quiet : ¬ (getCurrentEpoch m.state < getCurrentEpoch n.state ∧
          ∃ total, getTotalActiveBalance n.state = .ok total) := fun h => absurd h.1 (by simp [same])
      simp only [quiet, ↓reduceIte]
      exact Nat.le_of_eq (List.sum_eq_zero fun _ member => by
        obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
        simp [penaltyDebit, (free e present).1, (free e present).2])
    · subst req
      refine ⟨z, pre, Run.nil.snoc (Step.slot ok), rfl, hz, ?_⟩
      have crossed : getCurrentEpoch m.state < getCurrentEpoch n.state :=
        UInt64.lt_iff_toNat_lt.mpr (by omega)
      have hzn : (getCurrentEpoch z.state).toNat = (getCurrentEpoch m.state).toNat := by rw [hz]
      have bound := pass pre ok altair hn hz (by omega) iv.toNat replayed
      by_cases found : ∃ total, getTotalActiveBalance z.state = .ok total
      · simpa [crossed, found] using bound
      · simpa [found] using bound
  refine ⟨z, pre, post, hsplit, hz, ?_⟩
  have effEq : ∀ {a b : ForkedBeaconState preset} (pre' : Run config checks m a)
      (step : Step config checks a b) (post' : Run config checks b n),
      (pre'.snoc step).append post' = r → effectiveAt a iv.toNat = effectiveAt m iv.toNat := by
    intro a b pre' step post' split
    obtain ⟨epoch, -, bEarly⟩ := starts pre' step post' split
    have aEarly : a.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le bEarly
    exact run_same_epoch_effective pre' aEarly epoch iv.toNat inside
  have positive' : 0 < (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    rw [mspq_fusaka hm]; exact positive
  have half : (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat =
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 := by simp
  obtain ⟨last, trace, balance, debt, -, w, final, -, used, -, bounded, startSlashed⟩ :=
    FloorTrace.run_of_le_cap_general shared r genesis caps delay hn
      (getCurrentEpoch m.state).toNat endEpoch iv val hval hact
      (min (actualBalanceAt m iv.toNat) C) (effectiveAt m iv.toNat)
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
      (Nat.le_trans (Nat.min_le_right _ _) hC) positive'
      (fun {a b} pre' step post' split w found => by
        obtain ⟨epoch, fusaka, bEarly⟩ := starts pre' step post' split
        have epochs : (getCurrentEpoch a.state).toNat = (getCurrentEpoch m.state).toNat := by
          rw [epoch]
        have atMost := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
          ((Run.nil.snoc step).append post').chainSteps)
        have inv := Run.invariant genesis.invariant (shared.append pre')
        refine ⟨?_, ⟨fun _ => by omega, fun slashed => ?_⟩, ?_, fun evs hevs e member crossing => ?_⟩
        · obtain ⟨w', found', life⟩ := post'.registryLifecycle.validators iv.toNat w found
          have kept := hexit w' found'
          have small := w'.exitEpoch.toNat_lt
          by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
          · rw [assigned]
            simp [FAR_FUTURE_EPOCH]
            omega
          · rw [← life.exitEpoch assigned]; exact kept
        · have := hslash slashed
          omega
        · rw [mspq_fusaka hm, mspq_fusaka fusaka]
        · have sites := (step.balanceEvents_sites bEarly inv caps.compounding hevs) e member
          obtain ⟨before, -⟩ := sites.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 crossing
          exact Nat.not_le_of_lt before (Nat.le_trans (by decide) fusaka))
      replayed
  obtain ⟨-, slashBound⟩ := bounded (effectiveAt m iv.toNat) le_rfl
    (fun pre' step post' split => (effEq pre' step post' split).le)
  have floor := FloorTrace.slashed_balance_floor trace
    (by simp)
  have split : (events.map (floorPenaltyDebit iv.toNat)).sum =
      (events.map (penaltyDebit iv.toNat)).sum + (events.map (keySyncDebit iv.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  have index : iv.toNat.toUInt64 = iv := by simp
  rw [balance, debt, split] at floor
  rw [index]
  cases hs : last.slashedHigh with
  | none =>
    simp only [hs, Option.elim] at floor
    omega
  | some h =>
    have atMost := slashBound h hs
    have slashed : w.slashed = true := by
      cases hw : w.slashed
      · simp [hs, hw] at used
      · rfl
    have unslashed : val.slashed = false := by
      cases hv : val.slashed
      · rfl
      · have := startSlashed hv
        rw [hs] at this
        cases this
    simp only [hs, Option.elim] at floor
    have cond : val.slashed = false ∧ ∃ w, n.state.validators.data[iv.toNat]? = some w ∧
        w.slashed = true := ⟨unslashed, w, final, slashed⟩
    simp only [cond, and_self, ↓reduceIte]
    omega

end EthLib.Consensus.Models.Network.PinSplit
