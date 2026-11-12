module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Readiness
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Call
import Mathlib.Tactic.FinCases

/-! An allowed synchronous execution containing a nontrivial fast-confirmation call.

Small message and store codes let the kernel check the finite network schedule without hashing.

Their interpretation uses the certified handlers and the unchanged honest-validator protocol.

After 73 events, all messages have been delivered and an infinite tail advances only time.

The `Joint` module certifies every premise of Theorem 1 for this execution. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness.Trace

open Base

/-- The only store shapes used in the finite trace. -/
inductive Local where
  | anchor
  | ticked
  | running (time : UInt64) (count : Nat)
  deriving DecidableEq

/-- Interpret a store code using the already certified candidate stores. -/
def Local.store : Local → Store preset .phase0
  | .anchor => FiveValidatorWitness.anchor
  | .ticked => FiveValidatorWitness.ticked
  | .running time count => FiveValidatorWitness.running time count

/-- Code zero is the child block; the other three codes are votes at those slots. -/
def message (tag : Fin 4) : Message preset .phase0 :=
  if tag = 0 then .block signedBlock else .attestation (vote tag.val.toUInt64)

/-- A finite description of a world, retaining the state and view of every validator. -/
structure Snapshot where
  time : Nat
  sent : Finset (Fin 4)
  view : ValidatorIndex → Finset (Fin 4)
  state : ValidatorIndex → Local

/-- Interpret finite message sets as network views without assuming message injectivity. -/
def Snapshot.world (w : Snapshot) : World ValidatorIndex (Message preset .phase0)
    (Store preset .phase0) :=
  ⟨w.time, message '' (w.sent : Set (Fin 4)),
    fun v => message '' (w.view v : Set (Fin 4)), fun v => (w.state v).store⟩

/-- The trace sends single messages, broadcasts them, ticks, and handles them one node at a time. -/
inductive Action where
  | wait (time : Nat)
  | send (v : ValidatorIndex) (tag : Fin 4)
  | deliver (tag : Fin 4)
  | move (v : ValidatorIndex) (s : Local)

/-- Every encoded action is an event of the unchanged network model. -/
def Action.event : Action → Event ValidatorIndex (Message preset .phase0) (Store preset .phase0)
  | .wait time => .wait time
  | .send v tag => .send v (message tag)
  | .deliver tag => .deliver (fun _ => {message tag})
  | .move v s => .move v s.store

/-- Apply the same network update to the finite codes. -/
def Snapshot.apply (w : Snapshot) : Action → Snapshot
  | .wait time => { w with time }
  | .send v tag => { w with
      sent := insert tag w.sent
      view := Function.update w.view v (insert tag (w.view v)) }
  | .deliver tag => { w with view := fun v => insert tag (w.view v) }
  | .move v s => { w with state := Function.update w.state v s }

/-- Interpreting an encoded update gives exactly the network's update. -/
theorem apply_world (w : Snapshot) (a : Action) :
    (w.apply a).world = w.world.apply a.event := by
  cases a with
  | wait time => rfl
  | send v tag =>
    simp only [Snapshot.apply, Snapshot.world, Action.event, World.apply]
    congr 1
    · simp
    · funext u
      by_cases same : u = v
      · subst u; simp
      · simp [Function.update_of_ne same]
  | deliver tag =>
    simp only [Snapshot.apply, Snapshot.world, Action.event, World.apply]
    congr 1
    funext v
    simp [Set.union_comm]
  | move v s =>
    simp only [Snapshot.apply, Snapshot.world, Action.event, World.apply]
    congr 1
    funext u
    by_cases same : u = v
    · subst u; simp
    · simp [Function.update_of_ne same]

/-- Interpreting a finite run preserves every event, view, and local state. -/
theorem fold_world (w : Snapshot) (actions : List Action) :
    (actions.foldl Snapshot.apply w).world =
      (actions.map Action.event).foldl World.apply w.world := by
  induction actions generalizing w with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons, List.map_cons, ih, apply_world]

/-- A decidable version of processing completeness for encoded messages. -/
def Ready (time : UInt64) (count : Nat) (view : Finset (Fin 4)) : Prop :=
  ∀ tag ∈ view, tag = 0 ∨ tag.val ≤ count ∨ time / 1000 ≤ tag.val.toUInt64

instance (time : UInt64) (count : Nat) (view : Finset (Fin 4)) :
    Decidable (Ready time count view) := inferInstanceAs (Decidable (∀ tag ∈ view, _))

/-- Encoded completeness suffices for the actual handlers. -/
theorem ready_view {time : UInt64} {count : Nat} {view : Finset (Fin 4)}
    (ready : Ready time count view) :
    ReadyView time count (message '' (view : Set (Fin 4))) := by
  rintro _ ⟨tag, member, rfl⟩
  rcases ready tag member with zero | old | early
  · exact .inl (by simp [message, zero])
  · by_cases zero : tag = 0
    · exact .inl (by simp [message, zero])
    · refine .inr ⟨tag.val.toUInt64, ?_, by simp [message, zero], .inl ?_⟩
      · fin_cases tag <;> simp_all
      · exact (Nat.mod_le _ _).trans old
  · by_cases zero : tag = 0
    · exact .inl (by simp [message, zero])
    · refine .inr ⟨tag.val.toUInt64, ?_, by simp [message, zero], .inr early⟩
      fin_cases tag <;> simp_all

/-- The same-slot ticks and three boundary ticks used in this schedule. -/
def Tick (first next : UInt64) : Prop :=
  first ≤ next ∧
    ((first / 1000 = next / 1000 ∧ (first < 2000 ↔ next < 2000)) ∨
      (first = 1999 ∧ next = 2000) ∨
      (first = 2999 ∧ next = 3000) ∨
      (first = 3999 ∧ next = 4000))

instance (first next : UInt64) : Decidable (Tick first next) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Each encoded clock step runs the real tick handler successfully. -/
theorem tick_ok {first next : UInt64} (count : Nat) (tick : Tick first next) :
    (running first count).onTick config next = .ok (running next count) := by
  rcases tick.2 with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact running_tick_same first next count same.1 (propext same.2)
  · exact running_tick_boundary count (slot := 1) (.inl rfl)
  · exact running_tick_boundary count (slot := 2) (.inr (.inl rfl))
  · exact running_tick_boundary count (slot := 3) (.inr (.inr rfl))

/-- Local moves admitted by the handler certificates, including receipt of each used message. -/
def PermittedMove (time : Nat) (view : Finset (Fin 4)) (before after : Local) : Prop :=
  match before, after with
  | .anchor, .ticked => time = 1000
  | .ticked, .running next count => next = 1000 ∧ count = 0 ∧ 0 ∈ view
  | .running first count, .running next more =>
      (more = count ∧ time = next.toNat ∧ Tick first next) ∨
      (next = first ∧
        ∃ tag : Fin 4, tag ≠ 0 ∧ tag ∈ view ∧ first = (tag.val.toUInt64 + 1) * 1000 ∧
          count = tag.val - 1 ∧ more = tag.val)
  | _, _ => False

instance (time : Nat) (view : Finset (Fin 4)) (before after : Local) :
    Decidable (PermittedMove time view before after) := by
  unfold PermittedMove
  split <;> infer_instance

/-- A permitted encoded move is a genuine handler step, not a substitute transition rule. -/
theorem move_handles {time : Nat} {view : Finset (Fin 4)} {before after : Local}
    (valid : PermittedMove time view before after) :
    Handles config .acceptAll sources time (message '' (view : Set (Fin 4)))
      before.store after.store := by
  cases before <;> cases after <;> try exact False.elim valid
  case anchor.ticked =>
    change time = 1000 at valid
    subst time
    exact .tick (by decide) (by decide) first_tick
  case ticked.running next count =>
    obtain ⟨rfl, rfl, held⟩ := valid
    refine .block ⟨0, held, rfl⟩ ?_
    exact first_admitted
  case running.running first count next more =>
    rcases valid with ⟨rfl, rfl, tick⟩ | ⟨rfl, tag, nonzero, held, rfl, rfl, rfl⟩
    · refine .tick (UInt64.le_iff_toNat_le.mp tick.1) next.toNat_lt ?_
      simpa only [Local.store, Nat.toUInt64_eq, UInt64.ofNat_toNat] using tick_ok more tick
    · have within : tag.val.toUInt64 = 1 ∨ tag.val.toUInt64 = 2 ∨
          tag.val.toUInt64 = 3 := by fin_cases tag <;> simp_all
      refine .attestation (attestation := vote tag.val.toUInt64)
        ⟨tag, held, by simp [message, nonzero]⟩ ?_
      have small : tag.val < 18446744073709551616 := by omega
      simpa only [Local.store, Nat.toUInt64_eq, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt small] using running_vote_step within

/-- Decidable sufficient conditions for an encoded event to be allowed by the protocol. -/
def Permitted (w : Snapshot) : Action → Prop
  | .wait time => w.time ≤ time
  | .deliver tag => tag ∈ w.sent
  | .move v s => v ∈ honest ∧ PermittedMove w.time (w.view v) (w.state v) s
  | .send v tag => tag = 0 ∨
      match w.state v with
      | .running time count =>
          tag ≠ 0 ∧ v = voter tag.val.toUInt64 ∧ time = tag.val.toUInt64 * 1000 + 333 ∧
          w.time = time.toNat ∧ count ≤ 3 ∧ Ready time count (w.view v)
      | _ => False

instance (w : Snapshot) (a : Action) : Decidable (Permitted w a) := by
  cases a with
  | wait time => unfold Permitted; infer_instance
  | send v tag =>
    simp only [Permitted]
    cases w.state v <;> infer_instance
  | deliver tag => unfold Permitted; infer_instance
  | move v s => unfold Permitted honest; infer_instance

/-- The honest-validator protocol with the fixed candidate's parameters and assignment. -/
abbrev protocol := honestForkChoice config .acceptAll sources (state bodyRoot)
  (anchorBlock stateRoot) assignment 0

/-- The finite schedule checks imply the original protocol's permission predicate. -/
theorem permitted_allowed (w : Snapshot) (a : Action) (valid : Permitted w a) :
    Allowed protocol honest w.world a.event := by
  cases a with
  | wait time => exact valid
  | deliver tag =>
    intro v m member
    have eq : m = message tag := member
    subst m
    exact ⟨tag, valid, rfl⟩
  | move v s => exact ⟨valid.1, move_handles valid.2⟩
  | send v tag =>
    rcases valid with zero | valid
    · subst tag
      refine ⟨?_, fun _ x statement _ => ?_⟩
      · intro x statement
        change x ∈ statements config .acceptAll (state bodyRoot) (anchorBlock stateRoot)
          (message 0) at statement
        rw [show message 0 = .block signedBlock from rfl, block_statements] at statement
        exact False.elim statement
      · rw [show message 0 = .block signedBlock from rfl, block_statements] at statement
        exact False.elim statement
    · cases localState : w.state v with
      | anchor => simp [localState] at valid
      | ticked => simp [localState] at valid
      | running time count =>
        simp only [localState] at valid
        obtain ⟨nonzero, rfl, rfl, clock, bound, ready⟩ := valid
        have within : tag.val.toUInt64 = 1 ∨ tag.val.toUInt64 = 2 ∨
            tag.val.toUInt64 = 3 := by fin_cases tag <;> simp_all
        change (∀ x ∈ statements _ _ _ _ (message tag), _) ∧ _
        refine ⟨?_, fun _ => ?_⟩
        · intro x statement _ other
          rw [message, ite_eq_right nonzero] at statement
          have eq := running_vote_statements within statement
          exact False.elim (other (congrArg Prod.fst eq))
        · change HonestSends _ _ _ _ _ _ _ _ _ _ _ _
          simp only [Snapshot.world, localState, Local.store, clock, message,
            ite_eq_right nonzero]
          exact running_vote_sends within bound (ready_view ready)

/-- The four honest validators, in their processing order. -/
def validators : List ValidatorIndex := [0, 1, 2, 4]

/-- Every validator processes one step at the same network time. -/
def moveAll (s : Local) : List Action := validators.map (fun v => .move v s)

/-- One duty round: vote at its deadline, then process at and just before the next boundary. -/
def round (tag : Fin 4) : List Action :=
  let slot := tag.val.toUInt64
  let count := tag.val - 1
  [.wait (slot * 1000 + 333).toNat] ++ moveAll (.running (slot * 1000 + 333) count) ++
    [.send (voter slot) tag, .deliver tag, .wait (slot * 1000 + 999).toNat] ++
    moveAll (.running (slot * 1000 + 999) count) ++ [.wait ((slot + 1) * 1000).toNat] ++
    moveAll (.running ((slot + 1) * 1000) count) ++
    moveAll (.running ((slot + 1) * 1000) tag.val)

/-- The block is broadcast first, followed by the three honest duty rounds. -/
def actions : List Action :=
  [.send 3 0, .deliver 0] ++ moveAll .ticked ++ moveAll (.running 1000 0) ++
    round 1 ++ round 2 ++ round 3

/-- The execution starts at slot one with empty views and initialized anchor stores. -/
def initial : Snapshot := ⟨1000, ∅, fun _ => ∅, fun _ => .anchor⟩

/-- The finite encoded world after a prefix of the schedule. -/
def snapshot (n : Nat) : Snapshot := (actions.take n).foldl Snapshot.apply initial

/-- The actual network events of the finite schedule. -/
def events := actions.map Action.event

/-- Encoding does not change the model's empty initial world. -/
theorem initial_world :
    initial.world = World.initial 1000 (fun _ => FiveValidatorWitness.anchor) := by
  simp [initial, Snapshot.world, World.initial, Local.store]

/-- A prefix snapshot describes the actual world after that prefix. -/
theorem snapshot_world (n : Nat) :
    (snapshot n).world = (events.take n).foldl World.apply
      (World.initial 1000 (fun _ => FiveValidatorWitness.anchor)) := by
  rw [← initial_world, events, ← List.map_take, ← fold_world]
  rfl

/-- The kernel checks every permission in the finite schedule. -/
theorem permitted_actions :
    ∀ n : Fin actions.length, Permitted (snapshot n) actions[n] := by
  decide +kernel

/-- Every event in the prefix is allowed in the world before it. -/
theorem allowed_events (n : Nat) (h : n < events.length) :
    Allowed protocol honest
      ((events.take n).foldl World.apply
        (World.initial 1000 (fun _ => FiveValidatorWitness.anchor))) events[n] := by
  rw [← snapshot_world]
  simpa only [events, List.getElem_map, Fin.getElem_fin] using
    permitted_allowed _ _ (permitted_actions ⟨n, by simpa [events] using h⟩)

/-- The finite prefix ends exactly at the start of epoch one. -/
theorem final_clock :
    (events.foldl World.apply (World.initial 1000 (fun _ => FiveValidatorWitness.anchor))).time =
      4000 := by
  have h := congrArg World.time (snapshot_world events.length)
  change (snapshot 73).world.time = _ at h
  have clock : (snapshot 73).world.time = 4000 := rfl
  rw [clock] at h
  simpa only [List.take_length] using h.symm

/-- An infinite allowed execution: the certified prefix followed by increasing waits. -/
def execution : Execution protocol honest :=
  FinitePrefix.execution protocol honest 1000 (fun _ => FiveValidatorWitness.anchor)
    events 4000 final_clock allowed_events

/-- Bounded-time reasoning may use the finite snapshots of the execution. -/
theorem world_prefix (n : Nat) (h : n ≤ 73) : execution.world n = (snapshot n).world := by
  rw [Execution.world, execution, FinitePrefix.execution]
  rw [FinitePrefix.world_prefix _ _ _ n (by exact h), ← snapshot_world]

/-- At the call, validator zero has processed the child and the first two votes. -/
theorem call_store : (execution.world 52).state 0 = running 3000 2 := by
  rw [world_prefix 52 (by decide)]
  rfl

/-- The unique send time of each message. -/
def sentAt (tag : Fin 4) : Nat := if tag = 0 then 1000 else tag.val * 1000 + 333

/-- No view contains a message before its send time. -/
theorem held_after_send : ∀ n : Fin 74, ∀ v : Fin 5, ∀ tag : Fin 4,
    tag ∈ (snapshot n).view v.val.toUInt64 → sentAt tag ≤ (snapshot n).time := by
  decide +kernel

/-- Delivery finishes before the network clock advances past each send time. -/
theorem delivered_before_wait : ∀ n : Fin 74, ∀ v : Fin 5, ∀ tag : Fin 4,
    sentAt tag < (snapshot n).time → tag ∈ (snapshot n).view v.val.toUInt64 := by
  decide +kernel

/-- Every sent message has reached every registry validator before the infinite wait tail. -/
theorem final_delivered : ∀ v : Fin 5,
    (snapshot 73).sent ⊆ (snapshot 73).view v.val.toUInt64 := by
  decide +kernel

/-- Every honest validator is one of the five positions checked by the finite certificates. -/
theorem honest_index {v : ValidatorIndex} (h : v ∈ honest) :
    ∃ i : Fin 5, i.val.toUInt64 = v := by
  simp only [honest, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨4, rfl⟩

/-- The entire infinite execution is synchronous with a positive delay of one millisecond. -/
theorem synchronous : execution.Synchronous 1 := by
  apply FinitePrefix.synchronous_execution protocol honest 1000
    (fun _ => FiveValidatorWitness.anchor) events 4000 final_clock allowed_events 1 (by decide)
  · intro u honestU
    obtain ⟨u, rfl⟩ := honest_index honestU
    have last := snapshot_world events.length
    simp only [List.take_length] at last
    rw [← last]
    rintro _ ⟨tag, member, rfl⟩
    exact ⟨tag, final_delivered u member, rfl⟩
  · intro n k later bounded v honestV u honestU m member elapsed
    obtain ⟨v, rfl⟩ := honest_index honestV
    obtain ⟨u, rfl⟩ := honest_index honestU
    rw [← snapshot_world n] at member
    rw [← snapshot_world k]
    rw [← snapshot_world n, ← snapshot_world k] at elapsed
    obtain ⟨tag, held, rfl⟩ := member
    have kBound : k < 74 := by change k ≤ 73 at bounded; omega
    have nBound : n < 74 := by omega
    have afterSend := held_after_send ⟨n, nBound⟩ v tag held
    change sentAt tag ≤ (snapshot n).time at afterSend
    refine ⟨tag, delivered_before_wait ⟨k, kBound⟩ u tag ?_, rfl⟩
    change sentAt tag < (snapshot k).time
    change (snapshot n).time + 1 ≤ (snapshot k).time at elapsed
    omega

/-- The caller has processed every message its handlers accept at the call time. -/
theorem call_ready :
    UpToDate config .acceptAll sources (execution.world 52).time
      ((execution.world 52).view 0) ((execution.world 52).state 0) := by
  rw [world_prefix 52 (by decide)]
  exact running_up_to_date 3000 (count := 2) (by decide) (ready_view (by decide))

/-- An allowed execution contains a full call whose walk confirms the distinct slot-one child.

The phase0 candidate uses a custom minimal preset with zero shuffle rounds and four slots per epoch.

Its custom configuration has zero proposer boost and confirmation threshold 34, not mainnet values.

This theorem certifies the execution and its advancing call; `Joint` proves the other premises. -/
theorem confirms_by_walk :
    (execution.world 52).time = 3000 ∧
    ((execution.world 52).state 0).onFastConfirmation config (getFastConfirmationStore anchor) =
      .ok confirmed ∧
    ((execution.world 52).state 0).findLatestConfirmedDescendant config
      (getFastConfirmationStore anchor) blockRoot anchorRoot = .ok blockRoot ∧
    confirmed.confirmedRoot ≠ anchorRoot := by
  refine ⟨?_, ?_, ?_, blockRoot_ne_anchorRoot⟩
  · rw [world_prefix 52 (by decide)]; rfl
  · rw [call_store]; exact running_call
  · rw [call_store]; exact running_walk _ rfl

end EthLib.Consensus.Models.Network.FiveValidatorWitness.Trace
