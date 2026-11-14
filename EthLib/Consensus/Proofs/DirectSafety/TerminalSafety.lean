module

public import EthLib.Consensus.Proofs.DirectSafety.TerminalFields
public import EthLib.Consensus.Proofs.DirectSafety.TerminalQuorums
public import EthLib.Consensus.Proofs.DirectSafety.Safety
import all EthLib.Consensus.Proofs.DirectSafety.Safety
import all EthLib.Consensus.Proofs.DirectSafety.Conflict
import all EthLib.Consensus.Proofs.DirectSafety.Fields
import all EthLib.Consensus.Proofs.DirectSafety.Hashes

/-!
# Accountable safety including a terminal justification projection

All accepted votes belong to real runs, including votes counted by the terminal projection.

The projection contributes its actual input-state drift, not a hypothetical future execution.

The crossing argument follows [Combining GHOST and Casper][gasper], Lemmas 4.11 and 5.1.

Section 8.5 supplies the one- and two-epoch finalization cases.

The weight transfer here uses observed effective-weight drift at the selected concrete states.

[gasper]: https://arxiv.org/abs/2003.03052
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem view_epochs {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    {view : TerminalView a} (call : ViewQuorum run view) :
    call.source.epoch < call.target.epoch := by
  cases call with
  | inl c => exact call_epochs run genesis c
  | inr c => exact terminal_quorum_epochs run parameters genesis view c

private theorem view_attestations {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (_early : a.fork < .hegota) {view : TerminalView a}
    (call : ViewQuorum run view) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target := by
  exact view_quorum_attestations run parameters genesis call

private theorem view_same_epoch {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .hegota) (earlyB : b.fork < .hegota)
    {va : TerminalView a} {vb : TerminalView b}
    (one : ViewQuorum left va) (two : ViewQuorum right vb)
    (epoch : one.target.epoch = two.target.epoch) (different : one.target ≠ two.target) :
    ∀ key ∈ one.voters ∩ two.voters, Slashable left right key := by
  intro key member
  obtain ⟨inOne, inTwo⟩ := Finset.mem_inter.mp member
  obtain ⟨d₁, accepted₁, _, target₁⟩ :=
    view_attestations left parameters genesis earlyA one key inOne
  obtain ⟨d₂, accepted₂, _, target₂⟩ :=
    view_attestations right parameters genesis earlyB two key inTwo
  refine ⟨d₁, d₂, Or.inl accepted₁, Or.inr accepted₂, ?_⟩
  apply isSlashableAttestationData_of_double
  · intro same
    exact different (target₁.symm.trans ((congrArg AttestationData.target same).trans target₂))
  · rw [target₁, target₂]
    exact epoch

private theorem view_drift {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    {view : TerminalView a} (call : ViewQuorum (shared.append tail) view)
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high) :
    stateDrift x call.state ≤ terminalDrift high tail view := by
  cases call with
  | inl c =>
    have bound := selected_call_drift_le shared tail parameters low high starts c lower upper
    cases view with
    | realized => exact bound
    | pulled after ok => exact bound.trans (Nat.le_max_left _ _)
  | inr c =>
    change stateDrift x a ≤ terminalDrift high tail view
    rw [c.selected, terminalDrift_pulled]
    exact Nat.le_max_right _ _

private theorem terminal_pair_bound {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    {low high : Nat} (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (enoughA : ∀ high, EnoughStake (shared.append left) high)
    (enoughB : ∀ high, EnoughStake (shared.append right) high)
    {va : TerminalView a} {vb : TerminalView b}
    (terminalA : ∀ high, va.enough high) (terminalB : ∀ high, vb.enough high)
    (one : ViewQuorum (shared.append left) va) (two : ViewQuorum (shared.append right) vb)
    (lowerOne : low ≤ one.target.epoch.toNat) (lowerTwo : low ≤ two.target.epoch.toNat)
    (upperOne : one.target.epoch.toNat ≤ high) (upperTwo : two.target.epoch.toNat ≤ high)
    (overlap : ∀ key ∈ one.voters ∩ two.voters,
      Slashable (shared.append left) (shared.append right) key) :
    Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state)
        (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
      stateDrift x one.state + stateDrift x two.state := by
  have bound := view_pair_bound shared left right parameters genesis starts
    (enoughA high) (enoughB high) (terminalA high) (terminalB high) one two
    lowerOne lowerTwo upperOne upperTwo overlap
  have total := active_stake_le_fullRunAccountable shared left right genesis
    (stateDrift x one.state + stateDrift x two.state) (by simpa [Nat.add_assoc] using bound)
  simpa [Nat.add_assoc] using total

private theorem view_history_positive {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    {view : TerminalView a} {c : Checkpoint} (history : ViewHistory run view c) :
    0 < c.epoch.toNat := by
  let call := history.calls.getLast history.nonempty
  have target := history.finish call (List.getLast?_eq_some_getLast history.nonempty)
  have forward := UInt64.lt_iff_toNat_lt.mp (view_epochs run parameters genesis call)
  rw [target] at forward
  omega

/-- Equal-epoch fields include either endpoint fields or one terminal projection per branch. -/
theorem accountable_terminal_justified_unique_gloas {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (va : TerminalView a) (vb : TerminalView b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .hegota) (earlyB : b.fork < .hegota)
    (enoughA : ∀ high, EnoughStake (shared.append left) high)
    (enoughB : ∀ high, EnoughStake (shared.append right) high)
    (terminalA : ∀ high, va.enough high) (terminalB : ∀ high, vb.enough high) (j k : Checkpoint)
    (fieldA : j = va.state.previousJustifiedCheckpoint ∨ j = va.state.currentJustifiedCheckpoint)
    (fieldB : k = vb.state.previousJustifiedCheckpoint ∨ k = vb.state.currentJustifiedCheckpoint)
    (epoch : j.epoch = k.epoch)
    (starts : x.state.slot.toNat ≤ j.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    j = k ∨ Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state)
        (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
      2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) ∨
    HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects ++
      va.hashObjects ++ vb.hashObjects) := by
  classical
  by_cases same : j = k
  · exact .inl same
  rcases terminal_justified_fields (shared.append left) parameters genesis va j fieldA with ga | ha
  · rcases terminal_justified_fields (shared.append right) parameters genesis vb k fieldB with
      gb | hb
    · exact .inl (ga.trans gb.symm)
    · obtain ⟨hb⟩ := hb
      have positive := view_history_positive (shared.append right) parameters genesis hb
      have zero : j.epoch.toNat = 0 := by rw [ga]; rfl
      rw [epoch] at zero
      omega
  · obtain ⟨ha⟩ := ha
    rcases terminal_justified_fields (shared.append right) parameters genesis vb k fieldB with
      gb | hb
    · have positive := view_history_positive (shared.append left) parameters genesis ha
      have zero : k.epoch.toNat = 0 := by rw [gb]; rfl
      rw [← epoch] at zero
      omega
    · obtain ⟨hb⟩ := hb
      let one := ha.calls.getLast ha.nonempty
      let two := hb.calls.getLast hb.nonempty
      have targetA := ha.finish one (List.getLast?_eq_some_getLast ha.nonempty)
      have targetB := hb.finish two (List.getLast?_eq_some_getLast hb.nonempty)
      have overlap := view_same_epoch (shared.append left) (shared.append right)
        parameters genesis earlyA earlyB one two
        (by rw [targetA, targetB]; exact epoch) (by rw [targetA, targetB]; exact same)
      have bound := terminal_pair_bound shared left right parameters genesis starts
        enoughA enoughB terminalA terminalB one two (by rw [targetA])
        (by rw [targetB, ← epoch]) (by rw [targetA]) (by rw [targetB, ← epoch]) overlap
      have first := view_drift shared left parameters j.epoch.toNat j.epoch.toNat starts one
        (by rw [targetA]) (by rw [targetA])
      have second := view_drift shared right parameters j.epoch.toNat j.epoch.toNat starts two
        (by rw [targetB, epoch]) (by rw [targetB, epoch])
      exact .inr (.inl (by omega))

private theorem view_history_crossing {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {view : TerminalView a} {c : Checkpoint}
    (history : ViewHistory run view c) (epoch : Nat)
    (positive : 0 < epoch) (reached : epoch ≤ c.epoch.toNat) :
    ∃ call ∈ history.calls,
      call.source.epoch.toNat < epoch ∧ epoch ≤ call.target.epoch.toNat := by
  have crossing (calls : List (ViewQuorum run view))
      (start : ∀ call, calls.head? = some call → call.source.epoch.toNat < epoch)
      (finish : ∀ call, calls.getLast? = some call → epoch ≤ call.target.epoch.toNat)
      (consecutive : ∀ i one two, calls[i]? = some one → calls[i + 1]? = some two →
        one.target = two.source) (nonempty : calls ≠ []) :
      ∃ call ∈ calls, call.source.epoch.toNat < epoch ∧ epoch ≤ call.target.epoch.toNat := by
    induction calls with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest ih =>
      by_cases crossed : epoch ≤ first.target.epoch.toNat
      · exact ⟨first, by simp, start first rfl, crossed⟩
      · cases rest with
        | nil => exact False.elim (crossed (finish first rfl))
        | cons second tail =>
          have joined := consecutive 0 first second rfl rfl
          obtain ⟨call, member, bounds⟩ := ih
            (by
              intro call head
              simp only [List.head?_cons, Option.some.injEq] at head
              subst call
              rw [← joined]
              omega)
            (by intro call last; apply finish call; simpa using last)
            (by intro i one two hOne hTwo; exact consecutive (i + 1) one two hOne hTwo)
            (by simp)
          exact ⟨call, List.mem_cons_of_mem first member, bounds⟩
  refine crossing history.calls ?_ ?_ history.consecutive history.nonempty
  · intro call head
    rw [history.start call head]
    exact positive
  · intro call last
    rw [history.finish call last]
    exact reached

private theorem view_history_bound {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    {view : TerminalView a} {c : Checkpoint} (history : ViewHistory run view c)
    (call : ViewQuorum run view) (member : call ∈ history.calls) :
    call.target.epoch.toNat ≤ c.epoch.toNat := by
  have bound (calls : List (ViewQuorum run view))
      (finish : ∀ last, calls.getLast? = some last → last.target = c)
      (consecutive : ∀ i one two, calls[i]? = some one → calls[i + 1]? = some two →
        one.target = two.source) :
      ∀ call ∈ calls, call.target.epoch.toNat ≤ c.epoch.toNat := by
    induction calls with
    | nil => simp
    | cons first rest ih =>
      intro call member
      cases rest with
      | nil =>
        have equal := finish first rfl
        have same := List.mem_singleton.mp member
        subst call
        rw [equal]
      | cons second tail =>
        have tailBound := ih (by intro last found; apply finish last; simpa using found)
          (by intro i one two hOne hTwo; exact consecutive (i + 1) one two hOne hTwo)
        rcases List.mem_cons.mp member with same | member
        · subst call
          have joined := consecutive 0 first second rfl rfl
          have secondBound := tailBound second (by simp)
          have forward := UInt64.lt_iff_toNat_lt.mp (view_epochs run parameters genesis second)
          rw [joined]
          omega
        · exact tailBound call member
  exact bound history.calls history.finish history.consecutive call member

/-- A finalized terminal field fixes the earlier path of a later justified terminal field.

The alternatives retain observed drift and concrete hash evidence, not hash injectivity. -/
theorem accountable_terminal_finalized_prefix_gloas {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (va : TerminalView a) (vb : TerminalView b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .hegota) (earlyB : b.fork < .hegota)
    (enoughA : ∀ high, EnoughStake (shared.append left) high)
    (enoughB : ∀ high, EnoughStake (shared.append right) high)
    (terminalA : ∀ high, va.enough high) (terminalB : ∀ high, vb.enough high) (j : Checkpoint)
    (field : j = vb.state.previousJustifiedCheckpoint ∨ j = vb.state.currentJustifiedCheckpoint)
    (ordered : va.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (starts : x.state.slot.toNat ≤
      va.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (shared.append left).checkpointPath va.state.finalizedCheckpoint.epoch =
        (shared.append right).checkpointPath va.state.finalizedCheckpoint.epoch ∨
      Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state)
          (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
        2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects ++
        va.hashObjects ++ vb.hashObjects) := by
  classical
  let f := va.state.finalizedCheckpoint
  by_cases paths : (shared.append left).checkpointPath f.epoch =
      (shared.append right).checkpointPath f.epoch
  · exact .inl paths
  have positive : 0 < f.epoch.toNat := by
    by_contra zero
    have epochZero : f.epoch = 0 := UInt64.toNat_inj.mp (by change f.epoch.toNat = 0; omega)
    exact paths (by rw [epochZero, checkpointPath_zero, checkpointPath_zero])
  have notGenesis : f ≠ ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
    intro equal
    have zero : f.epoch.toNat = 0 := by rw [equal]; rfl
    omega
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  rcases terminal_justified_fields (shared.append right) parameters genesis vb j field with
      initial | history
  · have zero : j.epoch.toNat = 0 := by rw [initial]; rfl
    exact False.elim (by dsimp [f] at positive; omega)
  obtain ⟨history⟩ := history
  obtain ⟨crossing, member, below, above⟩ :=
    view_history_crossing history f.epoch.toNat positive orderedNat
  have upper := view_history_bound (shared.append right) parameters genesis history crossing member
  -- Every conflict witness is charged at its actual selected input state.
  have finish (one : ViewQuorum (shared.append left) va)
      (lower : f.epoch.toNat ≤ one.target.epoch.toNat)
      (upperOne : one.target.epoch.toNat ≤ j.epoch.toNat)
      (overlap : ∀ key ∈ one.voters ∩ crossing.voters,
        Slashable (shared.append left) (shared.append right) key) :
      Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state)
          (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
        2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) := by
    have bound := terminal_pair_bound shared left right parameters genesis starts
      enoughA enoughB terminalA terminalB one crossing lower above upperOne upper overlap
    have first := view_drift shared left parameters f.epoch.toNat j.epoch.toNat starts
      one lower upperOne
    have second := view_drift shared right parameters f.epoch.toNat j.epoch.toNat starts
      crossing above upper
    omega
  have pair (one : ViewQuorum (shared.append left) va)
      (epoch : one.target.epoch = crossing.target.epoch)
      (lower : f.epoch.toNat ≤ one.target.epoch.toNat) :
      Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state)
          (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
        2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects ++
        va.hashObjects ++ vb.hashObjects) := by
    by_cases same : one.target = crossing.target
    · rcases view_quorum_target_binding (shared.append left) (shared.append right)
          parameters genesis one crossing same with bound | hash
      · have earlier : f.epoch ≤ one.target.epoch := UInt64.le_iff_toNat_le.mpr lower
        apply False.elim
        apply paths
        rw [(shared.append left).checkpointPath_restrict f.epoch one.target.epoch earlier,
          (shared.append right).checkpointPath_restrict f.epoch crossing.target.epoch
            (epoch ▸ earlier), bound]
      · exact .inr (hashEvidence_mono (by simp_all) hash)
    · exact .inl (finish one lower (by rw [epoch]; exact upper)
        (view_same_epoch (shared.append left) (shared.append right) parameters genesis
          earlyA earlyB one crossing epoch same))
  obtain initial | ⟨outgoing, source, distance, ⟨fHistory⟩, middle⟩ :=
    terminal_finalized_quorums (shared.append left) parameters genesis va
  · exact False.elim (notGenesis initial)
  by_cases atFinal : crossing.target.epoch = f.epoch
  · let incoming := fHistory.calls.getLast fHistory.nonempty
    have target := fHistory.finish incoming (List.getLast?_eq_some_getLast fHistory.nonempty)
    exact .inr (pair incoming (by rw [target, atFinal]) (by rw [target]))
  have aboveStrict : f.epoch.toNat < crossing.target.epoch.toNat := by
    have different : crossing.target.epoch.toNat ≠ f.epoch.toNat :=
      fun equal => atFinal (UInt64.toNat_inj.mp equal)
    omega
  by_cases beyond : outgoing.target.epoch.toNat < crossing.target.epoch.toNat
  · apply Or.inr
    apply Or.inl
    apply finish outgoing (by rcases distance with one | two <;> dsimp [f] at * <;> omega)
      (by omega)
    intro key member
    obtain ⟨inInner, inOuter⟩ := Finset.mem_inter.mp member
    obtain ⟨d₁, accepted₁, source₁, target₁⟩ :=
      view_attestations (shared.append right) parameters genesis earlyB crossing key inOuter
    obtain ⟨d₂, accepted₂, source₂, target₂⟩ :=
      view_attestations (shared.append left) parameters genesis earlyA outgoing key inInner
    refine ⟨d₁, d₂, .inr accepted₁, .inl accepted₂,
      isSlashableAttestationData_of_surround ?_ ?_⟩
    · rw [source₁, source₂, source]
      exact UInt64.lt_iff_toNat_lt.mpr below
    · rw [target₁, target₂]
      exact UInt64.lt_iff_toNat_lt.mpr beyond
  by_cases sameEpoch : outgoing.target.epoch = crossing.target.epoch
  · exact .inr (pair outgoing sameEpoch (by rw [sameEpoch]; exact above))
  have middleEpoch : crossing.target.epoch.toNat = f.epoch.toNat + 1 := by
    have different : outgoing.target.epoch.toNat ≠ crossing.target.epoch.toNat :=
      fun equal => sameEpoch (UInt64.toNat_inj.mp equal)
    rcases distance with one | two <;> dsimp [f] at * <;> omega
  have gap : outgoing.target.epoch.toNat = f.epoch.toNat + 2 := by
    rcases distance with one | two
    · have same : outgoing.target.epoch = crossing.target.epoch := UInt64.toNat_inj.mp (by
        dsimp [f] at *; omega)
      exact False.elim (sameEpoch same)
    · exact two
  -- A crossing inside a two-epoch finalization link meets its justified middle checkpoint.
  obtain ⟨mid, midEpoch, ⟨midHistory⟩⟩ := middle gap
  let incoming := midHistory.calls.getLast midHistory.nonempty
  have target := midHistory.finish incoming (List.getLast?_eq_some_getLast midHistory.nonempty)
  exact .inr (pair incoming (UInt64.toNat_inj.mp (by rw [target]; dsimp [f] at *; omega))
    (by rw [target]; dsimp [f] at *; omega))

-- The original entry points keep their pre-Gloas contracts.
theorem accountable_terminal_justified_unique {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (va : TerminalView a) (vb : TerminalView b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : ∀ high, EnoughStake (shared.append left) high)
    (enoughB : ∀ high, EnoughStake (shared.append right) high)
    (terminalA : ∀ high, va.enough high) (terminalB : ∀ high, vb.enough high) (j k : Checkpoint)
    (fieldA : j = va.state.previousJustifiedCheckpoint ∨ j = va.state.currentJustifiedCheckpoint)
    (fieldB : k = vb.state.previousJustifiedCheckpoint ∨ k = vb.state.currentJustifiedCheckpoint)
    (epoch : j.epoch = k.epoch)
    (starts : x.state.slot.toNat ≤ j.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    j = k ∨ Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state)
        (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
      2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) ∨
    HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects ++
      va.hashObjects ++ vb.hashObjects) :=
  accountable_terminal_justified_unique_gloas shared left right va vb parameters genesis
    (Nat.lt_trans earlyA (by decide)) (Nat.lt_trans earlyB (by decide))
    enoughA enoughB terminalA terminalB j k fieldA fieldB epoch starts

theorem accountable_terminal_finalized_prefix {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (va : TerminalView a) (vb : TerminalView b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : ∀ high, EnoughStake (shared.append left) high)
    (enoughB : ∀ high, EnoughStake (shared.append right) high)
    (terminalA : ∀ high, va.enough high) (terminalB : ∀ high, vb.enough high) (j : Checkpoint)
    (field : j = vb.state.previousJustifiedCheckpoint ∨ j = vb.state.currentJustifiedCheckpoint)
    (ordered : va.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (starts : x.state.slot.toNat ≤
      va.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (shared.append left).checkpointPath va.state.finalizedCheckpoint.epoch =
        (shared.append right).checkpointPath va.state.finalizedCheckpoint.epoch ∨
      Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state)
          (fullRunAccountableKeys (shared.append left) (shared.append right) x) +
        2 * max (terminalDrift j.epoch.toNat left va) (terminalDrift j.epoch.toNat right vb) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects ++
        va.hashObjects ++ vb.hashObjects) :=
  accountable_terminal_finalized_prefix_gloas shared left right va vb parameters genesis
    (Nat.lt_trans earlyA (by decide)) (Nat.lt_trans earlyB (by decide))
    enoughA enoughB terminalA terminalB j field ordered starts

end EthLib.Consensus.DirectSafety
