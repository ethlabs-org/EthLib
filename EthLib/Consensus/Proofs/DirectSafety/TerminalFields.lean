module

public import EthLib.Consensus.Proofs.DirectSafety.Terminal
import all EthLib.Consensus.Proofs.DirectSafety.Fields
import all EthLib.Consensus.Proofs.DirectSafety.Hashes

/-!
# Checkpoint histories after a terminal projection

Historical counts remain attached to the real run.

The optional projection contributes only its own successful counts.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private def lift_history {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (view : TerminalView a) {j : Checkpoint} (history : JustificationHistory run j) :
    ViewHistory run view j where
  calls := history.calls.map Sum.inl
  nonempty := by simpa using history.nonempty
  start := by
    intro call found
    simp only [List.head?_map, Option.map_eq_some_iff] at found
    obtain ⟨old, first, rfl⟩ := found
    exact history.start old first
  finish := by
    intro call found
    simp only [List.getLast?_map, Option.map_eq_some_iff] at found
    obtain ⟨old, last, rfl⟩ := found
    exact history.finish old last
  consecutive := by
    intro i left right one two
    simp only [List.getElem?_map, Option.map_eq_some_iff] at one two
    obtain ⟨oldLeft, one, rfl⟩ := one
    obtain ⟨oldRight, two, rfl⟩ := two
    exact history.consecutive i oldLeft oldRight one two

private theorem view_history_of_call {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {view : TerminalView a} (call : ViewQuorum run view)
    (source : call.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (ViewHistory run view call.source)) :
    Nonempty (ViewHistory run view call.target) := by
  rcases source with initial | history
  · refine ⟨⟨[call], by simp, ?_, ?_, ?_⟩⟩
    · intro c found
      simpa using (Option.some.inj found ▸ initial)
    · intro c found
      simpa using (Option.some.inj found ▸ (rfl : call.target = call.target))
    · intro i left right one two
      simp at two
  · obtain ⟨history⟩ := history
    refine ⟨⟨history.calls ++ [call], by simp, ?_, ?_, ?_⟩⟩
    · intro c first
      have eq : (history.calls ++ [call]).head? = history.calls.head? := by
        cases h : history.calls with
        | nil => exact False.elim (history.nonempty h)
        | cons x xs => rfl
      exact history.start c (eq ▸ first)
    · intro c last
      simpa using (show call = c from by simpa using last) ▸
        (rfl : call.target = call.target)
    · intro i left right one two
      by_cases lt : i + 1 < history.calls.length
      · exact history.consecutive i left right
          (by simpa [List.getElem?_append, show i < history.calls.length by omega] using one)
          (by simpa [List.getElem?_append, lt] using two)
      · have bound := (List.getElem?_eq_some_iff.mp one).1
        have nextBound := (List.getElem?_eq_some_iff.mp two).1
        simp only [List.length_append, List.length_singleton] at bound nextBound
        have lastIndex : i + 1 = history.calls.length := by omega
        have rightEq : right = call := by
          simpa [List.getElem?_append, lastIndex] using two.symm
        subst right
        apply history.finish left
        rw [List.getLast?_eq_getElem?]
        have small : i < history.calls.length := by omega
        have indexEq : history.calls.length - 1 = i := by omega
        simpa [List.getElem?_append, small, indexEq] using one

private theorem terminal_balances {a : ForkedBeaconState preset}
    {after : BeaconState preset a.fork}
    (ok : processJustificationAndFinalization a.state = .ok after)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state) :
    ∃ (previous current : List ValidatorIndex) (total pb cb : Gwei),
      targetIndices a.state (getPreviousEpoch a.state) = .ok previous ∧
      targetIndices a.state (getCurrentEpoch a.state) = .ok current ∧
      getTotalActiveBalance a.state = .ok total ∧
      getTotalBalance a.state previous = .ok pb ∧
      getTotalBalance a.state current = .ok cb ∧
      weighJustificationAndFinalization a.state total pb cb = .ok after := by
  have late := UInt64.not_le.mpr later
  unfold processJustificationAndFinalization at ok
  split at ok
  · rename_i altair
    simp only [processJustificationAndFinalizationAltair, ite_eq_right late,
      bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      pb, pbOk, cb, cbOk, weighed⟩ := ok
    exact ⟨previous, current, total, pb, cb,
      by simpa [targetIndices, altair, liftAccessor_ok] using previousOk,
      by simpa [targetIndices, altair, liftAccessor_ok] using currentOk,
      totalOk, pbOk, cbOk, weighed⟩
  · rename_i notAltair
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at ok
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      pb, ⟨pi, piOk, pbOk⟩, cb, ⟨ci, ciOk, cbOk⟩, weighed⟩ := ok
    refine ⟨pi, ci, total, pb, cb, ?_, ?_, totalOk, pbOk, cbOk, weighed⟩
    · simp [targetIndices, notAltair, bind_ok_iff, liftAccessor_ok]
      exact ⟨_, previousOk, piOk⟩
    · simp [targetIndices, notAltair, bind_ok_iff, liftAccessor_ok]
      exact ⟨_, currentOk, ciOk⟩

private theorem terminal_current {a : ForkedBeaconState preset}
    {after : BeaconState preset a.fork}
    (ok : processJustificationAndFinalization a.state = .ok after)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state) :
    after.currentJustifiedCheckpoint = a.state.currentJustifiedCheckpoint ∨
      ∃ quorum : TerminalQuorum (.pulled after ok),
        quorum.target = after.currentJustifiedCheckpoint ∧
        (quorum.source = a.state.previousJustifiedCheckpoint ∨
          quorum.source = a.state.currentJustifiedCheckpoint) := by
  obtain ⟨previous, current, total, pb, cb, previousOk, currentOk, totalOk, pbOk, cbOk,
    weighed⟩ := terminal_balances ok later
  rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, _⟩ |
    ⟨now, threshold, weighted, thresholdOk, weightedOk, passes, epoch, root⟩
  · exact .inl same
  · right
    refine ⟨{ after := after, projected := ok, selected := rfl, later := later
              current := now
              target := after.currentJustifiedCheckpoint
              targetEpoch := epoch
              targetRoot := root
              indices := if now then current else previous
              counted := ?_
              passes := ⟨total, if now then cb else pb, threshold, weighted,
                totalOk, ?_, thresholdOk, weightedOk, passes⟩ }, rfl, ?_⟩
    · rw [epoch]; cases now <;> assumption
    · cases now <;> assumption
    · cases now <;> simp [TerminalQuorum.source]

/-- Projected justified fields retain the real history, with at most one terminal count. -/
theorem terminal_justified_fields {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (j : Checkpoint)
    (field : j = view.state.previousJustifiedCheckpoint ∨
      j = view.state.currentJustifiedCheckpoint) :
    j = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ Nonempty (ViewHistory run view j) := by
  have old (view : TerminalView a) (j : Checkpoint)
      (field : j = a.state.previousJustifiedCheckpoint ∨
        j = a.state.currentJustifiedCheckpoint) :
      j = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ Nonempty (ViewHistory run view j) := by
    rcases justified_fields run parameters genesis j field with initial | history
    · exact .inl initial
    · obtain ⟨history⟩ := history
      exact .inr ⟨lift_history view history⟩
  cases view with
  | realized => exact old _ j field
  | pulled after ok =>
    change j = after.previousJustifiedCheckpoint ∨ j = after.currentJustifiedCheckpoint at field
    rcases justification_split ok with ⟨_, rfl⟩ | ⟨later, total, pb, cb, weighed⟩
    · exact old _ j field
    · rcases field with previous | current
      · exact old _ j (.inr
          (previous.trans (weighJustificationAndFinalization_checkpoints weighed).1))
      · rcases terminal_current ok later with same | ⟨quorum, target, source⟩
        · exact old _ j (.inr (current.trans same))
        · have history := view_history_of_call (run := run) (Sum.inr quorum)
            (old _ quorum.source source)
          exact .inr ((target.trans current.symm) ▸ history)

private theorem terminal_new_bits {a : ForkedBeaconState preset}
    {after : BeaconState preset a.fork}
    (ok : processJustificationAndFinalization a.state = .ok after)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state) :
    (after.justificationBits.bits[0] = true →
      ∃ quorum : TerminalQuorum (.pulled after ok),
        quorum.source = a.state.currentJustifiedCheckpoint ∧
        quorum.target = after.currentJustifiedCheckpoint ∧
        quorum.target.epoch = getCurrentEpoch a.state) ∧
    (after.justificationBits.bits[1] = true →
      (∃ quorum : TerminalQuorum (.pulled after ok),
        quorum.source = a.state.previousJustifiedCheckpoint ∧
        quorum.target.epoch = getPreviousEpoch a.state) ∨
      a.state.justificationBits.bits[0] = true) := by
  obtain ⟨previous, current, total, pb, cb, previousOk, currentOk, totalOk, pbOk, cbOk,
    weighed⟩ := terminal_balances ok later
  obtain ⟨threshold, pw, cw, thresholdOk, pwOk, cwOk, zero, one, _⟩ :=
    weighJustificationAndFinalization_bits weighed
  constructor
  · intro set
    obtain ⟨passes, root, rootOk, target⟩ := zero set
    refine ⟨{ after := after, projected := ok, selected := rfl, later := later
              current := true
              target := ⟨getCurrentEpoch a.state, root⟩
              targetEpoch := rfl, targetRoot := rootOk
              indices := current, counted := currentOk
              passes := ⟨total, cb, threshold, cw, totalOk, cbOk, thresholdOk, cwOk, passes⟩ },
      rfl, target.symm, rfl⟩
  · intro set
    rcases one set with ⟨passes, root, rootOk⟩ | old
    · refine .inl ⟨{ after := after, projected := ok, selected := rfl, later := later
                     current := false
                     target := ⟨getPreviousEpoch a.state, root⟩
                     targetEpoch := rfl, targetRoot := rootOk
                     indices := previous, counted := previousOk
                     passes := ⟨total, pb, threshold, pw, totalOk, pbOk, thresholdOk, pwOk,
                       passes⟩ }, rfl, rfl⟩
    · exact .inr old

private theorem terminal_source_history {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    {view : TerminalView a} (call : ViewQuorum run view) :
    call.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (ViewHistory run view call.source) := by
  have lift {j} (h : j = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run j)) :
      j = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ Nonempty (ViewHistory run view j) := by
    rcases h with initial | history
    · exact .inl initial
    · obtain ⟨history⟩ := history
      exact .inr ⟨lift_history view history⟩
  cases call with
  | inl call => exact lift (quorum_source_history run parameters genesis call)
  | inr call =>
    apply lift (justified_fields run parameters genesis call.source _)
    cases h : call.current <;> simp [TerminalQuorum.source, h]

private theorem terminal_bit_history {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    {after : BeaconState preset a.fork}
    (ok : processJustificationAndFinalization a.state = .ok after)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state)
    (i : Fin 4) (set : after.justificationBits.bits[i] = true) :
    ∃ j : Checkpoint, j.epoch.toNat + i.val = (getCurrentEpoch a.state).toNat ∧
      Nonempty (ViewHistory run (.pulled after ok) j) := by
  have finish (call : ViewQuorum run (.pulled after ok))
      (date : call.target.epoch.toNat + i.val = (getCurrentEpoch a.state).toNat) :
      ∃ j : Checkpoint, j.epoch.toNat + i.val = (getCurrentEpoch a.state).toNat ∧
        Nonempty (ViewHistory run (.pulled after ok) j) :=
    ⟨call.target, date, view_history_of_call call
      (terminal_source_history run parameters genesis call)⟩
  have old (k : Fin 4) (shift : k.val + 1 = i.val)
      (set : a.state.justificationBits.bits[k] = true) :
      ∃ j : Checkpoint, j.epoch.toNat + i.val = (getCurrentEpoch a.state).toNat ∧
        Nonempty (ViewHistory run (.pulled after ok) j) := by
    obtain ⟨call, date⟩ := run_bits run genesis k set
    exact finish (Sum.inl call) (by change call.target.epoch.toNat + i.val = _; omega)
  fin_cases i
  · obtain ⟨call, _, _, date⟩ := (terminal_new_bits ok later).1 set
    exact finish (Sum.inr call) (by simp [ViewQuorum.target, date])
  · rcases (terminal_new_bits ok later).2 set with ⟨call, _, date⟩ | previous
    · have prev := getPreviousEpoch_toNat a.state
      have late := UInt64.lt_iff_toNat_lt.mp later
      simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
      apply finish (Sum.inr call)
      change call.target.epoch.toNat + 1 = _
      rw [date]; omega
    · exact old 0 rfl previous
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, weighed⟩ := terminal_balances ok later
    obtain ⟨_, _, _, _, _, _, _, _, two, _⟩ :=
      weighJustificationAndFinalization_bits weighed
    exact old 1 rfl (two ▸ set)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, weighed⟩ := terminal_balances ok later
    simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at weighed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, eq⟩ := weighed
    rw [← eq] at set
    exact old 2 rfl (by simpa [shiftJustificationBits] using set)

private theorem terminal_rule {fork : Fork} {state after : BeaconState preset fork}
    {total previous current : Gwei}
    (ok : weighJustificationAndFinalization state total previous current = .ok after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint ∨
      let c := after.finalizedCheckpoint
      let bits := after.justificationBits.bits
      let e := (getCurrentEpoch state).toNat
      (c = state.previousJustifiedCheckpoint ∧
        ((bits[1] = true ∧ bits[2] = true ∧ bits[3] = true ∧ c.epoch.toNat + 3 = e) ∨
          (bits[1] = true ∧ bits[2] = true ∧ c.epoch.toNat + 2 = e))) ∨
      (c = state.currentJustifiedCheckpoint ∧
        ((bits[0] = true ∧ bits[1] = true ∧ bits[2] = true ∧ c.epoch.toNat + 2 = e) ∨
          (bits[0] = true ∧ bits[1] = true ∧ c.epoch.toNat + 1 = e))) := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, b₃, h₃, b₂, h₂, c₂, hc₂, c₁, hc₁, eq⟩ := ok
  rw [← eq]
  dsimp only
  split
  · rename_i yes
    right
    right
    refine ⟨rfl, ?_⟩
    simp only [Bool.or_eq_true] at yes
    rcases yes with yes | yes
    · rw [yes] at hc₂
      have rule := finalizes_eq_true hc₂
      simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
      exact .inl ⟨rule.1.1.1, rule.1.1.2, rule.1.2, rule.2⟩
    · rw [yes] at hc₁
      have rule := finalizes_eq_true hc₁
      simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
      exact .inr ⟨rule.1.1, rule.1.2, rule.2⟩
  · split
    · rename_i yes
      right
      left
      refine ⟨rfl, ?_⟩
      simp only [Bool.or_eq_true] at yes
      rcases yes with yes | yes
      · rw [yes] at h₃
        have rule := finalizes_eq_true h₃
        simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
        exact .inl ⟨rule.1.1.1, rule.1.1.2, rule.1.2, rule.2⟩
      · rw [yes] at h₂
        have rule := finalizes_eq_true h₂
        simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
        exact .inr ⟨rule.1.1, rule.1.2, rule.2⟩
    · exact .inl rfl

/-- Each non-genesis finalized field has an outgoing count and the required middle history. -/
theorem terminal_finalized_quorums {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g) (view : TerminalView a) :
    let f := view.state.finalizedCheckpoint
    f = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      ∃ outgoing : ViewQuorum run view, outgoing.source = f ∧
        (outgoing.target.epoch.toNat = f.epoch.toNat + 1 ∨
          outgoing.target.epoch.toNat = f.epoch.toNat + 2) ∧
        Nonempty (ViewHistory run view f) ∧
        (outgoing.target.epoch.toNat = f.epoch.toNat + 2 →
          ∃ middle : Checkpoint, middle.epoch.toNat = f.epoch.toNat + 1 ∧
            Nonempty (ViewHistory run view middle)) := by
  have old (view : TerminalView a) (same : view.state.finalizedCheckpoint =
      a.state.finalizedCheckpoint) :
      view.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        ∃ outgoing : ViewQuorum run view, outgoing.source = view.state.finalizedCheckpoint ∧
          (outgoing.target.epoch.toNat = view.state.finalizedCheckpoint.epoch.toNat + 1 ∨
            outgoing.target.epoch.toNat = view.state.finalizedCheckpoint.epoch.toNat + 2) ∧
          Nonempty (ViewHistory run view view.state.finalizedCheckpoint) ∧
          (outgoing.target.epoch.toNat = view.state.finalizedCheckpoint.epoch.toNat + 2 →
            ∃ middle : Checkpoint,
              middle.epoch.toNat = view.state.finalizedCheckpoint.epoch.toNat + 1 ∧
              Nonempty (ViewHistory run view middle)) := by
    rw [same]
    rcases finalized_field run genesis with initial | ⟨call, _, rule⟩
    · exact .inl initial
    · obtain ⟨outgoing, source, gap, history, middle⟩ :=
        finalization_rule_quorums run parameters genesis call _ rule
      rcases history with initial | history
      · exact .inl initial
      · obtain ⟨history⟩ := history
        refine .inr ⟨Sum.inl outgoing, source, gap, ⟨lift_history view history⟩, ?_⟩
        intro two
        obtain ⟨middle, date, history⟩ := middle two
        obtain ⟨history⟩ := history
        exact ⟨middle, date, ⟨lift_history view history⟩⟩
  cases view with
  | realized => exact old _ rfl
  | pulled after ok =>
    rcases justification_split ok with ⟨_, rfl⟩ | ⟨later, total, pb, cb, weighed⟩
    · exact old _ rfl
    · rcases terminal_rule weighed with same | rule
      · exact old _ same
      · have finish (outgoing : ViewQuorum run (.pulled after ok))
            (source : outgoing.source = after.finalizedCheckpoint)
            (gap : outgoing.target.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 1 ∨
              outgoing.target.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 2)
            (middle : outgoing.target.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 2 →
              ∃ middle : Checkpoint,
                middle.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 1 ∧
                Nonempty (ViewHistory run (.pulled after ok) middle)) :
            after.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
              ∃ outgoing : ViewQuorum run (.pulled after ok),
                outgoing.source = after.finalizedCheckpoint ∧
                (outgoing.target.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 1 ∨
                  outgoing.target.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 2) ∧
                Nonempty (ViewHistory run (.pulled after ok) after.finalizedCheckpoint) ∧
                (outgoing.target.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 2 →
                  ∃ middle : Checkpoint,
                    middle.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 1 ∧
                    Nonempty (ViewHistory run (.pulled after ok) middle)) := by
          rcases terminal_source_history run parameters genesis outgoing with initial | history
          · exact .inl (source.symm.trans initial)
          · exact .inr ⟨outgoing, source, gap, source ▸ history, middle⟩
        have middle (i : Fin 4) (set : after.justificationBits.bits[i] = true)
            (date : after.finalizedCheckpoint.epoch.toNat + 1 + i.val =
              (getCurrentEpoch a.state).toNat) :
            ∃ middle : Checkpoint,
              middle.epoch.toNat = after.finalizedCheckpoint.epoch.toNat + 1 ∧
              Nonempty (ViewHistory run (.pulled after ok) middle) := by
          obtain ⟨j, epoch, history⟩ := terminal_bit_history run parameters genesis ok later i set
          exact ⟨j, by omega, history⟩
        have previous (set : after.justificationBits.bits[1] = true) :
            ∃ outgoing : ViewQuorum run (.pulled after ok),
              outgoing.source = a.state.previousJustifiedCheckpoint ∧
              outgoing.target.epoch.toNat + 1 = (getCurrentEpoch a.state).toNat := by
          rcases (terminal_new_bits ok later).2 set with ⟨call, source, epoch⟩ | old
          · have prev := getPreviousEpoch_toNat a.state
            have late := UInt64.lt_iff_toNat_lt.mp later
            simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
            refine ⟨Sum.inr call, source, ?_⟩
            change call.target.epoch.toNat + 1 = _
            rw [epoch]; omega
          · obtain ⟨call, source, _, date⟩ := run_zero run genesis old
            exact ⟨Sum.inl call, source, date⟩
        rcases rule with ⟨source, three | two⟩ | ⟨source, two | one⟩
        · obtain ⟨outgoing, start, date⟩ := previous three.1
          exact finish outgoing (start.trans source.symm) (.inr (by omega))
            (fun _ => middle 2 three.2.1 (by omega))
        · obtain ⟨outgoing, start, date⟩ := previous two.1
          exact finish outgoing (start.trans source.symm) (.inl (by omega))
            (fun gap => False.elim (by omega))
        · obtain ⟨outgoing, start, _, date⟩ := (terminal_new_bits ok later).1 two.1
          have dateNat := congrArg UInt64.toNat date
          exact finish (Sum.inr outgoing) (start.trans source.symm) (.inr (by
            change outgoing.target.epoch.toNat = _; omega))
            (fun _ => middle 1 two.2.1 (by omega))
        · obtain ⟨outgoing, start, _, date⟩ := (terminal_new_bits ok later).1 one.1
          have dateNat := congrArg UInt64.toNat date
          exact finish (Sum.inr outgoing) (start.trans source.symm) (.inl (by
            change outgoing.target.epoch.toNat = _; omega))
            (fun gap => False.elim (by change outgoing.target.epoch.toNat = _ at gap; omega))

private theorem view_target_prefix {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset)
    (view : TerminalView a) (call : ViewQuorum run view) :
    ∃ (b : ForkedBeaconState preset) (pre : Run config checks g b),
      getBlockRoot b.state call.target.epoch = .ok call.target.root ∧
      run.checkpointPath call.target.epoch = pre.checkpointPath call.target.epoch ∧
      pre.hashObjects ⊆ run.hashObjects := by
  cases call with
  | inr call => exact ⟨a, run, call.targetRoot, rfl, fun _ h => h⟩
  | inl call =>
    -- The cached root is already in the real input ring, before this epoch call.
    obtain ⟨early, recent⟩ := call_target_window parameters call
    have read := call.targetRoot
    rw [getBlockRoot_processSlot call.cachedOk recent] at read
    obtain ⟨pre, post, same⟩ := run.contains_split (.slot call.advanced) call.member
    refine ⟨call.before, pre, read, ?_, ?_⟩
    · have stable := path_append_stable pre
        ((Run.nil.snoc (.slot call.advanced)).append post) call.target.epoch early
      have assoc : pre.append ((Run.nil.snoc (.slot call.advanced)).append post) =
          (pre.snoc (.slot call.advanced)).append post :=
        append_slot_tail pre (.slot call.advanced) post
      change run.checkpointPath call.target.epoch = _
      rw [assoc, ← same] at stable
      exact stable
    · intro object member
      have included := hashObjects_append_subset (pre.snoc (.slot call.advanced)) post
        (List.mem_append_left _ member)
      exact (congrArg Run.hashObjects same).symm ▸ included

/-- Equal targets bind the selected real paths, retaining collision and zero-root evidence. -/
theorem view_quorum_target_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (va : TerminalView a) (vb : TerminalView b)
    (one : ViewQuorum left va) (two : ViewQuorum right vb) (same : one.target = two.target) :
    left.checkpointPath one.target.epoch = right.checkpointPath two.target.epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects ++ va.hashObjects ++ vb.hashObjects) := by
  obtain ⟨a', preA, readA, pathA, objectsA⟩ := view_target_prefix left parameters va one
  obtain ⟨b', preB, readB, pathB, objectsB⟩ := view_target_prefix right parameters vb two
  rcases checkpoint_binding preA preB parameters genesis one.target.epoch one.target.root
      readA (by simpa [same] using readB) with paths | evidence
  · exact .inl (pathA.trans (paths.trans (by simpa [same] using pathB.symm)))
  · right
    apply hashEvidence_mono (one := preA.hashObjects ++ preB.hashObjects) _ evidence
    intro object member
    apply List.mem_append_left
    apply List.mem_append_left
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (objectsA member)
    · exact List.mem_append_right _ (objectsB member)

end EthLib.Consensus.DirectSafety
