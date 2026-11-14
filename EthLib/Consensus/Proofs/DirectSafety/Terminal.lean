module

public import EthLib.Consensus.Proofs.DirectSafety.Drift
public import EthLib.Consensus.Proofs.DirectSafety.Safety

/-!
# A terminal justification projection on a reachable state

The projection runs the concrete justification function once, without advancing the chain.

It introduces no votes and does not assert success of a later slot or epoch transition.

Its witnesses retain successful reads and the checked two-thirds threshold of that function.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

open Classical in
attribute [local instance] propDecidable

/-- Active reference keys with slashable votes or slashing evidence anywhere in either run. -/
noncomputable def fullRunAccountableKeys {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (reference : ForkedBeaconState preset) : Finset BLSPubkey := by
  classical
  exact (activeKeys reference.state).filter fun key =>
    Slashable left right key ∨ left.SlashingEvidence key ∨ right.SlashingEvidence key

private theorem evidence_append {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a) (key : BLSPubkey) :
    (shared.append tail).SlashingEvidence key ↔
      shared.SlashingEvidence key ∨ tail.SlashingEvidence key := by
  constructor
  · rintro ⟨u, v, step, inside, evidence⟩
    rcases (Run.contains_append shared tail step).mp inside with before | after
    · exact .inl ⟨u, v, step, before, evidence⟩
    · exact .inr ⟨u, v, step, after, evidence⟩
  · rintro (⟨u, v, step, inside, evidence⟩ | ⟨u, v, step, inside, evidence⟩)
    · exact ⟨u, v, step, (Run.contains_append shared tail step).mpr (.inl inside), evidence⟩
    · exact ⟨u, v, step, (Run.contains_append shared tail step).mpr (.inr inside), evidence⟩

/-- A Genesis history accounts for the reference keys already slashed before either tail. -/
theorem active_stake_le_fullRunAccountable {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (genesis : Genesis config checks g) (drift : Nat)
    (bound : Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) + drift) :
    Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state)
        (fullRunAccountableKeys (shared.append left) (shared.append right) x) + drift := by
  classical
  let slashed := (activeKeys x.state).filter (SlashedAt x.state)
  have partition : Models.stake (effectiveWeight x.state) (activeKeys x.state) =
      Models.stake (effectiveWeight x.state) (unslashedKeys x.state) +
        Models.stake (effectiveWeight x.state) slashed := by
    simpa only [Models.stake, unslashedKeys, slashed, not_not] using
      (Finset.sum_filter_add_sum_filter_not (activeKeys x.state)
        (fun key => ¬ SlashedAt x.state key) (effectiveWeight x.state)).symm
  have included : accountableKeys shared left right ∪ slashed ⊆
      fullRunAccountableKeys (shared.append left) (shared.append right) x := by
    intro key member
    rcases Finset.mem_union.mp member with accountable | marked
    · obtain ⟨clean, fault⟩ := Finset.mem_filter.mp accountable
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp clean).1, ?_⟩
      rcases fault with conflict | evidence | evidence
      · exact .inl conflict
      · exact .inr (.inl ((evidence_append shared left key).mpr (.inr evidence)))
      · exact .inr (.inr ((evidence_append shared right key).mpr (.inr evidence)))
    · obtain ⟨active, marked⟩ := Finset.mem_filter.mp marked
      refine Finset.mem_filter.mpr ⟨active, .inr (.inl ?_)⟩
      exact (evidence_append shared left key).mpr
        (.inl (shared.slashed_evidence_of_genesis genesis key marked))
  have disjoint : Disjoint (accountableKeys shared left right) slashed := by
    apply Finset.disjoint_left.mpr
    intro key member marked
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
      (Finset.mem_filter.mp marked).2
  have union := Models.stake_mono (w := effectiveWeight x.state) included
  rw [Models.stake, Finset.sum_union disjoint] at union
  dsimp only [Models.stake] at bound partition union ⊢
  omega

/-- Charge the actual terminal input, not a hypothetical future endpoint. -/
noncomputable def terminalDrift {x a : ForkedBeaconState preset}
    (high : Nat) (tail : Run config checks x a) (view : TerminalView a) : Nat :=
  match view with
  | .realized => derivedDrift high tail
  | .pulled _ _ => max (derivedDrift high tail)
      (2 * (∑ key ∈ (activeKeys x.state).filter (¬ SlashedAt a.state ·),
        (effectiveWeight x.state key - Models.supported (recentKeys a.state)
          (effectiveWeight a.state) key)) +
      (∑ key ∈ recentKeys a.state,
        (effectiveWeight a.state key - Models.supported (activeKeys x.state)
          (effectiveWeight x.state) key)) + 2 * boundaryStake a)

/-- Persistence identifies the pulled full-active budget with master's drift. -/
theorem terminalDrift_pulled {x a : ForkedBeaconState preset}
    (high : Nat) (tail : Run config checks x a) {after : BeaconState preset a.fork}
    (ok : processJustificationAndFinalization a.state = .ok after) :
    terminalDrift high tail (.pulled after ok) =
      max (derivedDrift high tail) (stateDrift x a) := by
  unfold terminalDrift
  rw [stateDrift_eq_of_run tail]

def TerminalView.hashObjects {a : ForkedBeaconState preset}
    (view : TerminalView a) : List (HashObject preset) :=
  match view with
  | .realized => []
  | .pulled after _ => [.state a, .header a.state.latestBlockHeader,
      .state ⟨a.fork, after⟩, .header after.latestBlockHeader]

structure ViewHistory {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (view : TerminalView a) (checkpoint : Checkpoint) where
  calls : List (ViewQuorum run view)
  nonempty : calls ≠ []
  start : ∀ c, calls.head? = some c → c.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  finish : ∀ c, calls.getLast? = some c → c.target = checkpoint
  consecutive : ∀ i left right, calls[i]? = some left → calls[i + 1]? = some right →
    left.target = right.source

end EthLib.Consensus.DirectSafety
