module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds

/-!
# Direct accountable safety from selected executions

All checkpoints are the fields of the endpoints of actual executions.

All attestation witnesses come from the supplied shared prefix or one of its two tails.

The bounds use observed effective-weight drift and retain explicit hash-evidence alternatives.

Closed-form source bounds are separate obligations, not premises of these proofs.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable def accountableKeys {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (reference : ForkedBeaconState preset) : Finset BLSPubkey := by
  classical
  exact (activeKeys reference.state).filter (Accountable left right)

/-- Retain the two witness costs instead of replacing both by the larger branch budget. -/
theorem accountable_safety_at_calls {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint ∨
      j = b.state.finalizedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j) :
    (∃ one two : EitherCall (shared.append left) (shared.append right),
      a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
      a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
      Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
        3 * Quorum.weight (effectiveWeight x.state)
          (accountableKeys (shared.append left) (shared.append right) x) +
        stateDrift x one.state + stateDrift x two.state) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  classical
  -- Transfer both quorum denominators together, rather than bounding the union stake alone.
  rcases conflicting_fields_quorums (shared.append left) (shared.append right)
    parameters genesis earlyA earlyB j field ordered conflict with witnesses | hashes
  · obtain ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, overlap⟩ := witnesses
    let bad := (activeKeys x.state).filter (Accountable (shared.append left) (shared.append right))
    have facts (call : EitherCall (shared.append left) (shared.append right)) :
        call.voters ⊆ recentKeys call.state.state ∧
        2 * Quorum.weight (effectiveWeight call.state.state) (activeKeys call.state.state) ≤
          3 * Quorum.weight (effectiveWeight call.state.state) call.voters ∧
        (∑ k ∈ activeKeys x.state \ bad,
          (effectiveWeight x.state k - Quorum.supported (recentKeys call.state.state)
            (effectiveWeight call.state.state) k)) ≤ referenceLoss x call.state := by
      have branch {z : ForkedBeaconState preset} (run : Run config checks g z)
          (early : z.fork < .glamsterdam) (enough : EnoughStake run)
          (included : ∀ k, run.SlashingEvidence k →
            Accountable (shared.append left) (shared.append right) k)
          (c : QuorumCall run) :
          c.voters ⊆ recentKeys c.cached ∧
          2 * Quorum.weight (effectiveWeight c.cached) (activeKeys c.cached) ≤
            3 * Quorum.weight (effectiveWeight c.cached) c.voters ∧
          (∑ k ∈ activeKeys x.state \ bad,
            (effectiveWeight x.state k - Quorum.supported (recentKeys c.cached)
              (effectiveWeight c.cached) k)) ≤ referenceLoss x ⟨c.before.fork, c.cached⟩ := by
        refine ⟨quorum_voters_recent run parameters genesis early c,
          quorum_count run genesis enough c, ?_⟩
        obtain ⟨pre, post, split, frame, validators, balances⟩ := c.toEpochCall.selected_prefix
        have earlyBefore : c.before.fork < .glamsterdam :=
          Nat.lt_of_le_of_lt (fork_le_of_chainSteps
            ((Run.nil.snoc (.slot c.advanced)).append post).chainSteps) early
        unfold referenceLoss
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨active, absent⟩ := Finset.mem_sdiff.mp hk
          refine Finset.mem_filter.mpr ⟨active, ?_⟩
          rintro ⟨v, found, key, slashed⟩
          have evidence := pre.slashed_evidence genesis earlyBefore v
            (by simpa only [validators] using found) slashed
          have all : run.SlashingEvidence v.pubkey := by
            obtain ⟨u, v, step, inside, ev⟩ := evidence
            refine ⟨u, v, step, ?_, ev⟩
            rw [split]
            exact ((pre.snoc (.slot c.advanced)).contains_append post step).mpr
              (.inl (.earlier inside _))
          exact absent (Finset.mem_filter.mpr ⟨active, key ▸ included _ all⟩)
        · intros; exact Nat.zero_le _
      cases call with
      | inl c => exact branch _ earlyA enoughA (fun _ h => .inr (.inl h)) c
      | inr c => exact branch _ earlyB enoughB (fun _ h => .inr (.inr h)) c
    obtain ⟨recentOne, quorumOne, lossOne⟩ := facts one
    obtain ⟨recentTwo, quorumTwo, lossTwo⟩ := facts two
    -- Include overlap outside the reference set; it contributes no reference weight.
    let accountable := bad ∪ (one.voters ∩ two.voters)
    have outsideLoss (c : EitherCall (shared.append left) (shared.append right))
        (bound : (∑ k ∈ activeKeys x.state \ bad,
          (effectiveWeight x.state k - Quorum.supported (recentKeys c.state.state)
            (effectiveWeight c.state.state) k)) ≤ referenceLoss x c.state) :
        (∑ k ∈ activeKeys x.state \ accountable,
          (effectiveWeight x.state k - Quorum.supported (recentKeys c.state.state)
            (effectiveWeight c.state.state) k)) ≤ referenceLoss x c.state := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; omega)) bound
      exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left
    have same : activeKeys x.state ∩ accountable = bad := by
      ext k
      simp only [accountable, bad, Finset.mem_inter, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨active, h | h⟩
        · exact h
        · exact ⟨active, .inl (overlap k (Finset.mem_inter.mpr h))⟩
      · intro h; exact ⟨h.1, .inl h⟩
    have bound := Quorum.accountable_at_reference (activeKeys x.state)
      (activeKeys one.state.state) (activeKeys two.state.state)
      (recentKeys one.state.state) (recentKeys two.state.state) one.voters two.voters
      accountable (effectiveWeight x.state) (effectiveWeight one.state.state)
      (effectiveWeight two.state.state) (referenceLoss x one.state) (referenceLoss x two.state)
      (referenceGain x one.state) (referenceGain x two.state)
      (boundaryStake one.state) (boundaryStake two.state)
      Finset.subset_union_left Finset.subset_union_left recentOne recentTwo quorumOne quorumTwo
      Finset.subset_union_right (outsideLoss one lossOne) (outsideLoss two lossTwo)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    rw [same] at bound
    refine .inl ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, ?_⟩
    change _ ≤ 3 * Quorum.weight (effectiveWeight x.state) bad +
      stateDrift x one.state + stateDrift x two.state
    dsimp only [stateDrift]
    omega
  · exact .inr hashes

private theorem selected_call_drift_le {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (parameters : Parameters preset) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail))
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high) :
    stateDrift x ⟨call.before.fork, call.cached⟩ ≤ derivedDrift high tail := by
  have member := call_after_reference shared tail parameters low starts call lower
  obtain ⟨pre, post, split⟩ := tail.contains_split (.slot call.advanced) member
  let before := call.before
  -- The budget observes the state before caching, whose slot and registry caching preserves.
  obtain ⟨_, _, _, frame, validators, _⟩ := call.toEpochCall.selected_prefix
  have epoch : (getCurrentEpoch before.state).toNat ≤ high + 1 := by
    have target : (getCurrentEpoch call.cached).toNat ≤ call.target.epoch.toNat + 1 := by
      rw [call.targetEpoch]
      cases call.current <;> simp [getPreviousEpoch_toNat]
      omega
    have same : getCurrentEpoch call.cached = getCurrentEpoch before.state := by
      simp only [getCurrentEpoch, frame.slot, before]
    rw [same] at target
    omega
  have observed {z : ForkedBeaconState preset} (run : Run config checks x z)
      (bounded : (getCurrentEpoch z.state).toNat ≤ high + 1) :
      stateDrift x z ≤ derivedDrift high run := by
    cases run with
    | nil => exact Nat.le_refl _
    | snoc pre step =>
      simp only [derivedDrift, ite_eq_left bounded]; exact Nat.le_max_right _ _
  have mono {u v : ForkedBeaconState preset} (pre : Run config checks x u)
      (post : Run config checks u v) :
      derivedDrift high pre ≤ derivedDrift high (pre.append post) := by
    induction post with
    | nil => exact Nat.le_refl _
    | snoc post step ih =>
      simp only [Run.append, derivedDrift]
      split
      · exact ih.trans (Nat.le_max_left _ _)
      · exact ih
  have next : derivedDrift high pre ≤ derivedDrift high (pre.snoc (.slot call.advanced)) := by
    simp only [derivedDrift]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  have same : stateDrift x ⟨call.before.fork, call.cached⟩ = stateDrift x before := by
    have weight : effectiveWeight call.cached = effectiveWeight before.state := by
      funext k
      simp only [effectiveWeight, validators, before]
    simp only [stateDrift, referenceLoss, referenceGain, boundaryStake, weight, recentKeys,
      activeKeys, keysAt, getActiveValidatorIndices, getPreviousEpoch,
      getCurrentEpoch, validators, frame.slot, before]
    rfl
  rw [same]
  have result := (observed pre epoch).trans (next.trans (mono _ post))
  simpa only [← split] using result

/-- Order the finalized fields by epoch, with weights measured at their shared state. -/
theorem accountable_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint)
    (starts : x.state.slot.toNat ≤
      min a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat *
        preset.SLOTS_PER_EPOCH.toNat) :
    let high := max a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat
    (Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Quorum.weight (effectiveWeight x.state)
        (accountableKeys (shared.append left) (shared.append right) x) +
        2 * max (derivedDrift high left) (derivedDrift high right)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  dsimp only
  have _ := caps
  have _ := aligned
  have _ := withdrawalDelay
  rcases accountable_safety_at_calls shared left right parameters genesis earlyA earlyB
    enoughA enoughB b.state.finalizedCheckpoint (.inr (.inr rfl)) ordered conflict with
    witnesses | hashes
  · obtain ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, bound⟩ := witnesses
    let high := max a.state.finalizedCheckpoint.epoch.toNat b.state.finalizedCheckpoint.epoch.toNat
    have start : x.state.slot.toNat ≤
        a.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
      starts.trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _))
    have budget (c : EitherCall (shared.append left) (shared.append right))
        (lower : a.state.finalizedCheckpoint.epoch.toNat ≤ c.targetEpoch)
        (upper : c.targetEpoch ≤ b.state.finalizedCheckpoint.epoch.toNat) :
        stateDrift x c.state ≤ max (derivedDrift high left) (derivedDrift high right) := by
      have upperHigh : c.targetEpoch ≤ high := upper.trans (Nat.le_max_right _ _)
      cases c with
      | inl c => exact (selected_call_drift_le shared left parameters _ high start c lower
          upperHigh).trans (Nat.le_max_left _ _)
      | inr c => exact (selected_call_drift_le shared right parameters _ high start c lower
          upperHigh).trans (Nat.le_max_right _ _)
    have first := budget one lowerOne upperOne
    have second := budget two lowerTwo upperTwo
    exact .inl (by dsimp only [high] at first second; omega)
  · exact .inr hashes

/-- A finalized field versus either justified field at an equal or later epoch. -/
theorem accountable_safety_justified {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (enoughA : EnoughStake (shared.append left)) (enoughB : EnoughStake (shared.append right))
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j)
    (starts : x.state.slot.toNat ≤
      a.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
      3 * Quorum.weight (effectiveWeight x.state)
        (accountableKeys (shared.append left) (shared.append right) x) +
        2 * max (derivedDrift j.epoch.toNat left) (derivedDrift j.epoch.toNat right)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  have _ := caps
  have _ := aligned
  have _ := withdrawalDelay
  rcases accountable_safety_at_calls shared left right parameters genesis earlyA earlyB
    enoughA enoughB j (field.imp_right Or.inl) ordered conflict with witnesses | hashes
  · obtain ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, bound⟩ := witnesses
    have budget (c : EitherCall (shared.append left) (shared.append right))
        (lower : a.state.finalizedCheckpoint.epoch.toNat ≤ c.targetEpoch)
        (upper : c.targetEpoch ≤ j.epoch.toNat) :
        stateDrift x c.state ≤
          max (derivedDrift j.epoch.toNat left) (derivedDrift j.epoch.toNat right) := by
      cases c with
      | inl c => exact (selected_call_drift_le shared left parameters _ _ starts c lower
          upper).trans (Nat.le_max_left _ _)
      | inr c => exact (selected_call_drift_le shared right parameters _ _ starts c lower
          upper).trans (Nat.le_max_right _ _)
    have first := budget one lowerOne upperOne
    have second := budget two lowerTwo upperTwo
    exact .inl (by omega)
  · exact .inr hashes

/-- The signer interpretation is conditional, with no probability or sampling theorem. -/
theorem accepted_evidence_is_signed {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (signed : BLSPubkey → AttestationData → Prop)
    (authA : Authenticated left signed) (authB : Authenticated right signed)
    (key : BLSPubkey) (slashable : Slashable left right key) :
    ∃ d₁ d₂, signed key d₁ ∧ signed key d₂ ∧ isSlashableAttestationData d₁ d₂ = true := by
  obtain ⟨d₁, d₂, first, second, conflict⟩ := slashable
  exact ⟨d₁, d₂, first.elim (authA key d₁) (authB key d₁),
    second.elim (authA key d₂) (authB key d₂), conflict⟩

end EthLib.Consensus.DirectSafety
