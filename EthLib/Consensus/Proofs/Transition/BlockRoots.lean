module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the slots keep the root of the latest block

Each slot step writes the root of the latest block header into the buffer of block roots.

It fills the state root of the header when that root is zero.

So it writes the root of the new header.

The epoch transition changes neither the buffer of block roots nor the latest block header.

So after the slots up to a later slot, the root at the slot before it is the root of the header.

The block handler uses this to show which parent a block it accepts names.

The block, and from Gloas its bid, names that root as its parent.

From Gloas the slots and the epoch transition also keep the latest block hash and the latest bid.

The slots and the transition keep the genesis time.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- A successful slot run splits at any number of its steps. -/
theorem advanceSlots_split {first rest : Nat}
    (computed : advanceSlots config checks (first + rest) state = .ok after) :
    ∃ middle, advanceSlots config checks first state = .ok middle ∧
      advanceSlots config checks rest middle = .ok after := by
  induction first generalizing state with
  | zero => exact ⟨state, rfl, by simpa only [Nat.zero_add] using computed⟩
  | succ first ih =>
    rw [Nat.succ_add] at computed
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, stepped, tail⟩ := computed
    obtain ⟨middle, before, afterOk⟩ := ih tail
    exact ⟨middle, by simp only [advanceSlots, stepped, bind, Except.bind]; exact before, afterOk⟩

/-- A successful slot run visits every intermediate slot. -/
theorem processSlots_split {slot middleSlot : Slot}
    (computed : processSlots config checks state slot = .ok after)
    (low : state.slot < middleSlot) (high : middleSlot < slot) :
    ∃ middle, processSlots config checks state middleSlot = .ok middle ∧
      processSlots config checks middle slot = .ok after := by
  have lo := UInt64.lt_iff_toNat_lt.mp low
  have hi := UInt64.lt_iff_toNat_lt.mp high
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, run⟩ := computed
  have sum : slot.toNat - state.slot.toNat =
      (middleSlot.toNat - state.slot.toNat) + (slot.toNat - middleSlot.toNat) := by omega
  rw [sum] at run
  obtain ⟨middle, before, afterOk⟩ := advanceSlots_split run
  have middleAt : middle.slot = middleSlot := by
    apply UInt64.toNat_inj.mp
    have := advanceSlots_slot _ before
    omega
  refine ⟨middle, ?_, ?_⟩
  · simp only [processSlots, bind_ok_iff, ensure_ok_iff]
    exact ⟨(), low, before⟩
  · simp only [processSlots, bind_ok_iff, ensure_ok_iff, middleAt]
    exact ⟨(), high, afterOk⟩

/-- A slot keeps a header whose state root is already nonzero. -/
theorem processSlot_latestBlockHeader_of_nonzero
    (nonzero : state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0)
    (computed : processSlot state = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨stateRoot, hashed, stateRoots, written, root, rooted, blockRoots, stored, computed⟩ :=
    computed
  simp only [nonzero, ↓reduceIte] at computed
  split at computed
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl

/-- The first cached slot fills an empty header state root with the root of its input state. -/
theorem processSlot_latestBlockHeader_of_zero {root : Root}
    (zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (hashed : SszType.hashTreeRoot state = .ok root)
    (computed : processSlot state = .ok after) :
    after.latestBlockHeader = { state.latestBlockHeader with stateRoot := root } := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨stateRoot, stateHashed, stateRoots, written, blockRoot, rooted, blockRoots, stored,
    computed⟩ := computed
  rw [hashed, Except.ok.injEq] at stateHashed
  subst stateRoot
  simp only [zero, ↓reduceIte] at computed
  split at computed
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl

/-- One slot step runs the caching, then keeps the buffer of block roots and the latest header.

It keeps the genesis time.

From Gloas it also keeps the latest block hash and the latest bid.

It moves to the next slot. -/
theorem advanceSlot_cachedRoots
    (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, processSlot state = .ok cached ∧ after.genesisTime = cached.genesisTime ∧
      after.blockRoots = cached.blockRoots ∧
      after.latestBlockHeader = cached.latestBlockHeader ∧
      after.latestBlockHash = cached.latestBlockHash ∧
      after.latestExecutionPayloadBid = cached.latestExecutionPayloadBid ∧
      after.slot.toNat = state.slot.toNat + 1 := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  refine ⟨cached, cachedOk, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨_, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    obtain ⟨genesis, roots, header, hash, bid, -⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    exact ⟨frame.genesisTime.trans genesis, frame.blockRoots.trans roots,
      frame.latestBlockHeader.trans header, frame.latestBlockHash.trans hash,
      frame.latestExecutionPayloadBid.trans bid, sum⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, rfl, rfl, rfl, sum⟩

/-- After one slot, the latest block header is the one before, with its state root filled if zero.

The root that fills it is the root of the state before the slot. -/
theorem advanceSlot_latestBlockHeader (computed : advanceSlot config checks state = .ok after) :
    ∃ root, SszType.hashTreeRoot state = .ok root ∧
      after.latestBlockHeader =
        if state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
          { state.latestBlockHeader with stateRoot := root } else state.latestBlockHeader := by
  obtain ⟨cached, cachedOk, -, -, header, -⟩ := advanceSlot_cachedRoots computed
  rw [header]
  unfold processSlot at cachedOk
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at cachedOk
  obtain ⟨root, hashed, _, _, _, _, _, _, cachedOk⟩ := cachedOk
  refine ⟨root, hashed, ?_⟩
  split at cachedOk
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp cachedOk)
    rfl
  · cases cachedOk
    rfl

/-- Advancing one slot keeps a header whose state root is nonzero. -/
theorem advanceSlot_latestBlockHeader_of_nonzero
    (nonzero : state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0)
    (computed : advanceSlot config checks state = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  obtain ⟨cached, cachedOk, -, -, header, -⟩ := advanceSlot_cachedRoots computed
  exact header.trans (processSlot_latestBlockHeader_of_nonzero nonzero cachedOk)

/-- Empty slots keep a header whose state root is nonzero. -/
theorem advanceSlots_latestBlockHeader_of_nonzero
    (nonzero : state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0) {count : Nat}
    (computed : advanceSlots config checks count state = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    rfl
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, stepped, rest⟩ := computed
    have kept := advanceSlot_latestBlockHeader_of_nonzero nonzero stepped
    exact (ih (kept ▸ nonzero) rest).trans kept

/-- Processing to a later slot keeps a header whose state root is nonzero. -/
theorem processSlots_latestBlockHeader_of_nonzero {slot : Slot}
    (nonzero : state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0)
    (computed : processSlots config checks state slot = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advanced⟩ := computed
  exact advanceSlots_latestBlockHeader_of_nonzero nonzero advanced

/-- After a nonempty run, an initially empty header contains the nonzero initial state root. -/
theorem advanceSlots_latestBlockHeader_of_zero {root : Root} {count : Nat}
    (zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (hashed : SszType.hashTreeRoot state = .ok root) (nonzero : root ≠ Vector.replicate 32 0)
    (computed : advanceSlots config checks (count + 1) state = .ok after) :
    after.latestBlockHeader = { state.latestBlockHeader with stateRoot := root } := by
  simp only [advanceSlots, bind_ok_iff] at computed
  obtain ⟨next, stepped, rest⟩ := computed
  obtain ⟨cached, cachedOk, -, -, header, -⟩ := advanceSlot_cachedRoots stepped
  have filled := header.trans (processSlot_latestBlockHeader_of_zero zero hashed cachedOk)
  have kept := advanceSlots_latestBlockHeader_of_nonzero
    (state := next) (by rw [filled]; exact nonzero) rest
  exact kept.trans filled

/-- Processing empty slots fills a zero header once when the initial state root is nonzero. -/
theorem processSlots_latestBlockHeader_of_zero {root : Root} {slot : Slot}
    (zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (hashed : SszType.hashTreeRoot state = .ok root) (nonzero : root ≠ Vector.replicate 32 0)
    (computed : processSlots config checks state slot = .ok after) :
    after.latestBlockHeader = { state.latestBlockHeader with stateRoot := root } := by
  have earlier := UInt64.lt_iff_toNat_lt.mp (processSlots_slot computed).1
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advanced⟩ := computed
  obtain ⟨count, eq⟩ : ∃ count, slot.toNat - state.slot.toNat = count + 1 :=
    ⟨slot.toNat - state.slot.toNat - 1, by omega⟩
  rw [eq] at advanced
  exact advanceSlots_latestBlockHeader_of_zero zero hashed nonzero advanced

/-- Two nonempty slot runs from one state finish with the same header. -/
theorem processSlots_latestBlockHeader_eq {left right : BeaconState preset fork}
    {leftChecks rightChecks : SignatureChecks} {leftSlot rightSlot : Slot} {root : Root}
    (hashed : SszType.hashTreeRoot state = .ok root) (nonzero : root ≠ Vector.replicate 32 0)
    (one : processSlots config leftChecks state leftSlot = .ok left)
    (two : processSlots config rightChecks state rightSlot = .ok right) :
    left.latestBlockHeader = right.latestBlockHeader := by
  by_cases zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0
  · rw [processSlots_latestBlockHeader_of_zero zero hashed nonzero one,
      processSlots_latestBlockHeader_of_zero zero hashed nonzero two]
  · rw [processSlots_latestBlockHeader_of_nonzero zero one,
      processSlots_latestBlockHeader_of_nonzero zero two]

/-- A read before a slot step comes from the old buffer or the header cached at that step. -/
theorem getBlockRootAtSlot_advanceSlot_cases {slot : Slot} {root : Root}
    (computed : advanceSlot config checks state = .ok after)
    (read : getBlockRootAtSlot after slot = .ok root) :
    (slot < state.slot ∧ getBlockRootAtSlot state slot = .ok root) ∨
      (slot = state.slot ∧ SszType.hashTreeRoot after.latestBlockHeader = .ok root) := by
  obtain ⟨cached, cachedOk, -, roots, header, -, -, afterSlot⟩ := advanceSlot_cachedRoots computed
  obtain ⟨writtenRoot, hashed, written⟩ := processSlot_blockRoots cachedOk
  obtain ⟨before, fits, recent, readBuffer⟩ := getBlockRootAtSlot_ok_iff.mp read
  by_cases same : slot = state.slot
  · right
    refine ⟨same, ?_⟩
    rw [roots, same, readCircular_writeCircular written] at readBuffer
    rw [header, hashed, Except.ok.inj readBuffer]
  · left
    have lt : slot.toNat < state.slot.toNat := by
      have ne : slot.toNat ≠ state.slot.toNat := fun eq => same (UInt64.toNat_inj.mp eq)
      omega
    have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
        slot % preset.SLOTS_PER_HISTORICAL_ROOT := by
      intro eq
      have eq' := congrArg UInt64.toNat eq
      simp only [UInt64.toNat_mod] at eq'
      exact Nat.mod_ne_of_sub_lt lt (by omega) eq'
    rw [roots, readCircular_writeCircular_of_ne written other] at readBuffer
    exact ⟨UInt64.lt_iff_toNat_lt.mpr lt,
      getBlockRootAtSlot_ok_iff.mpr ⟨lt, fits, by omega, readBuffer⟩⟩

/-- A history read that predates a run of empty slots was already in its input state. -/
theorem getBlockRootAtSlot_of_advanceSlots {slot : Slot} {root : Root} {count : Nat}
    (computed : advanceSlots config checks count state = .ok after)
    (read : getBlockRootAtSlot after slot = .ok root) :
    slot < state.slot → getBlockRootAtSlot state slot = .ok root := by
  intro earlier
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    exact read
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, stepped, rest⟩ := computed
    obtain ⟨_, _, _, _, _, _, _, nextSlot⟩ := advanceSlot_cachedRoots stepped
    have earlierNext : slot < next.slot := by
      have := UInt64.lt_iff_toNat_lt.mp earlier
      exact UInt64.lt_iff_toNat_lt.mpr (by omega)
    have nextRead := ih rest earlierNext
    rcases getBlockRootAtSlot_advanceSlot_cases stepped nextRead with kept | ⟨same, -⟩
    · exact kept.2
    · subst slot
      exact (UInt64.lt_irrefl _ earlier).elim

/-- A root written during empty slots hashes their unchanged nonzero header. -/
theorem getBlockRootAtSlot_advanceSlots_of_nonzero {slot : Slot} {root : Root} {count : Nat}
    (nonzero : state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0)
    (computed : advanceSlots config checks count state = .ok after)
    (read : getBlockRootAtSlot after slot = .ok root) (later : state.slot ≤ slot) :
    SszType.hashTreeRoot state.latestBlockHeader = .ok root := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    have lt := (getBlockRootAtSlot_ok_iff.mp read).1
    have le := UInt64.le_iff_toNat_le.mp later
    omega
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, stepped, rest⟩ := computed
    have kept := advanceSlot_latestBlockHeader_of_nonzero nonzero stepped
    by_cases before : slot < next.slot
    · have firstRead := getBlockRootAtSlot_of_advanceSlots rest read before
      rcases getBlockRootAtSlot_advanceSlot_cases stepped firstRead with old | ⟨-, hashed⟩
      · have lt := UInt64.lt_iff_toNat_lt.mp old.1
        have le := UInt64.le_iff_toNat_le.mp later
        omega
      · rwa [kept] at hashed
    · have hashed := ih (kept ▸ nonzero) rest (UInt64.not_lt.mp before)
      rwa [kept] at hashed

/-- A root written after an empty header is filled hashes the header with the initial state root. -/
theorem getBlockRootAtSlot_advanceSlots_of_zero {slot : Slot} {root stateRoot : Root}
    {count : Nat} (zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (hashed : SszType.hashTreeRoot state = .ok stateRoot)
    (nonzero : stateRoot ≠ Vector.replicate 32 0)
    (computed : advanceSlots config checks count state = .ok after)
    (read : getBlockRootAtSlot after slot = .ok root) (later : state.slot ≤ slot) :
    SszType.hashTreeRoot { state.latestBlockHeader with stateRoot } = .ok root := by
  cases count with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    have lt := (getBlockRootAtSlot_ok_iff.mp read).1
    have le := UInt64.le_iff_toNat_le.mp later
    omega
  | succ count =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, stepped, rest⟩ := computed
    obtain ⟨cached, cachedOk, -, -, header, -⟩ := advanceSlot_cachedRoots stepped
    have filled := header.trans (processSlot_latestBlockHeader_of_zero zero hashed cachedOk)
    by_cases before : slot < next.slot
    · have firstRead := getBlockRootAtSlot_of_advanceSlots rest read before
      rcases getBlockRootAtSlot_advanceSlot_cases stepped firstRead with old | ⟨-, rooted⟩
      · have lt := UInt64.lt_iff_toNat_lt.mp old.1
        have le := UInt64.le_iff_toNat_le.mp later
        omega
      · rwa [filled] at rooted
    · have rooted := getBlockRootAtSlot_advanceSlots_of_nonzero
        (state := next) (by rw [filled]; exact nonzero) rest read (UInt64.not_lt.mp before)
      rwa [filled] at rooted

/-- A history read written in empty slots equals their final header root.

A nonzero initial state root prevents the zero header sentinel from being filled twice. -/
theorem getBlockRootAtSlot_processSlots_header {slot query : Slot} {root stateRoot : Root}
    (hashed : SszType.hashTreeRoot state = .ok stateRoot)
    (nonzero : stateRoot ≠ Vector.replicate 32 0)
    (computed : processSlots config checks state slot = .ok after)
    (read : getBlockRootAtSlot after query = .ok root) (later : state.slot ≤ query) :
    SszType.hashTreeRoot after.latestBlockHeader = .ok root := by
  have run := computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
  obtain ⟨_, -, advanced⟩ := run
  by_cases zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0
  · rw [processSlots_latestBlockHeader_of_zero zero hashed nonzero computed]
    exact getBlockRootAtSlot_advanceSlots_of_zero zero hashed nonzero advanced read later
  · rw [processSlots_latestBlockHeader_of_nonzero zero computed]
    exact getBlockRootAtSlot_advanceSlots_of_nonzero zero advanced read later

/-- One slot keeps the root recorded at a slot while that slot stays in the buffer of roots. -/
theorem getBlockRootAtSlot_advanceSlot {slot : Slot} {root : Root}
    (computed : advanceSlot config checks state = .ok after)
    (read : getBlockRootAtSlot state slot = .ok root)
    (recent : state.slot.toNat < slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRootAtSlot after slot = .ok root := by
  obtain ⟨cached, cachedOk, -, roots, -, -, -, afterSlot⟩ := advanceSlot_cachedRoots computed
  obtain ⟨_, -, written⟩ := processSlot_blockRoots cachedOk
  obtain ⟨before, readOk⟩ := getBlockRootAtSlot_read read
  have before' := UInt64.lt_iff_toNat_lt.mp before
  have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
      slot % preset.SLOTS_PER_HISTORICAL_ROOT := by
    intro same
    have same' := congrArg UInt64.toNat same
    rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
    exact Nat.mod_ne_of_sub_lt before' (by omega) same'
  unfold getBlockRootAtSlot at read
  simp only [before, ↓reduceIte, bind_ok_iff, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at read
  obtain ⟨bound, ⟨fits, boundEq⟩, -⟩ := read
  unfold getBlockRootAtSlot
  have later : slot < after.slot := UInt64.lt_iff_toNat_lt.mpr (by omega)
  simp only [later, ↓reduceIte, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
  refine ⟨bound, ⟨fits, boundEq⟩, ?_⟩
  have within : after.slot ≤ bound := UInt64.le_iff_toNat_le.mpr (by omega)
  simp only [within, ↓reduceIte, roots]
  rw [readCircular_writeCircular_of_ne written other]
  exact readOk

/-- One slot keeps the root of the block at the first slot of an epoch.

That slot must stay in the buffer of roots at the next slot. -/
theorem getBlockRoot_advanceSlot {epoch : Epoch} {root : Root}
    (computed : advanceSlot config checks state = .ok after)
    (read : getBlockRoot state epoch = .ok root)
    (recent : state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRoot after epoch = .ok root := by
  unfold getBlockRoot at read ⊢
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at read ⊢
  obtain ⟨start, startOk, read⟩ := read
  refine ⟨start, startOk, getBlockRootAtSlot_advanceSlot computed read ?_⟩
  rw [(mulChecked_ok_iff.mp startOk).2]
  exact recent

/-- A state one slot later with the same roots reads the same root of an epoch.

The first slot of the epoch must be before the slot of the earlier state and stay in the buffer. -/
theorem getBlockRoot_succ_iff {other : BeaconState preset fork}
    (roots : other.blockRoots = state.blockRoots) (slot : other.slot.toNat = state.slot.toNat + 1)
    {epoch : Epoch} {root : Root}
    (before : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat)
    (recent : state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRoot other epoch = .ok root ↔ getBlockRoot state epoch = .ok root := by
  rw [getBlockRoot_ok_iff, getBlockRoot_ok_iff]
  refine exists_congr fun start => and_congr_right fun startOk => ?_
  have startEq := (mulChecked_ok_iff.mp startOk).2
  rw [getBlockRootAtSlot_ok_iff, getBlockRootAtSlot_ok_iff, roots, slot]
  constructor
  · rintro ⟨-, fits, -, read⟩
    exact ⟨by omega, fits, by omega, read⟩
  · rintro ⟨-, fits, -, read⟩
    exact ⟨by omega, fits, by omega, read⟩

/-- The caching of a slot keeps the root recorded at a slot while that slot stays in the buffer.

It writes the entry of the current slot only. -/
theorem getBlockRootAtSlot_processSlot {cached : BeaconState preset fork} {slot : Slot}
    (computed : processSlot state = .ok cached)
    (recent : state.slot.toNat < slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRootAtSlot cached slot = getBlockRootAtSlot state slot := by
  obtain ⟨_, -, written⟩ := processSlot_blockRoots computed
  unfold getBlockRootAtSlot
  rw [processSlot_slot computed]
  by_cases lt : slot < state.slot
  · simp only [lt, ↓reduceIte]
    rcases sum : addChecked slot preset.SLOTS_PER_HISTORICAL_ROOT with _ | bound
    · rfl
    · by_cases within : state.slot ≤ bound
      · simp only [liftArith, Except.mapError, within, ↓reduceIte, bind, Except.bind]
        refine readCircular_writeCircular_of_ne written fun same => ?_
        have same' := congrArg UInt64.toNat same
        rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
        have lt' := UInt64.lt_iff_toNat_lt.mp lt
        exact Nat.mod_ne_of_sub_lt lt' (by omega) same'
      · simp only [liftArith, Except.mapError, within, ↓reduceIte, bind, Except.bind]
        rfl
  · simp only [lt, ↓reduceIte]
    rfl

/-- The caching of a slot keeps the root of the block at the first slot of an epoch.

That slot must stay in the buffer of roots. -/
theorem getBlockRoot_processSlot {cached : BeaconState preset fork} {epoch : Epoch}
    (computed : processSlot state = .ok cached)
    (recent : state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRoot cached epoch = getBlockRoot state epoch := by
  unfold getBlockRoot
  rcases start : computeStartSlotAtEpoch preset epoch with _ | first
  · rfl
  · simp only [liftArith, Except.mapError, bind, Except.bind]
    refine getBlockRootAtSlot_processSlot computed ?_
    rw [(mulChecked_ok_iff.mp start).2]
    exact recent

/-- After one slot, the root at the slot before the new one is that of the header. -/
theorem advanceSlot_latestBlockRoot
    (computed : advanceSlot config checks state = .ok after) :
    ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
      readCircular after.blockRoots.elements (after.slot - 1) = .ok root := by
  obtain ⟨cached, cachedOk, -, roots, header, -, -, slot⟩ := advanceSlot_cachedRoots computed
  obtain ⟨root, hashed, written⟩ := processSlot_blockRoots cachedOk
  have previous : after.slot - 1 = state.slot := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), slot]
    simp
  rw [header, roots, previous]
  exact ⟨root, hashed, readCircular_writeCircular written⟩

/-- After one slot or more, the root at the slot before the last one is that of the header. -/
private theorem advanceSlots_latestBlockRoot :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks (count + 1) state = .ok after →
      ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
        readCircular after.blockRoots.elements (after.slot - 1) = .ok root
  | 0, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, first, rfl⟩ := computed
    exact advanceSlot_latestBlockRoot first
  | count + 1, _, _, computed => by
    rw [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, _, rest⟩ := computed
    exact advanceSlots_latestBlockRoot count rest

/-- After the slots up to a later slot, the root at the slot before it is that of the header.

That root is the root of the latest block header of the result. -/
theorem processSlots_latestBlockRoot {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
      readCircular after.blockRoots.elements (slot - 1) = .ok root := by
  obtain ⟨lt, reached⟩ := processSlots_slot computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advanced⟩ := computed
  have lt' := UInt64.lt_iff_toNat_lt.mp lt
  obtain ⟨count, counted⟩ : ∃ count, slot.toNat - state.slot.toNat = count + 1 :=
    ⟨slot.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  rw [← reached]
  exact advanceSlots_latestBlockRoot count advanced

/-- The slots keep the genesis time, the latest block hash and the latest bid, for any count. -/
private theorem advanceSlots_keeps :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      after.genesisTime = state.genesisTime ∧ after.latestBlockHash = state.latestBlockHash ∧
        after.latestExecutionPayloadBid = state.latestExecutionPayloadBid
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl⟩
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, first, rest⟩ := computed
    obtain ⟨_, cachedOk, genesisKept, -, -, hashKept, bidKept, -⟩ := advanceSlot_cachedRoots first
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    obtain ⟨genesis, hash, bid⟩ := advanceSlots_keeps count rest
    exact ⟨genesis.trans genesisKept, hash.trans hashKept, bid.trans bidKept⟩

/-- The slots keep the latest block hash and the latest bid. -/
theorem processSlots_latestBid {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.latestBlockHash = state.latestBlockHash ∧
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact (advanceSlots_keeps _ advanced).2

/-- The slots keep the genesis time. -/
theorem processSlots_genesisTime {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.genesisTime = state.genesisTime := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact (advanceSlots_keeps _ advanced).1

/-- The transition of a block keeps the genesis time. -/
theorem stateTransition_genesisTime {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    after.genesisTime = state.genesisTime := by
  obtain ⟨_, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  exact (frame_processBlock blockOk).genesisTime.trans (processSlots_genesisTime slotsOk)

end EthLib.Consensus
