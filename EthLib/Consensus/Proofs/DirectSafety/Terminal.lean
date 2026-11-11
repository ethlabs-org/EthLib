module

public import EthLib.Consensus.Proofs.DirectSafety.Drift

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

/-- Either the real endpoint fields or the result of one successful terminal projection. -/
inductive TerminalView (a : ForkedBeaconState preset) : Type where
  | realized
  | pulled (after : BeaconState preset a.fork)
      (ok : processJustificationAndFinalization a.state = .ok after)

def TerminalView.state {a : ForkedBeaconState preset}
    (view : TerminalView a) : BeaconState preset a.fork :=
  match view with
  | .realized => a.state
  | .pulled after _ => after

/-- The terminal count needs its own bound beyond those of historical epoch calls. -/
def TerminalView.enough {a : ForkedBeaconState preset} (view : TerminalView a) : Prop :=
  match view with
  | .realized => True
  | .pulled _ _ => GENESIS_EPOCH + 1 < getCurrentEpoch a.state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Quorum.weight (effectiveWeight a.state) (activeKeys a.state)

/-- Charge the actual terminal input, not a hypothetical future endpoint. -/
noncomputable def terminalDrift {x a : ForkedBeaconState preset}
    (high : Nat) (tail : Run config checks x a) (view : TerminalView a) : Nat :=
  match view with
  | .realized => derivedDrift high tail
  | .pulled _ _ => max (derivedDrift high tail) (stateDrift x a)

def TerminalView.hashObjects {a : ForkedBeaconState preset}
    (view : TerminalView a) : List (HashObject preset) :=
  match view with
  | .realized => []
  | .pulled after _ => [.state a, .header a.state.latestBlockHeader,
      .state ⟨a.fork, after⟩, .header after.latestBlockHeader]

/-- Successful reads and a passing test at the input of the selected projection.

The witness retains the projection equation rather than a future epoch-call occurrence. -/
structure TerminalQuorum {a : ForkedBeaconState preset} (view : TerminalView a) where
  after : BeaconState preset a.fork
  projected : processJustificationAndFinalization a.state = .ok after
  selected : view = .pulled after projected
  later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state
  current : Bool
  target : Checkpoint
  targetEpoch : target.epoch =
    if current then getCurrentEpoch a.state else getPreviousEpoch a.state
  targetRoot : getBlockRoot a.state target.epoch = .ok target.root
  indices : List ValidatorIndex
  counted : targetIndices a.state target.epoch = .ok indices
  total : Gwei
  part : Gwei
  threshold : Gwei
  weighted : Gwei
  totalOk : getTotalActiveBalance a.state = .ok total
  partOk : getTotalBalance a.state indices = .ok part
  thresholdOk : Uint64.mulChecked total 2 = .ok threshold
  weightedOk : Uint64.mulChecked part 3 = .ok weighted
  passes : threshold ≤ weighted

def TerminalQuorum.source {a : ForkedBeaconState preset} {view : TerminalView a}
    (call : TerminalQuorum view) : Checkpoint :=
  if call.current then a.state.currentJustifiedCheckpoint
    else a.state.previousJustifiedCheckpoint

noncomputable def TerminalQuorum.voters {a : ForkedBeaconState preset}
    {view : TerminalView a} (call : TerminalQuorum view) : Finset BLSPubkey :=
  keysAt a.state call.indices

/-- A history may finish with one terminal count, but its earlier counts remain real calls. -/
abbrev ViewQuorum {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (view : TerminalView a) :=
  QuorumCall run ⊕ TerminalQuorum view

def ViewQuorum.source {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {view : TerminalView a} (call : ViewQuorum run view) : Checkpoint :=
  match call with
  | .inl c => c.source
  | .inr c => c.source

def ViewQuorum.target {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {view : TerminalView a} (call : ViewQuorum run view) : Checkpoint :=
  match call with
  | .inl c => c.target
  | .inr c => c.target

noncomputable def ViewQuorum.voters {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {view : TerminalView a}
    (call : ViewQuorum run view) : Finset BLSPubkey :=
  match call with
  | .inl c => c.voters
  | .inr c => c.voters

def ViewQuorum.state {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {view : TerminalView a} (call : ViewQuorum run view) : ForkedBeaconState preset :=
  match call with
  | .inl c => ⟨c.before.fork, c.cached⟩
  | .inr _ => a

structure ViewHistory {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (view : TerminalView a) (checkpoint : Checkpoint) where
  calls : List (ViewQuorum run view)
  nonempty : calls ≠ []
  start : ∀ c, calls.head? = some c → c.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  finish : ∀ c, calls.getLast? = some c → c.target = checkpoint
  consecutive : ∀ i left right, calls[i]? = some left → calls[i + 1]? = some right →
    left.target = right.source

end EthLib.Consensus.DirectSafety
