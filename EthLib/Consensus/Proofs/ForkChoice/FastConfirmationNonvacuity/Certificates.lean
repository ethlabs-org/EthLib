module

public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public meta import Lean
public meta import EthLib.Serialization.Ssz.Codec.Root

/-! These certificates compute candidate bytes outside the kernel, then prove them inside it.

The candidate computation is not trusted: each result needs a kernel-checked equality proof.

Repeated SSZ subroots reuse those proofs instead of rebuilding their reduction traces.

Open the `NonvacuityCertificates` scope to enable these procedures in a certificate file.

Each auxiliary equality is checked synchronously before another certificate may reuse it. -/

@[expose] public section

namespace EthLib.Consensus.NonvacuityCertificates

open Serialization.Ssz

set_option Elab.async false

open Lean Meta Sym Tactic.Cbv Cryptography.Hash in
scoped cbv_simproc cbv_eval sha256Certificate (Sha256.hash _) := fun e => do
  let_expr Sha256.hash bytes := e | return .rfl
  let_expr ByteArray.mk data := bytes | return .rfl
  let_expr Array.mk _ items := data | return .rfl
  let some elems := getListLitElems items | return .rfl
  let some values := elems.mapM (m := Option) (fun x => (Sym.getUInt8Value? x).run) |
    return .rfl
  let hashed := Sha256.hash ⟨values⟩
  let array := mkApp2 (mkConst ``Array.mk [0]) (mkConst ``UInt8) (toExpr hashed.data.toList)
  let result ← share <| mkApp (mkConst ``ByteArray.mk) array
  let expected ← liftM <| Meta.mkEq e result
  -- Reflexivity checks the actual SHA-256 reduction, not the candidate generator.
  let name ← liftM <| Meta.withFreshCache do
    let proof ← Meta.mkEqRefl result
    withOptions (Elab.async.set · false) <| mkAuxLemma [] expected proof
  return .step result (mkConst name)

/-- A zero-subtree certificate extends by one checked hash of its two identical children. -/
theorem zero_step (n : Nat) (previous next : Array UInt8)
    (ih : zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash n = previous)
    (hashed : Cryptography.Hash.Sha256.hash ⟨previous ++ previous⟩ = ⟨next⟩) :
    zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash (n + 1) = next := by
  change (Cryptography.Hash.Sha256.hash
    ⟨(zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash n).run ++
      (zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash n).run⟩).data = next
  rw [ih]
  exact congrArg ByteArray.data hashed

open Lean Meta Sym Tactic.Cbv Cryptography.Hash in
scoped cbv_simproc cbv_eval zeroCertificate (zeroSubtreeM Sha256.hash _) := fun e => do
  let_expr zeroSubtreeM _ _ _ count := e | return .rfl
  let some depth := Sym.getNatValue? count | return .rfl
  let literal (xs : Array UInt8) :=
    mkApp2 (mkConst ``Array.mk [0]) (mkConst ``UInt8) (toExpr xs.toList)
  let mut bytes : Array UInt8 := Array.replicate 32 0
  let mut value := literal bytes
  let mut proof ← liftM <| Meta.mkEqRefl value
  -- Each level uses the previous certificate, so padding costs one hash per level.
  for i in [:depth] do
    let next := (Sha256.hash ⟨bytes ++ bytes⟩).data
    let nextValue := literal next
    let input ← liftM <| mkAppM ``HAppend.hAppend #[value, value]
    let hash := mkApp (mkConst ``Sha256.hash) (mkApp (mkConst ``ByteArray.mk) input)
    let expected ← liftM <| Meta.mkEq hash (mkApp (mkConst ``ByteArray.mk) nextValue)
    let hashRefl ← liftM <| Meta.mkEqRefl (mkApp (mkConst ``ByteArray.mk) nextValue)
    let hashName ← liftM <|
      withOptions (Elab.async.set · false) <| mkAuxLemma [] expected hashRefl
    let step := mkApp5 (mkConst ``zero_step) (mkNatLit i) value nextValue proof (mkConst hashName)
    let type ← liftM <| Meta.inferType step
    let name ← liftM <| withOptions (Elab.async.set · false) <| mkAuxLemma [] type step
    value := nextValue
    proof := mkConst name
    bytes := next
  return .step (← share value) proof

/-- A power-of-two limit has an exact Merkle-tree depth. -/
theorem depthFor_power_two (n : Nat) : depthFor (2 ^ n) = n := by
  apply Nat.le_antisymm (depthFor_le_of_le_two_pow (Nat.le_refl _))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (le_two_pow_depthFor _)

open Lean Meta Sym Tactic.Cbv in
scoped cbv_simproc cbv_eval depthCertificate (depthFor _) := fun e => do
  let_expr depthFor count := e | return .rfl
  let some value := Sym.getNatValue? count | return .rfl
  let exponent := value.log2
  if value != 2 ^ exponent then return .rfl
  let result ← share (mkNatLit exponent)
  return .step result (mkApp (mkConst ``depthFor_power_two) result)

open Lean Meta Sym Tactic.Cbv in
private meta def literalDesc : Nat → Expr → Option Desc
  | 0, _ => none
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn.constName! with
    | ``Desc.bool => return .bool
    | ``Desc.uint => return .uint (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.byteVector => return .byteVector (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.byteList => return .byteList (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.bitVector => return .bitVector (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.bitList => return .bitList (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.vector =>
      return .vector (← literalDesc fuel args[0]!) (← (Sym.getNatValue? args[1]!).run)
    | ``Desc.list =>
      return .list (← literalDesc fuel args[0]!) (← (Sym.getNatValue? args[1]!).run)
    | ``Desc.container =>
      return .container
        ((← (← getListLitElems args[0]!).mapM Sym.getStringValue?).toList)
        ((← (← getListLitElems args[1]!).mapM (literalDesc fuel)).toList)
    | _ => none

open Lean Meta Sym Tactic.Cbv in
private meta def literalValue : Nat → Expr → Option Value
  | 0, _ => none
  | fuel + 1, e => do
    let a := e.appArg!
    match e.getAppFn.constName! with
    | ``Value.bool => return .bool (← (Sym.getBoolValue? a).run)
    | ``Value.uint => return .uint (← (Sym.getNatValue? a).run)
    | ``Value.bytes => do
      let_expr Array.mk _ items := a | none
      return .bytes (← (← getListLitElems items).mapM (fun x => (Sym.getUInt8Value? x).run))
    | ``Value.bits => do
      let_expr Array.mk _ items := a | none
      return .bits (← (← getListLitElems items).mapM (fun x => (Sym.getBoolValue? x).run))
    | ``Value.seq => return .seq ((← (← getListLitElems a).mapM (literalValue fuel)).toList)
    | _ => none

open Lean Meta Sym Tactic.Cbv Cryptography.Hash in
scoped cbv_simproc cbv_eval rootCertificate (hashTreeRootAtM _ _ _ _) := fun e => do
  let_expr hashTreeRootAtM _ _ _ budget shape input := e | return .rfl
  let some depth := Sym.getNatValue? budget | return .rfl
  -- The recursive evaluation handles this node itself and certifies only smaller children.
  if depth >= (← getOptions).get `witness.rootBudget 1000 then return .rfl
  let some desc := literalDesc 32 shape | return .rfl
  let some data := literalValue 32 input | return .rfl
  let output := (hashTreeRootAtM (m := Id) (Hasher.ofHash Sha256.hash) depth desc data).run
  let .ok bytes := output | return .rfl
  let array := mkApp2 (mkConst ``Array.mk [0]) (mkConst ``UInt8) (toExpr bytes.toList)
  let value := mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``Err)
    (mkApp (mkConst ``Array [0]) (mkConst ``UInt8)) array
  let expected ← liftM <| Meta.mkEq e value
  -- Only an already checked equality may bypass proof construction.
  let env ← getEnv
  if let some (name, _) := (auxLemmasExt.getState env).lemmas.find?
      { type := expected, isPrivate := !env.isExporting, defeq := false } then
    return .step (← share value) (mkConst name)
  let reduced ← liftM <| Meta.withFreshCache <|
    withOptions (·.set `witness.rootBudget depth) <| cbvEntry e
  let .step _ proof .. := reduced | return .rfl
  let name ← liftM <| Meta.withFreshCache <|
    withOptions (Elab.async.set · false) <| mkAuxLemma [] expected proof
  return .step (← share value) (mkConst name)

/-- The monadic SHA-256 instance is the concrete hash used by these certificates. -/
@[scoped cbv_eval] theorem hasher_certificate :
    sha256Hasher = Hasher.ofHash Cryptography.Hash.Sha256.hash := ofHash_sha256.symm

end EthLib.Consensus.NonvacuityCertificates
