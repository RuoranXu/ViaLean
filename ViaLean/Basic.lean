import Lean

open Lean Meta

namespace ViaLean

/-- Monotonic wall-clock budget shared by every search action. -/
structure Budget where
  deadlineMs : UInt64
deriving Inhabited, Repr

def Budget.start (timeoutSec : Nat) : IO Budget := do
  let now := UInt64.ofNat (← IO.monoMsNow)
  pure ⟨now + UInt64.ofNat (timeoutSec * 1000)⟩

def Budget.remainingMs (budget : Budget) : IO Nat := do
  let now := UInt64.ofNat (← IO.monoMsNow)
  if budget.deadlineMs ≤ now then return 0
  return (budget.deadlineMs - now).toNat

def Budget.remainingSecCeil (budget : Budget) : IO Nat := do
  let ms ← budget.remainingMs
  return if ms = 0 then 0 else (ms + 999) / 1000

def Budget.remainingSecFloor (budget : Budget) : IO Nat := do
  return (← budget.remainingMs) / 1000

def exprSize : Expr → Nat
  | .forallE _ d b _ | .lam _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .app f a => 1 + exprSize f + exprSize a
  | .mdata _ e | .proj _ _ e => 1 + exprSize e
  | _ => 1

/-- Detect `sorryAx` without consuming Lean's recursion-depth budget. Mathlib
proof terms can be much deeper than the dependency-free core examples. -/
def containsSorry (root : Expr) : Bool := Id.run do
  let mut pending := #[root]
  while !pending.isEmpty do
    let expr := pending.back!
    pending := pending.pop
    match expr with
    | .const ``sorryAx _ => return true
    | .app f a => pending := (pending.push f).push a
    | .lam _ d b _ | .forallE _ d b _ => pending := (pending.push d).push b
    | .letE _ t v b _ => pending := ((pending.push t).push v).push b
    | .mdata _ e | .proj _ _ e => pending := pending.push e
    | _ => pure ()
  return false

/-- Recognize exactly the standard `Nat` modulo instance. -/
private def isStandardNatModInstance (inst : Expr) : Bool :=
  match inst.getAppFnArgs with
  | (``instHMod, #[carrier, modInstance]) =>
      carrier.isConstOf ``Nat && modInstance.isConstOf ``Nat.instMod
  | _ => false

/-- Recognize exactly the standard `Nat` exponentiation instance. -/
private def isStandardNatPowInstance (inst : Expr) : Bool :=
  match inst.getAppFnArgs with
  | (``instHPow, #[baseType, exponentType, natPow]) =>
      baseType.isConstOf ``Nat && exponentType.isConstOf ``Nat &&
        match natPow.getAppFnArgs with
        | (natPowName, #[carrier, monoid]) =>
            carrier.isConstOf ``Nat && natPowName.toString == "Monoid.toNatPow" &&
              match monoid.getAppFn with
              | .const monoidName _ => monoidName.toString == "Nat.instMonoid"
              | _ => false
        | _ => false
  | _ => false

private def rawNatLit? : Expr → Option Nat
  | .lit (.natVal value) => some value
  | _ => none

private def standardNatNumeral? (expr : Expr) : Option Nat :=
  match rawNatLit? expr with
  | some value => some value
  | none =>
      match expr.getAppFnArgs with
      | (``OfNat.ofNat, #[carrier, numeral, inst]) =>
          if !carrier.isConstOf ``Nat then none else
            match rawNatLit? numeral, inst.getAppFnArgs with
            | some value, (``instOfNatNat, #[instNumeral]) =>
                if instNumeral == numeral then some value else none
            | _, _ => none
      | _ => none
/-- Remove only the exact standard `Nat` overload wrappers, without invoking
reduction. In particular this never evaluates `Nat.pow` or `Nat.mod`. -/
private partial def normalizeNatSurface (expr : Expr) : Expr :=
  if let some value := standardNatNumeral? expr then
    mkRawNatLit value
  else
    match expr.getAppFnArgs with
    | (``HMod.hMod, #[inputType, modulusType, outputType, inst, dividend, modulus]) =>
        if inputType.isConstOf ``Nat && modulusType.isConstOf ``Nat &&
            outputType.isConstOf ``Nat && isStandardNatModInstance inst then
          mkApp2 (mkConst ``Nat.mod) (normalizeNatSurface dividend)
            (normalizeNatSurface modulus)
        else expr
    | (``HPow.hPow, #[baseType, exponentType, outputType, inst, base, exponent]) =>
        if baseType.isConstOf ``Nat && exponentType.isConstOf ``Nat &&
            outputType.isConstOf ``Nat && isStandardNatPowInstance inst then
          mkApp2 (mkConst ``Nat.pow) (normalizeNatSurface base)
            (normalizeNatSurface exponent)
        else expr
    | (``Nat.mod, #[dividend, modulus]) =>
        mkApp2 (mkConst ``Nat.mod) (normalizeNatSurface dividend)
          (normalizeNatSurface modulus)
    | (``Nat.pow, #[base, exponent]) =>
        mkApp2 (mkConst ``Nat.pow) (normalizeNatSurface base)
          (normalizeNatSurface exponent)
    | _ => expr

/-- Canonicalize only safe surface syntax on both sides of a `Nat` equality. -/
private def normalizeNatEqualitySurface? (type : Expr) : Option Expr := do
  let (carrier, lhs, rhs) ← type.eq?
  if !carrier.isConstOf ``Nat then none else
    some (mkApp3 (mkConst ``Eq [levelZero]) carrier
      (normalizeNatSurface lhs) (normalizeNatSurface rhs))
/-- Fully instantiate and check a candidate at the final trust boundary. -/
def finalizeProof (target proof : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  if containsSorry proof then
    throwError "ViaLean rejected a proof containing sorryAx"
  -- Type inference solves universe constraints introduced by reconstructed constants.
  discard <| inferType proof
  let proof ← instantiateMVars proof
  let inferred ← instantiateMVars (← inferType proof)
  let inferredSurface? := normalizeNatEqualitySurface? inferred
  let targetSurface? := normalizeNatEqualitySurface? target
  let surfaceMatch := match inferredSurface?, targetSurface? with
    | some inferred, some target => inferred == target
    | _, _ => false
  unless inferred == target || surfaceMatch do
    unless ← isDefEq inferred target do
      throwError "ViaLean internal error: proof has type {inferred}, expected {target}"
  let proof ← instantiateMVars proof
  if proof.hasMVar then
    throwError "ViaLean rejected a proof with unresolved metavariables"
  return proof

/-- Check the final trust boundary before a candidate proof is accepted. -/
def checkProof (target proof : Expr) : MetaM Unit := do
  discard <| finalizeProof target proof

end ViaLean
