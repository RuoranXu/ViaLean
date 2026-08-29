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

partial def containsSorry : Expr → Bool
  | .const ``sorryAx _ => true
  | .app f a => containsSorry f || containsSorry a
  | .lam _ d b _ | .forallE _ d b _ => containsSorry d || containsSorry b
  | .letE _ t v b _ => containsSorry t || containsSorry v || containsSorry b
  | .mdata _ e | .proj _ _ e => containsSorry e
  | _ => false

/-- Fully instantiate and check a candidate at the final trust boundary. -/
def finalizeProof (target proof : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  if containsSorry proof then
    throwError "ViaLean rejected a proof containing sorryAx"
  -- Type inference solves universe constraints introduced by reconstructed constants.
  discard <| inferType proof
  let proof ← instantiateMVars proof
  let inferred ← instantiateMVars (← inferType proof)
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
