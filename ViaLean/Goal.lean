import ViaLean.Basic

open Lean Meta

namespace ViaLean

inductive GoalShape
  | equality | iff | conjunction | forall | exists | structure
  | proposition | data | other
deriving BEq, Hashable, Repr, Inhabited

structure LocalInfo where
  fvarId   : FVarId
  userName : Name
  type     : Expr
  isLet    : Bool := false

structure GoalSnapshot where
  goalId      : MVarId
  target      : Expr
  locals      : Array LocalInfo
  targetSize  : Nat
  localCount  : Nat
  shape       : GoalShape
  fingerprint : UInt64

def classifyTarget (target : Expr) : MetaM GoalShape := do
  let target ← whnf target
  if target.isAppOf ``Eq then return .equality
  if target.isAppOf ``Iff then return .iff
  if target.isAppOf ``And then return .conjunction
  if target.isAppOf ``Exists then return .exists
  if target.isForall then return .forall
  let fn := target.getAppFn
  if let .const name _ := fn then
    if isStructure (← getEnv) name then return .structure
  let sort ← whnf (← inferType target)
  if sort.isProp then return .proposition
  if sort.isSort then return .data
  return .other

def snapshot (goal : MVarId) : MetaM GoalSnapshot := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let lctx ← getLCtx
  let mut locals := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      locals := locals.push {
        fvarId := decl.fvarId
        userName := decl.userName
        type := ← instantiateMVars decl.type
        isLet := decl.isLet
      }
  let fingerprint := locals.foldl (fun acc info => hash (acc, hash info.type)) (hash target)
  pure {
    goalId := goal
    target
    locals
    targetSize := exprSize target
    localCount := locals.size
    shape := ← classifyTarget target
    fingerprint
  }

end ViaLean
