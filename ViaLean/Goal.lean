import ViaLean.GoalKey

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
  value?   : Option Expr := none

/-- Dataset-independent structural features of a proof state. These cheap,
kernel-side measurements contain no theorem names, numeral identities, or
benchmark labels, so they can drive either symbolic search or a learned model. -/
structure GoalMetrics where
  targetSize   : Nat := 0
  targetDepth  : Nat := 0
  binders      : Nat := 0
  logicalNodes : Nat := 0
  metavars     : Nat := 0
  localFacts   : Nat := 0
  localData    : Nat := 0
  localSize    : Nat := 0
  difficulty   : Float := 1.0
deriving Inhabited, Repr

private partial def expressionDepth : Expr → Nat
  | .app fn arg => 1 + max (expressionDepth fn) (expressionDepth arg)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      1 + max (expressionDepth domain) (expressionDepth body)
  | .letE _ type value body _ =>
      1 + max (expressionDepth type) (max (expressionDepth value) (expressionDepth body))
  | .mdata _ body | .proj _ _ body => 1 + expressionDepth body
  | _ => 1

private partial def binderNodes : Expr → Nat
  | .app fn arg => binderNodes fn + binderNodes arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      1 + binderNodes domain + binderNodes body
  | .letE _ type value body _ =>
      1 + binderNodes type + binderNodes value + binderNodes body
  | .mdata _ body | .proj _ _ body => binderNodes body
  | _ => 0

private partial def logicalNodeCount : Expr → Nat
  | .const name _ =>
      if name == ``And || name == ``Or || name == ``Iff || name == ``Exists ||
          name == ``Not || name == ``Eq || name == ``HEq then 1 else 0
  | .app fn arg => logicalNodeCount fn + logicalNodeCount arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      1 + logicalNodeCount domain + logicalNodeCount body
  | .letE _ type value body _ =>
      logicalNodeCount type + logicalNodeCount value + logicalNodeCount body
  | .mdata _ body | .proj _ _ body => logicalNodeCount body
  | _ => 0

private partial def metavariableCount : Expr → Nat
  | .mvar _ => 1
  | .app fn arg => metavariableCount fn + metavariableCount arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      metavariableCount domain + metavariableCount body
  | .letE _ type value body _ =>
      metavariableCount type + metavariableCount value + metavariableCount body
  | .mdata _ body | .proj _ _ body => metavariableCount body
  | _ => 0

private def metricDifficulty (targetSize targetDepth binders logicalNodes metavars
    localFacts localData localSize : Nat) : Float :=
  1.0 + Float.ofNat targetSize / 12.0 + Float.ofNat targetDepth / 4.0 +
    Float.ofNat binders * 0.45 + Float.ofNat logicalNodes * 0.35 +
    Float.ofNat metavars * 0.75 + Float.ofNat localFacts * 0.30 +
    Float.ofNat localData * 0.12 + Float.ofNat localSize / 80.0

structure GoalSnapshot where
  goalId      : MVarId
  target      : Expr
  locals      : Array LocalInfo
  targetSize  : Nat
  localCount  : Nat
  shape       : GoalShape
  key         : GoalKey
  fingerprint : UInt64
  metrics     : GoalMetrics := {}

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
  let mut localFacts := 0
  let mut localData := 0
  let mut localSize := 0
  for decl in lctx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      localSize := localSize + exprSize type
      if ← isProp type then localFacts := localFacts + 1
      else localData := localData + 1
      locals := locals.push {
        fvarId := decl.fvarId
        userName := decl.userName
        type
        isLet := decl.isLet
        value? := ← decl.value? (allowNondep := true).mapM instantiateMVars
      }
  let key ← mkGoalKey goal
  let targetSize := exprSize target
  let targetDepth := expressionDepth target
  let binders := binderNodes target
  let logicalNodes := logicalNodeCount target
  let metavars := metavariableCount target
  let metrics : GoalMetrics := {
    targetSize, targetDepth, binders, logicalNodes, metavars,
    localFacts, localData, localSize
    difficulty := metricDifficulty targetSize targetDepth binders logicalNodes metavars
      localFacts localData localSize
  }
  pure {
    goalId := goal
    target
    locals
    targetSize
    localCount := locals.size
    shape := ← classifyTarget target
    key
    fingerprint := key.bucket
    metrics
  }

end ViaLean
