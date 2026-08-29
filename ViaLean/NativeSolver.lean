import ViaLean.Trace
import ViaLean.Solver.Basic
import ViaLean.Validate
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Simp.Attr

open Lean Meta

namespace ViaLean

structure NativeStats where
  nodes                  : Nat := 0
  attemptedApplications  : Nat := 0
  successfulApplications : Nat := 0
  attemptedTransforms    : Nat := 0
  successfulTransforms   : Nat := 0
deriving Inhabited

structure NativeAttempt where
  proof?    : Option Expr := none
  stats     : NativeStats := {}
  elapsedMs : Nat := 0
deriving Inhabited

private structure NativeContext where
  config     : ProposeConfig
  deadlineMs : Nat
  stats      : IO.Ref NativeStats
  premises   : Array Name

private def NativeContext.beforeDeadline (ctx : NativeContext) : MetaM Bool := do
  return (← IO.monoMsNow) < ctx.deadlineMs

private def goalKey (goal : MVarId) : MetaM UInt64 := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let mut key := hash target
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      key := hash (key, hash (← instantiateMVars decl.type))
  return key

private def exactLocal? (goal : MVarId) (target : Expr) : MetaM Bool := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isDefEq decl.type target then
        goal.assign (mkFVar decl.fvarId)
        return true
  return false

private def constructorsFor (target : Expr) : MetaM (Array Name) := do
  let target ← whnf target
  let .const name _ := target.getAppFn | return #[]
  match (← getEnv).find? name with
  | some (.inductInfo info) => return info.ctors.toArray
  | _ => return #[]

mutual
  private partial def solveNativeGoals
      (goals : List MVarId) (ctx : NativeContext) (depth : Nat)
      (path : Std.HashSet UInt64) : MetaM Bool := do
    for child in goals do
      unless ← solveNativeGoal child ctx depth path do
        return false
    return true

  private partial def tryApply
      (goal : MVarId) (candidate : Expr) (ctx : NativeContext) (depth : Nat)
      (path : Std.HashSet UInt64) : MetaM Bool := do
    let current ← ctx.stats.get
    if current.attemptedApplications ≥ ctx.config.nativeMaxApplications then return false
    let saved ← saveState
    ctx.stats.modify fun s =>
      { s with attemptedApplications := s.attemptedApplications + 1 }
    try
      let children ← goal.apply candidate
      if children.length > ctx.config.maxStructuralChildren then
        saved.restore
        return false
      if ← solveNativeGoals children ctx (depth + 1) path then
        ctx.stats.modify fun s =>
          { s with successfulApplications := s.successfulApplications + 1 }
        return true
      saved.restore
      return false
    catch _ =>
      saved.restore
      return false

  private partial def tryContradiction
      (goal : MVarId) (ctx : NativeContext) : MetaM Bool := do
    let saved ← saveState
    ctx.stats.modify fun s => { s with attemptedTransforms := s.attemptedTransforms + 1 }
    try
      goal.contradiction
      ctx.stats.modify fun s => { s with successfulTransforms := s.successfulTransforms + 1 }
      return true
    catch _ =>
      saved.restore
      return false

  private partial def trySimp
      (goal : MVarId) (ctx : NativeContext) (depth : Nat)
      (path : Std.HashSet UInt64) : MetaM Bool := do
    let saved ← saveState
    ctx.stats.modify fun s => { s with attemptedTransforms := s.attemptedTransforms + 1 }
    try
      let simpCtx ← Simp.Context.mkDefault
      let (result, _) ← simpTargetStar goal simpCtx
      match result with
      | .closed =>
          ctx.stats.modify fun s => { s with successfulTransforms := s.successfulTransforms + 1 }
          return true
      | .modified child =>
          if ← solveNativeGoal child ctx (depth + 1) path then
            ctx.stats.modify fun s => { s with successfulTransforms := s.successfulTransforms + 1 }
            return true
          saved.restore
          return false
      | .noChange =>
          saved.restore
          return false
    catch _ =>
      saved.restore
      return false

  private partial def tryCases
      (goal : MVarId) (ctx : NativeContext) (depth : Nat)
      (path : Std.HashSet UInt64) : MetaM Bool := do
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        let type ← instantiateMVars decl.type
        if (← isProp type) && !type.isEq && !type.isHEq then
          let saved ← saveState
          ctx.stats.modify fun s => { s with attemptedTransforms := s.attemptedTransforms + 1 }
          try
            let branches ← goal.cases decl.fvarId
            if branches.size > 0 && branches.size ≤ ctx.config.nativeMaxCaseBranches then
              if ← solveNativeGoals (branches.toList.map (·.mvarId)) ctx (depth + 1) path then
                ctx.stats.modify fun s => { s with successfulTransforms := s.successfulTransforms + 1 }
                return true
            saved.restore
          catch _ => saved.restore
    return false

  private partial def solveNativeGoal
      (goal : MVarId) (ctx : NativeContext) (depth : Nat)
      (path : Std.HashSet UInt64) : MetaM Bool := do
    if ← goal.isAssigned then return true
    if depth > ctx.config.nativeMaxDepth || !(← ctx.beforeDeadline) then return false
    ctx.stats.modify fun s => { s with nodes := s.nodes + 1 }
    goal.withContext do
      let key ← goalKey goal
      if path.contains key then return false
      let path := path.insert key
      let target ← instantiateMVars (← goal.getType)

      if ← exactLocal? goal target then return true
      if let some (_, lhs, rhs) := eqTarget? target then
        if ← isDefEq lhs rhs then
          goal.assign (← mkEqRefl lhs)
          return true
      if target.isConstOf ``True then
        goal.assign (mkConst ``True.intro)
        return true

      if ctx.config.nativeTransforms then
        if ← tryContradiction goal ctx then return true
        if ← trySimp goal ctx depth path then return true

      if target.isForall then
        let saved ← saveState
        try
          let (_, child) ← goal.intro1P
          if ← solveNativeGoal child ctx (depth + 1) path then return true
          saved.restore
        catch _ => saved.restore

      for ctor in ← constructorsFor target do
        if !(← ctx.beforeDeadline) then return false
        if ← tryApply goal (← mkConstWithFreshMVarLevels ctor) ctx depth path then
          return true

      for decl in ← getLCtx do
        unless decl.isImplementationDetail do
          if !(← ctx.beforeDeadline) then return false
          if ← tryApply goal (mkFVar decl.fvarId) ctx depth path then
            return true

      if ctx.config.nativeTransforms && ctx.config.nativeCases then
        if ← tryCases goal ctx depth path then return true

      for premise in ctx.premises do
        if !(← ctx.beforeDeadline) then return false
        try
          if ← tryApply goal (← mkConstWithFreshMVarLevels premise) ctx depth path then
            return true
        catch _ => pure ()
      return false
end

def searchProofExpr
    (contextGoal : MVarId) (target : Expr) (cfg : ProposeConfig)
    (budgetMs : Nat) (extraPremises : Array Name := #[]) : MetaM NativeAttempt := do
  if budgetMs = 0 then return {}
  contextGoal.withContext do
    let started ← IO.monoMsNow
    let stats ← IO.mkRef ({} : NativeStats)
    let saved ← getMCtx
    try
      let fresh ← mkFreshExprSyntheticOpaqueMVar target
      let goal := fresh.mvarId!
      let ctx : NativeContext := {
        config := cfg
        deadlineMs := started + budgetMs
        stats := stats
        premises := extraPremises
      }
      let solved ← solveNativeGoal goal ctx 0 {}
      let proof? ← if solved then
        match ← getExprMVarAssignment? goal with
        | some proof => do
            let finalized ← finalizeProof target proof
            pure (some finalized)
        | none => pure none
      else pure none
      let finalStats ← stats.get
      let finished ← IO.monoMsNow
      let result : NativeAttempt := {
        proof? := proof?
        stats := finalStats
        elapsedMs := finished - started
      }
      setMCtx saved
      return result
    catch error =>
      setMCtx saved
      throw error

def solveWithNative
    (goal : MVarId) (cfg : ProposeConfig) (budgetMs : Nat)
    (extraPremises : Array Name := #[]) : MetaM NativeAttempt := do
  searchProofExpr goal (← goal.getType) cfg budgetMs extraPremises

def nativeLeafSolver (cfg : ProposeConfig) : LeafSolver where
  kind := .native
  solve request := do
    let result ← solveWithNative request.goal cfg request.budgetMs request.extraPremises
    pure {
      backend := .native
      proof? := result.proof?
      solved := result.proof?.isSome
      elapsedMs := result.elapsedMs
      progress := if result.proof?.isSome then 1.0 else 0.0
      diagnostics? := if request.wantDiagnostics then
        some s!"nodes={result.stats.nodes}, applications={result.stats.attemptedApplications}, transforms={result.stats.successfulTransforms}/{result.stats.attemptedTransforms}"
      else none
    }

end ViaLean
