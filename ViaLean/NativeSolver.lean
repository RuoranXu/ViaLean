import ViaLean.Trace
import ViaLean.Solver.Basic
import ViaLean.Validate
import ViaLean.Transport
import ViaLean.Induction
import ViaLean.Search.Execute
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Rewrite
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

/-- Eager `simpTargetStar`/`cases` can enter long kernel traversals when the
local context contains higher-order propositions. Those goals remain available
to ordinary application and structural search, but not to eager transforms. -/
private partial def containsConstName (needle : Name) : Expr → Bool
  | .const name _ => name == needle
  | .app fn arg => containsConstName needle fn || containsConstName needle arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsConstName needle domain || containsConstName needle body
  | .letE _ type value body _ =>
      containsConstName needle type || containsConstName needle value ||
        containsConstName needle body
  | .mdata _ body | .proj _ _ body => containsConstName needle body
  | _ => false

private def targetBenefitsFromPremiseRewrite (target : Expr) : Bool :=
  match eqTarget? target with
  | some (_, lhs, rhs) => !(lhs.isFVar && rhs.isFVar)
  | none => true

private def safeForEagerTransforms (target : Expr) : MetaM Bool := do
  let target ← instantiateMVars target
  if target.isForall || containsConstName ``Exists target then return false
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      if (← isProp type) && (type.isForall || containsConstName ``Exists type) then
        return false
  return true

/-- Build a small, target-connected rewrite context. Starting from the free
variables visible in the target, follow at most three layers of local `Eq`/`Iff`
facts. This preserves useful definitional chains without giving `simp` every
proposition in the local context. -/
def targetConnectedRewriteContext (target : Expr) : MetaM (Simp.Context × Nat) := do
  let mut relevant := (collectFVars {} target).fvarIds
  let mut rewrites : Array FVarId := #[]
  for _ in [0:3] do
    let mut changed := false
    for decl in ← getLCtx do
      unless decl.isImplementationDetail || rewrites.contains decl.fvarId do
        let type ← instantiateMVars decl.type
        if type.isEq || type.isAppOfArity ``Iff 2 then
          let used := (collectFVars {} type).fvarIds
          if used.any relevant.contains then
            rewrites := rewrites.push decl.fvarId
            for fvarId in used do
              unless relevant.contains fvarId do
                relevant := relevant.push fvarId
                changed := true
    unless changed do break
  let mut ctx ← Simp.mkContext
    (simpTheorems := {}) (congrTheorems := (← getSimpCongrTheorems))
  let mut theorems := ctx.simpTheorems
  for fvarId in rewrites do
    theorems ← theorems.addTheorem (.fvar fvarId) (mkFVar fvarId)
      (config := ctx.indexConfig)
  ctx := ctx.setSimpTheorems theorems
  return (ctx, rewrites.size)

private def hasLocalProposition : MetaM Bool := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp (← instantiateMVars decl.type) then
        return true
  return false

mutual  private partial def solveNativeGoals
      (goals : List MVarId) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
    for child in goals do
      unless ← solveNativeGoal child ctx depth path do
        return false
    return true

  private partial def tryApply
      (goal : MVarId) (candidate : Expr) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
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
      (path : StrictGoalSet) : MetaM Bool := do
    let saved ← saveState
    ctx.stats.modify fun s => { s with attemptedTransforms := s.attemptedTransforms + 1 }
    try
      let target ← instantiateMVars (← goal.getType)
      let (connectedCtx, rewriteCount) ← targetConnectedRewriteContext target
      -- Premise-free computational identities benefit from the environment's
      -- ordinary simp lemmas. Once propositions enter the local context, stay
      -- with the small target-connected closure: importing a large library
      -- must not turn one native transform into an unbounded global sweep.
      let simpCtx ←
        if rewriteCount == 0 && !(← hasLocalProposition) then
          Simp.Context.mkDefault
        else
          pure connectedCtx
      let (child?, _) ← ExecutionBoundary.withoutSpeculativeMessages <|
        simpTarget goal simpCtx
      match child? with
      | none =>
          ctx.stats.modify fun s => { s with successfulTransforms := s.successfulTransforms + 1 }
          return true
      | some child =>
          let childTarget ← instantiateMVars (← child.getType)
          if childTarget == target then
            saved.restore
            return false
          if ← solveNativeGoal child ctx (depth + 1) path then
            ctx.stats.modify fun s => { s with successfulTransforms := s.successfulTransforms + 1 }
            return true
          saved.restore
          return false
    catch error =>
      if error.isInterrupt then throw error
      saved.restore
      return false

  private partial def tryCases
      (goal : MVarId) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        let type ← instantiateMVars decl.type
        let constructors ← constructorsFor type
        if (← isProp type) && !type.isEq && !type.isHEq && !constructors.isEmpty then
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

  /-- Rewrite with retrieved equality theorems before branching further. Lean's
  rewrite primitive instantiates theorem parameters and returns any genuine
  side conditions, which are solved by the same recursive search. -/
  private partial def tryPremiseRewrites
      (goal : MVarId) (target : Expr) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
    -- `ctx.premises` is already bounded by `maxRetrievedPremises`. Do not
    -- apply the narrower proposal-family cap here: this is the semantic
    -- rewrite closure inside proof branches, not a visible candidate list.
    for premise in ctx.premises do
      if !(← ctx.beforeDeadline) then return false
      let saved ← saveState
      ctx.stats.modify fun s =>
        { s with attemptedTransforms := s.attemptedTransforms + 1 }
      try
        let theoremExpr ← mkConstWithFreshMVarLevels premise
        let result ← goal.rewrite target theoremExpr
        let child ← goal.replaceTargetEq result.eNew result.eqProof
        let children := result.mvarIds ++ [child]
        if children.length ≤ ctx.config.maxStructuralChildren &&
            (← solveNativeGoals children ctx (depth + 1) path) then
          ctx.stats.modify fun s =>
            { s with successfulTransforms := s.successfulTransforms + 1 }
          return true
        saved.restore
      catch _ => saved.restore
    return false

  /-- Transport bounded local equalities through local equivalences, normalize
  the resulting kernel term, and try it as a rewrite in both directions. This
  changes only the target, avoiding whole-context simplifier blowups. -/
  private partial def tryEquivTransports
      (goal : MVarId) (target : Expr) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
    let limit := ctx.config.maxCandidatesPerFamily
    let facts ← equivTransportFacts limit (2 * limit * limit)
      ctx.config.maxProposalSize
    trace[ViaLean.native] "equiv transport facts={facts.size}"
    for fact in facts do
      if !(← ctx.beforeDeadline) then return false
      let saved ← saveState
      trace[ViaLean.native] "equiv transport fact: {fact.type}"
      ctx.stats.modify fun s =>
        { s with attemptedTransforms := s.attemptedTransforms + 1 }
      for symm in #[false, true] do
        let branchSaved ← saveState
        try
          let result ← goal.rewrite target fact.proof symm
          let child ← goal.replaceTargetEq result.eNew result.eqProof
          let children := result.mvarIds ++ [child]
          if children.length ≤ ctx.config.maxStructuralChildren &&
              (← solveNativeGoals children ctx (depth + 1) path) then
            ctx.stats.modify fun s =>
              { s with successfulTransforms := s.successfulTransforms + 1 }
            return true
          branchSaved.restore
        catch _ => branchSaved.restore
      saved.restore
    return false

  /-- Explore structural induction as one semantic transformation. The
  recursor is recovered from the local's type, so this works for user-defined
  recursive data just as it does for the standard library. -/
  private partial def tryInduction
      (goal : MVarId) (target : Expr) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
    let lctx ← getLCtx
    for fvarId in lctx.getFVarIds.reverse do
      let decl := lctx.get! fvarId
      unless decl.isImplementationDetail do
        if !(← ctx.beforeDeadline) then return false
        let type ← instantiateMVars decl.type
        if !(← isProp type) && (← targetBenefitsFromInduction target decl.fvarId) then
          let some recursor ← inductionRecursor? type | continue
          let saved ← saveState
          ctx.stats.modify fun s =>
            { s with attemptedTransforms := s.attemptedTransforms + 1 }
          try
            let branches ← goal.induction decl.fvarId recursor
            if branches.size > 0 && branches.size ≤ ctx.config.nativeMaxCaseBranches then
              if ← solveNativeGoals (branches.toList.map (·.mvarId)) ctx (depth + 1) path then
                ctx.stats.modify fun s =>
                  { s with successfulTransforms := s.successfulTransforms + 1 }
                return true
            saved.restore
          catch _ => saved.restore
    return false

  private partial def solveNativeGoal
      (goal : MVarId) (ctx : NativeContext) (depth : Nat)
      (path : StrictGoalSet) : MetaM Bool := do
    if ← goal.isAssigned then return true
    if depth > ctx.config.nativeMaxDepth || !(← ctx.beforeDeadline) then return false
    ctx.stats.modify fun s => { s with nodes := s.nodes + 1 }
    goal.withContext do
      let key ← mkGoalKey goal
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

      let eagerTransformsSafe ← safeForEagerTransforms target
      if ctx.config.nativeEquivTransport && eagerTransformsSafe then
        if ← tryEquivTransports goal target ctx depth path then return true

      if ctx.config.nativeTransforms && eagerTransformsSafe then
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

      if ctx.config.nativeTransforms && !ctx.premises.isEmpty &&
          targetBenefitsFromPremiseRewrite target then
        if ← tryPremiseRewrites goal target ctx depth path then return true

      if ctx.config.nativeTransforms && ctx.config.nativeInduction then
        if ← tryInduction goal target ctx depth path then return true

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
