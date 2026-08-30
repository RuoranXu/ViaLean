import ViaLean.Config
import ViaLean.Goal
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Simp.Attr

open Lean Meta

namespace ViaLean

/-- One bounded node in the multi-step symbolic future visible to the model. -/
structure SymbolicFutureView where
  depth   : Nat
  path    : String
  goal    : String
  signals : Array String := #[]
deriving Inhabited, Repr

/-- A bounded, non-scoring symbolic preview of one possible near-future view. -/
structure FrontierProbe where
  id          : String
  perspective : String
  operation   : String
  source      : String
  result      : String
  executable  : Bool := false
  subject?    : Option FVarId := none
  constructor? : Option Name := none
  symm        : Bool := false
  goals       : Array String := #[]
  facts       : Array String := #[]
  future      : Array SymbolicFutureView := #[]
deriving Inhabited, Repr

namespace FrontierEngine

private def bounded (limit : Nat) (text : String) : String :=
  if text.length ≤ limit then text else (text.take limit).toString ++ "…"

private def renderExpr (expr : Expr) (limit : Nat) : MetaM String := do
  return bounded limit (← ppExpr (← instantiateMVars expr)).pretty

private def renderGoal (goal : MVarId) (limit : Nat) : MetaM String :=
  goal.withContext do
    let mut lines : Array String := #[]
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        lines := lines.push s!"{decl.userName} : {← renderExpr decl.type limit}"
    let target := bounded (max 16 (limit / 2)) (← renderExpr (← goal.getType) limit)
    let header := s!"⊢ {target}"
    let contextLimit := limit - min limit (header.length + 1)
    let context := bounded contextLimit (String.intercalate "\n" lines.reverse.toList)
    return if context.isEmpty then bounded limit header
      else bounded limit (header ++ "\n" ++ context)

private def renderGoals
    (goals : Array MVarId) (maxChildren chars : Nat) : MetaM (Array String) := do
  let mut result := #[]
  for goal in goals.take maxChildren do
    result := result.push (← renderGoal goal chars)
  return result

private def makeProbe
    (perspective operation source result : String)
    (goals facts : Array String := #[]) : FrontierProbe := {
  id := toString (hash (perspective, operation, source, result, goals, facts))
  perspective
  operation
  source
  result
  executable := perspective != "forward" && perspective != "equality-graph"
  goals
  facts
}

private def budgetOpen (budget? : Option Budget) : MetaM Bool :=
  match budget? with
  | none => pure true
  | some budget => return (← budget.remainingMs) > 0

/-- Execute a preview under full metavariable rollback and retain rendered data only. -/
private def observingProbe? (budget? : Option Budget)
    (action : MetaM (Option FrontierProbe)) : MetaM (Option FrontierProbe) := do
  unless ← budgetOpen budget? do return none
  let saved ← saveState
  try
    let result ← action
    saved.restore
    if ← budgetOpen budget? then return result else return none
  catch _ =>
    saved.restore
    return none

private def freshGoal (target : Expr) : MetaM MVarId := do
  return (← mkFreshExprSyntheticOpaqueMVar target).mvarId!

private def constructorsFor (target : Expr) : MetaM (Array Name) := do
  let target ← whnf target
  let .const name _ := target.getAppFn | return #[]
  match (← getEnv).find? name with
  | some (.inductInfo info) => return info.ctors.toArray
  | _ => return #[]

private def futureKey (goal : MVarId) : MetaM UInt64 := goal.withContext do
  let mut key := hash (← instantiateMVars (← goal.getType))
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      key := hash (key, hash (← instantiateMVars decl.type))
  return key

private def pushFutureSignal
    (signals : Array String) (cfg : ProposeConfig) (signal : String) : Array String :=
  if signals.size < cfg.frontierMaxFacts then signals.push signal else signals

private def futureSignals
    (goal : MVarId) (cfg : ProposeConfig) (chars : Nat) : MetaM (Array String) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let mut signals := #[]
    if target.isForall then
      signals := pushFutureSignal signals cfg "intro exposes a deeper local context"
    if target.isEq || target.isHEq then
      signals := pushFutureSignal signals cfg
        "equality reasoning and bidirectional rewriting are available"
    for ctor in ← constructorsFor target do
      signals := pushFutureSignal signals cfg s!"constructor {ctor} exposes coupled obligations"
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        if signals.size < cfg.frontierMaxFacts then
          let type ← instantiateMVars decl.type
          let saved ← saveState
          let closes ← try isDefEq type target catch _ => pure false
          saved.restore
          if closes then
            signals := pushFutureSignal signals cfg s!"exact local {decl.userName} closes this node"
          if type.isEq || type.isHEq then
            signals := pushFutureSignal signals cfg s!"rewrite source {decl.userName}"
          match ← whnf type with
          | .forallE _ _ _ _ =>
            signals := pushFutureSignal signals cfg s!"backward application candidate {decl.userName}"
          | _ =>
            if (← isProp type) && !type.isEq && !type.isHEq then
              signals := pushFutureSignal signals cfg s!"elimination candidate {decl.userName}"
    let reduced ← whnf target
    unless reduced == target do
      signals := pushFutureSignal signals cfg
        s!"normalization changes target to {← renderExpr reduced chars}"
    return signals

private def observingFuture (action : MetaM (Array SymbolicFutureView)) : MetaM (Array SymbolicFutureView) := do
  let saved ← saveState
  try
    let result ← action
    saved.restore
    return result
  catch _ =>
    saved.restore
    return #[]

mutual
  private partial def exploreFutureChildren
      (children : Array MVarId) (depth : Nat) (path operation : String)
      (cfg : ProposeConfig) (chars : Nat) (budget? : Option Budget)
      (count : IO.Ref Nat) (seen : Std.HashSet UInt64) : MetaM (Array SymbolicFutureView) := do
    if children.isEmpty then
      if (← count.get) ≥ cfg.frontierFutureNodes || !(← budgetOpen budget?) then return #[]
      count.modify (· + 1)
      let closed : SymbolicFutureView := {
        depth := depth
        path := path ++ "/" ++ operation
        goal := "closed"
        signals := #["symbolic transform closes this branch"]
      }
      return #[closed]
    let mut result := #[]
    for index in [0:children.size] do
      if (← count.get) ≥ cfg.frontierFutureNodes || !(← budgetOpen budget?) then break
      let child := children[index]!
      unless ← child.isAssigned do
        result := result ++ (← exploreFutureGoal child depth
          s!"{path}/{operation}[{index}]" cfg chars budget? count seen)
    return result

  private partial def exploreFutureGoal
      (goal : MVarId) (depth : Nat) (path : String)
      (cfg : ProposeConfig) (chars : Nat) (budget? : Option Budget)
      (count : IO.Ref Nat) (seen : Std.HashSet UInt64) : MetaM (Array SymbolicFutureView) := do
    if depth > cfg.frontierFutureDepth || (← count.get) ≥ cfg.frontierFutureNodes ||
        !(← budgetOpen budget?) || (← goal.isAssigned) then return #[]
    goal.withContext do
      let key ← futureKey goal
      if seen.contains key then return #[]
      let seen := seen.insert key
      count.modify (· + 1)
      let view : SymbolicFutureView := {
        depth
        path
        goal := ← renderGoal goal chars
        signals := ← futureSignals goal cfg chars
      }
      if depth = cfg.frontierFutureDepth then return #[view]
      let target ← instantiateMVars (← goal.getType)
      let mut result := #[view]
      let mut expanded := 0

      if expanded < cfg.frontierFutureWidth && target.isForall then
        let branch ← observingFuture do
          let clone ← freshGoal target
          let (_, child) ← clone.intro1P
          exploreFutureChildren #[child] (depth + 1) path "intro" cfg chars budget? count seen
        unless branch.isEmpty do
          expanded := expanded + 1
          result := result ++ branch

      if expanded < cfg.frontierFutureWidth then
        let branch ← observingFuture do
          let clone ← freshGoal target
          let simpCtx ← Simp.Context.mkDefault
          let (simpResult, _) ← simpTargetStar clone simpCtx
          match simpResult with
          | .closed => exploreFutureChildren #[] (depth + 1) path "simp" cfg chars budget? count seen
          | .modified child => exploreFutureChildren #[child] (depth + 1) path "simp" cfg chars budget? count seen
          | .noChange => return #[]
        unless branch.isEmpty do
          expanded := expanded + 1
          result := result ++ branch

      let mut locals : Array LocalDecl := #[]
      for decl in ← getLCtx do
        unless decl.isImplementationDetail do
          locals := locals.push decl
      for decl in locals do
        if expanded ≥ cfg.frontierFutureWidth then break
        let branch ← observingFuture do
          let clone ← freshGoal target
          let children ← clone.apply (mkFVar decl.fvarId)
          if children.length > cfg.frontierMaxChildren then return #[]
          exploreFutureChildren children.toArray (depth + 1) path
            s!"apply:{decl.userName}" cfg chars budget? count seen
        unless branch.isEmpty do
          expanded := expanded + 1
          result := result ++ branch

      for ctor in ← constructorsFor target do
        if expanded ≥ cfg.frontierFutureWidth then break
        let branch ← observingFuture do
          let clone ← freshGoal target
          let children ← clone.apply (← mkConstWithFreshMVarLevels ctor)
          if children.length > cfg.frontierMaxChildren then return #[]
          exploreFutureChildren children.toArray (depth + 1) path
            s!"constructor:{ctor}" cfg chars budget? count seen
        unless branch.isEmpty do
          expanded := expanded + 1
          result := result ++ branch

      for decl in locals do
        if expanded ≥ cfg.frontierFutureWidth then break
        let type ← instantiateMVars decl.type
        if (← isProp type) && !type.isEq && !type.isHEq then
          let branch ← observingFuture do
            let clone ← freshGoal target
            let branches ← clone.cases decl.fvarId
            if branches.isEmpty || branches.size > cfg.frontierMaxChildren then return #[]
            exploreFutureChildren (branches.map (·.mvarId)) (depth + 1) path
              s!"cases:{decl.userName}" cfg chars budget? count seen
          unless branch.isEmpty do
            expanded := expanded + 1
            result := result ++ branch

      for decl in locals do
        if expanded ≥ cfg.frontierFutureWidth then break
        if decl.type.isEq then
          for symm in #[false, true] do
            if expanded ≥ cfg.frontierFutureWidth then break
            let direction := if symm then "reverse" else "forward"
            let branch ← observingFuture do
              let clone ← freshGoal target
              let rewriteResult ← clone.rewrite target (mkFVar decl.fvarId) (symm := symm)
              let child ← clone.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
              exploreFutureChildren (#[child] ++ rewriteResult.mvarIds) (depth + 1) path
                s!"rewrite:{decl.userName}:{direction}"
                cfg chars budget? count seen
            unless branch.isEmpty do
              expanded := expanded + 1
              result := result ++ branch
      return result

end

private def deepFutureProbe?
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Option FrontierProbe) := do
  if cfg.frontierFutureDepth = 0 || cfg.frontierFutureNodes = 0 then return none
  let count ← IO.mkRef 0
  let future ← observingFuture <| exploreFutureGoal snap.goalId 0 "root"
    cfg chars budget? count {}
  if future.isEmpty then return none
  return some { (makeProbe "future-graph" "bounded-deep-symbolic-search"
    "multi-operator" "expanded") with executable := false, future }

private def normalizationProbes
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Array FrontierProbe) := do
  unless ← budgetOpen budget? do return #[]
  let mut probes := #[]
  let reduced ← whnf snap.target
  unless reduced == snap.target do
    probes := probes.push <| makeProbe "normalization" "whnf" "target" "changed"
      #[← renderExpr reduced chars]

  if let some probe ← observingProbe? budget? do
    let goal ← freshGoal snap.target
    let simpCtx ← Simp.Context.mkDefault
    let (result, _) ← simpTargetStar goal simpCtx
    match result with
    | .closed => return some { (makeProbe "normalization" "simp-target-star" "local propositions" "closed") with executable := true }
    | .modified child =>
        return some <| makeProbe "normalization" "simp-target-star" "local propositions" "changed"
          #[← renderGoal child chars]
    | .noChange => return none
  then probes := probes.push probe

  if let some probe ← observingProbe? budget? do
    let goal ← freshGoal snap.target
    let simpCtx ← Simp.Context.mkDefault
    let propHyps ← getPropHyps
    let (result?, _) ← simpGoal goal simpCtx (fvarIdsToSimp := propHyps)
    match result? with
    | none => return some { (makeProbe "normalization" "simp-context" "all proposition hypotheses" "closed") with executable := true }
    | some (_, child) =>
        let target ← renderGoal child chars
        let facts ← child.withContext do
          let mut facts := #[]
          for decl in ← getLCtx do
            unless decl.isImplementationDetail do
              if ← isProp decl.type then
                if facts.size < cfg.frontierMaxFacts then
                  facts := facts.push s!"{decl.userName} : {← renderExpr decl.type chars}"
          return facts
        if target == (← renderExpr snap.target chars) then return none
        return some <| makeProbe "normalization" "simp-context" "all proposition hypotheses" "changed"
          #[target] facts
  then probes := probes.push probe
  return probes

private def contradictionProbes
    (snap : GoalSnapshot) (budget? : Option Budget) : MetaM (Array FrontierProbe) := do
  if let some probe ← observingProbe? budget? do
    let goal ← freshGoal snap.target
    goal.contradiction
    return some { (makeProbe "consistency" "contradiction-core" "local context" "closed") with executable := true }
  then return #[probe]
  return #[]

private def rewriteProbes
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Array FrontierProbe) := do
  let mut probes := #[]
  for info in snap.locals do
    unless ← budgetOpen budget? do break
    if probes.size ≥ cfg.frontierMaxPerPerspective then break
    if info.type.isEq then
      for symm in #[false, true] do
        if probes.size ≥ cfg.frontierMaxPerPerspective then break
        if let some probe ← observingProbe? budget? do
          let goal ← freshGoal snap.target
          let result ← goal.rewrite snap.target (mkFVar info.fvarId) (symm := symm)
          let child ← goal.replaceTargetEq result.eNew result.eqProof
          let goals ← renderGoals (#[child] ++ result.mvarIds) cfg.frontierMaxChildren chars
          return some { (makeProbe "rewrite" (if symm then "rewrite-reverse" else "rewrite-forward")
            (toString info.userName) "changed" goals) with
            subject? := some info.fvarId, symm := symm }
        then probes := probes.push probe
  return probes

private def eliminationProbes
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Array FrontierProbe) := do
  let mut probes := #[]
  for info in snap.locals do
    unless ← budgetOpen budget? do break
    if probes.size ≥ cfg.frontierMaxPerPerspective then break
    if (← isProp info.type) && !info.type.isEq && !info.type.isHEq then
      if let some probe ← observingProbe? budget? do
        let goal ← freshGoal snap.target
        let branches ← goal.cases info.fvarId
        if branches.isEmpty || branches.size > cfg.frontierMaxChildren then return none
        let goals ← renderGoals (branches.map (·.mvarId)) cfg.frontierMaxChildren chars
        return some { (makeProbe "elimination" "cases-one-layer" (toString info.userName)
          "branched" goals) with subject? := some info.fvarId }
      then probes := probes.push probe
  return probes

private def constructionProbes
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Array FrontierProbe) := do
  let mut probes := #[]
  for ctor in ← constructorsFor snap.target do
    unless ← budgetOpen budget? do break
    if probes.size ≥ cfg.frontierMaxPerPerspective then break
    if let some probe ← observingProbe? budget? do
      let goal ← freshGoal snap.target
      let children ← goal.apply (← mkConstWithFreshMVarLevels ctor)
      if children.length > cfg.frontierMaxChildren then return none
      let goals ← renderGoals children.toArray cfg.frontierMaxChildren chars
      return some { (makeProbe "construction" "constructor-one-layer" (toString ctor)
        (if children.isEmpty then "closed" else "opened") goals) with constructor? := some ctor }
    then probes := probes.push probe
  return probes

private def backwardProbes
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Array FrontierProbe) := do
  let mut probes := #[]
  for info in snap.locals do
    unless ← budgetOpen budget? do break
    if probes.size ≥ cfg.frontierMaxPerPerspective then break
    if let some probe ← observingProbe? budget? do
      let goal ← freshGoal snap.target
      let children ← goal.apply (mkFVar info.fvarId)
      if children.length > cfg.frontierMaxChildren then return none
      let goals ← renderGoals children.toArray cfg.frontierMaxChildren chars
      return some { (makeProbe "backward" "apply-one-layer" (toString info.userName)
        (if children.isEmpty then "closed" else "opened") goals) with subject? := some info.fvarId }
    then probes := probes.push probe
  return probes

private structure DerivedTerm where
  expr   : Expr
  origin : String

private def forwardProbe?
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Option FrontierProbe) := do
  let mut pool : Array DerivedTerm := snap.locals.map fun info => {
    expr := mkFVar info.fvarId
    origin := toString info.userName
  }
  let mut frontier := pool
  let mut facts := #[]
  let mut seen : Std.HashSet UInt64 := {}
  for step in [0:cfg.frontierForwardDepth] do
    unless ← budgetOpen budget? do break
    if facts.size ≥ cfg.frontierMaxFacts then break
    let mut next := #[]
    for fnTerm in frontier do
      unless ← budgetOpen budget? do break
      if facts.size ≥ cfg.frontierMaxFacts then break
      let fnType ← whnf (← inferType fnTerm.expr)
      let .forallE _ domain _ _ := fnType | continue
      for argTerm in pool do
        unless ← budgetOpen budget? do break
        if facts.size ≥ cfg.frontierMaxFacts then break
        let saved ← saveState
        let compatible ← try
          isDefEq (← inferType argTerm.expr) domain
        catch _ => pure false
        if !compatible then
          saved.restore
          continue
        let derived := mkApp fnTerm.expr argTerm.expr
        let derivedType ← instantiateMVars (← inferType derived)
        saved.restore
        let key := hash (derivedType, fnTerm.origin, argTerm.origin)
        if seen.contains key then continue
        seen := seen.insert key
        let rendered := s!"{← renderExpr derived chars} : {← renderExpr derivedType chars}"
        facts := facts.push s!"step {step + 1}, {fnTerm.origin} ← {argTerm.origin}: {rendered}"
        next := next.push { expr := derived, origin := s!"({fnTerm.origin} {argTerm.origin})" }
    pool := pool ++ next
    frontier := next
    if frontier.isEmpty then break
  if facts.isEmpty then return none
  return some <| makeProbe "forward" "typed-local-closure" "local terms" "derived" #[] facts

private def equalityChainProbe?
    (snap : GoalSnapshot) (cfg : ProposeConfig) (chars : Nat)
    (budget? : Option Budget) : MetaM (Option FrontierProbe) := do
  let equalities := snap.locals.filter fun info => info.type.isEq
  let mut facts := #[]
  for left in equalities do
    unless ← budgetOpen budget? do break
    if facts.size ≥ cfg.frontierMaxFacts then break
    let some (_, _, leftRhs) := left.type.eq? | continue
    for right in equalities do
      unless ← budgetOpen budget? do break
      if facts.size ≥ cfg.frontierMaxFacts then break
      if left.fvarId == right.fvarId then continue
      let some (_, rightLhs, _) := right.type.eq? | continue
      let saved ← saveState
      let joins ← try isDefEq leftRhs rightLhs catch _ => pure false
      if !joins then
        saved.restore
        continue
      let proof ← mkEqTrans (mkFVar left.fvarId) (mkFVar right.fvarId)
      let type ← instantiateMVars (← inferType proof)
      saved.restore
      facts := facts.push s!"{left.userName} ; {right.userName} ⟹ {← renderExpr type chars}"
  if facts.isEmpty then return none
  return some <| makeProbe "equality-graph" "two-edge-transitive-closure" "local equalities"
    "derived" #[] facts

/-- Build a diversity-balanced atlas. Each probe is at most one tactic layer plus bounded local closure. -/
def build (snap : GoalSnapshot) (cfg : ProposeConfig)
    (budget? : Option Budget := none) : MetaM (Array FrontierProbe) :=
  snap.goalId.withContext do
    if !cfg.frontier || cfg.frontierMaxProbes = 0 || !(← budgetOpen budget?) then return #[]
    let slots := max 1 (cfg.frontierMaxProbes * (cfg.frontierMaxChildren + cfg.frontierMaxFacts + 1))
    let chars := max 64 (cfg.frontierContextChars / slots)
    let normalization ← normalizationProbes snap cfg chars budget?
    let contradiction ← contradictionProbes snap budget?
    let rewrites ← rewriteProbes snap cfg chars budget?
    let elimination ← eliminationProbes snap cfg chars budget?
    let construction ← constructionProbes snap cfg chars budget?
    let backward ← backwardProbes snap cfg chars budget?
    let forward := (← forwardProbe? snap cfg chars budget?).map (#[·]) |>.getD #[]
    let equality := (← equalityChainProbe? snap cfg chars budget?).map (#[·]) |>.getD #[]
    let deepFuture := (← deepFutureProbe? snap cfg chars budget?).map (#[·]) |>.getD #[]
    let groups := #[normalization, contradiction, rewrites, elimination,
      construction, backward, forward, equality, deepFuture]
    let mut atlas := #[]
    for index in [0:cfg.frontierMaxPerPerspective] do
      unless ← budgetOpen budget? do break
      for group in groups do
        if atlas.size ≥ cfg.frontierMaxProbes then break
        if let some probe := group[index]? then atlas := atlas.push probe
      if atlas.size ≥ cfg.frontierMaxProbes then break
    return atlas

end FrontierEngine
end ViaLean
