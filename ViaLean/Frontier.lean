import ViaLean.Config
import ViaLean.Goal
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Simp.Attr

open Lean Meta

namespace ViaLean

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
    let groups := #[normalization, contradiction, rewrites, elimination,
      construction, backward, forward, equality]
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
