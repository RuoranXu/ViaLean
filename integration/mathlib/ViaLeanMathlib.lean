import ViaLean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.PowMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Normed.Group.Basic
import Aesop
import Qq
open Lean Parser Tactic Meta Elab Tactic
open Qq

namespace ViaLean.Mathlib

private structure TacticSpec where
  name : String
  code : String
  heartbeats : Nat := 3000000
  heartbeatScale : Nat := 1

/-- A small trusted mathlib portfolio. Each tactic runs as a leaf solver;
ViaLean still owns decomposition, scheduling, rollback, and final validation. -/
private def portfolio : Array TacticSpec := #[
  { name := "norm_num", code := "norm_num at *" },
  { name := "omega", code := "omega" },
  { name := "linarith", code := "linarith" },
  { name := "nlinarith", code := "nlinarith" },
  { name := "positivity", code := "positivity" },
  { name := "ring", code := "ring" },
  { name := "ring_nf", code := "ring_nf" },
  { name := "field_simp/nlinarith", code := "field_simp at * <;> ring_nf at * <;> nlinarith" }
]

private def targetPortfolio : Array TacticSpec := #[
  { name := "target/norm_num", code := "norm_num" },
  { name := "target/omega", code := "omega" },
  { name := "target/linarith", code := "linarith" },
  { name := "target/nlinarith", code := "nlinarith" },
  { name := "target/ring", code := "ring" },
  { name := "target/positivity", code := "positivity" }
]

/-- A symbolic case split contributes a verified local fact. Consume that fact
before generic arithmetic tactics so the selected transition remains visible. -/
private def caseSplitPortfolio : Array TacticSpec := #[
  { name := "case-simp", code := "simp_all" },
  { name := "case-simp/nlinarith", code := "simp_all <;> norm_num at * <;> nlinarith" },
  { name := "case-field/nlinarith",
    code := "simp_all <;> field_simp at * <;> ring_nf at * <;> nlinarith" }
]

/-- Higher-order contexts use a smaller deterministic leaf budget. Logical
opening still belongs to ViaLean's explicit structural transitions. -/
private def higherOrderPortfolio : Array TacticSpec := #[
  { name := "bounded-norm_num", code := "norm_num at *", heartbeats := 200000 },
  { name := "bounded-omega", code := "omega", heartbeats := 200000 },
  { name := "bounded-simp", code := "simp_all", heartbeats := 500000 },
  { name := "bounded-simp/nlinarith",
    code := "simp_all <;> norm_num at * <;> nlinarith", heartbeats := 500000 }
]
private def parseTrustedTactic (env : Environment) (code : String) : Except String Syntax := do
  let term ← Parser.runParserCategory env `term ("by\n  " ++ code)
  match term with
  | .node _ kind args =>
      unless kind.toString == "Lean.Parser.Term.byTactic" do
        throw "trusted tactic did not parse as a by-proof"
      let some tactics := args[1]?
        | throw "trusted tactic produced a malformed by-proof"
      return tactics
  | _ => throw "trusted tactic did not parse as a by-proof"

private def runClosedTactic
    (request : SolverRequest) (spec : TacticSpec) : MetaM (Except String Expr) :=
  request.goal.withContext do
    let saved ← saveState
    let _ : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try
      let target ← instantiateMVars (← request.goal.getType)
      let rootExpr ← mkFreshExprSyntheticOpaqueMVar target
      let root := rootExpr.mvarId!
      let tacticSyntax ← match parseTrustedTactic (← getEnv) spec.code with
        | .ok tactic => pure tactic
        | .error message => return .error s!"{spec.name}: {message}"
      let (remaining, _) ← ExecutionBoundary.withoutSpeculativeMessages <|
        withOptions (fun options => options.setNat `maxRecDepth 10000) do
          withTheReader Core.Context
            (fun context => {
              context with
                maxRecDepth := max context.maxRecDepth 10000
                -- Most portfolio leaves use cheap internal-tick budgets. Deep,
                -- shape-gated futures opt into Lean option units with scale 1000.
                maxHeartbeats := spec.heartbeats * spec.heartbeatScale }) do
              withCurrHeartbeats <| Elab.runTactic root tacticSyntax
      if !remaining.isEmpty then
        saved.restore
        return .error s!"{spec.name}: left {remaining.length} goals"
      let some proof ← getExprMVarAssignment? root
        | saved.restore
          return .error s!"{spec.name}: reported no goals without assigning the root"
      let proof ← finalizeProof target proof
      let updatedEnv ← getEnv
      saved.restore
      modifyEnv fun _ => updatedEnv
      return .ok proof
    catch error =>
      if error.isInterrupt then throw error
      trace[ViaLean.native] "mathlib tactic exception ({spec.name}): {error.toMessageData}"
      saved.restore
      -- Formatting a deeply nested tactic exception can itself exceed Lean's
      -- recursion limit. Diagnostics are best-effort and must never abort the
      -- router's fallback to the next backend.
      if request.wantDiagnostics then
        let message ← try error.toMessageData.toString catch _ =>
          pure "exception detail exceeded the rendering limit"
        return .error s!"{spec.name}: {message}"
      return .error s!"{spec.name}: tactic failed"

/-- Normalize only through target-connected local equalities, then run one
decision procedure on the resulting atomic target. The simplifier assignment
reconstructs a proof of the original goal when the child proof is installed. -/
private def runTargetConnectedTactic
    (request : SolverRequest) (spec : TacticSpec) : MetaM (Except String Expr) :=
  request.goal.withContext do
    let saved ← saveState
    let _ : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try
      let target ← instantiateMVars (← request.goal.getType)
      let rootExpr ← mkFreshExprSyntheticOpaqueMVar target
      let root := rootExpr.mvarId!
      let (simpCtx, rewriteCount) ← targetConnectedRewriteContext target
      if rewriteCount = 0 then
        saved.restore
        return .error s!"{spec.name}: no target-connected local equality"
      let (child?, _) ← ExecutionBoundary.withoutSpeculativeMessages <|
        simpTarget root simpCtx
      match child? with
      | some child =>
          let childTarget ← instantiateMVars (← child.getType)
          if childTarget == target then
            saved.restore
            return .error s!"{spec.name}: target-connected normalization made no progress"
          match ← runClosedTactic { request with goal := child } spec with
          | .error message =>
              saved.restore
              return .error message
          | .ok childProof => child.assign childProof
      | none => pure ()
      let some proof ← getExprMVarAssignment? root
        | saved.restore
          return .error s!"{spec.name}: normalized child did not reconstruct the root"
      let proof ← finalizeProof target proof
      let updatedEnv ← getEnv
      saved.restore
      modifyEnv fun _ => updatedEnv
      return .ok proof
    catch error =>
      if error.isInterrupt then throw error
      saved.restore
      return .error s!"{spec.name}: target-connected normalization failed"
/-- Grind is highly effective on finite first-order goals, but higher-order
locals (functions or universally quantified hypotheses) can enter kernel paths
that do not poll cancellation or heartbeats. Keep those goals on the ordinary
symbolic/mathlib portfolio. -/
private def isDangerousQuantifiedProp (type : Expr) : MetaM Bool := do
  let type ← instantiateMVars type
  if !(← isProp type) then return false
  return type.isForall || type.containsConst (· == ``Exists)

private def isGrindSafeGoal (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        if ← isDangerousQuantifiedProp decl.type then return false
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars _ => do
      for fvar in fvars do
        if ← isDangerousQuantifiedProp (← inferType fvar) then return false
      return true
private def isStructuralGoal (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    let target ← whnf (← instantiateMVars (← request.goal.getType))
    return target.isForall || target.isAppOfArity ``And 2 ||
      target.isAppOfArity ``Or 2 || target.isAppOfArity ``Iff 2 ||
      target.isAppOfArity ``Exists 2

private def natPowArgs? (expr : Expr) : Option (Expr × Expr) :=
  match expr.getAppFnArgs with
  | (``HPow.hPow, #[natType, _, _, _, base, exponent]) =>
      if natType.isConstOf ``Nat then some (base, exponent) else none
  | (``Nat.pow, #[base, exponent]) => some (base, exponent)
  | _ => none

private def natModArgs? (expr : Expr) : Option (Expr × Expr) :=
  match expr.getAppFnArgs with
  | (``HMod.hMod, #[natType, _, _, _, dividend, modulus]) =>
      if natType.isConstOf ``Nat then some (dividend, modulus) else none
  | (``Nat.mod, #[dividend, modulus]) => some (dividend, modulus)
  | _ => none

private def fastNatPowModProof? (target : Expr) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  let some (_, lhs, rhs) := target.eq? | return none
  let inspect (modSide expected : Expr) (reversed : Bool) := do
    let some (power, modulus) := natModArgs? modSide | return none
    let some (base, exponent) := natPowArgs? power | return none
    let some baseValue := base.numeral? | return none
    let some exponentValue := exponent.numeral? | return none
    let some modulusValue := modulus.numeral? | return none
    let some expectedValue := expected.numeral? | return none
    let rawBase : Q(ℕ) := mkRawNatLit baseValue
    let rawExponent : Q(ℕ) := mkRawNatLit exponentValue
    let rawModulus : Q(ℕ) := mkRawNatLit modulusValue
    let rawExpected : Q(ℕ) := mkRawNatLit expectedValue
    let ⟨computed, proof⟩ :=
      Mathlib.Meta.NormNum.evalNatPowMod rawBase rawExponent rawModulus
    unless ← isDefEq computed rawExpected do return none
    if reversed then return some (← mkAppM `Eq.symm #[proof])
    return some proof
  match ← inspect lhs rhs false with
  | some proof => return some proof
  | none => inspect rhs lhs true
private def fastNatPowModLeafSolver : LeafSolver where
  kind := .leanTactic "fast-nat-pow-mod"
  solve request := request.goal.withContext do
    let started ← IO.monoMsNow
    let target ← instantiateMVars (← request.goal.getType)
    let proof? ←
      withTheReader Core.Context
          (fun context => { context with maxRecDepth := 100000, maxHeartbeats := 5000000 }) do
        withCurrHeartbeats do
          let candidate? ← fastNatPowModProof? target
          match candidate? with
          | some proof =>
              let proof ← finalizeProof target proof
              return some proof
          | none => pure none
    return {
      backend := .leanTactic "fast-nat-pow-mod"
      proof?
      solved := proof?.isSome
      elapsedMs := (← IO.monoMsNow) - started
      progress := if proof?.isSome then 1.0 else 0.0
    }
/-- Optional mathlib leaf backend. The enclosing ViaLean search supplies the
wall-clock cancellation token; this backend also checks its shared budget
between tactics and never accepts a tactic that leaves goals. -/
def mathlibLeafSolver : LeafSolver where
  kind := .leanTactic "mathlib-portfolio"
  solve request := do
    let isStructural ← isStructuralGoal request
    if isStructural then
      return {
        backend := .leanTactic "mathlib-portfolio"
        solved := false
        proof? := none
        elapsedMs := 0
        diagnostics? := if request.wantDiagnostics then
          some "logical structure is delegated to ViaLean transitions before leaf solving"
        else none
      }
    let portfolioSafe ← isGrindSafeGoal request
    let baseTactics := if portfolioSafe then portfolio else higherOrderPortfolio
    let hasCaseSplitFact := (← getLCtx).any fun decl =>
      !decl.isImplementationDetail && decl.userName.toString.startsWith "hCaseSplit"
    let tactics := if hasCaseSplitFact then caseSplitPortfolio ++ baseTactics else baseTactics
    let started ← IO.monoMsNow
    let leafBudgetMs := request.budgetMs
    let mut diagnostics := #[]
    for spec in targetPortfolio do
      let elapsed := (← IO.monoMsNow) - started
      if elapsed ≥ leafBudgetMs then break
      match ← runTargetConnectedTactic request spec with
      | .ok proof =>
          return {
            backend := .leanTactic spec.name
            proof? := some proof
            solved := true
            elapsedMs := (← IO.monoMsNow) - started
            progress := 1.0
            diagnostics? := if request.wantDiagnostics then
              some s!"closed after target-connected normalization by {spec.name}"
            else none
          }
      | .error message =>
          if request.wantDiagnostics then diagnostics := diagnostics.push message
    for spec in tactics do
      let elapsed := (← IO.monoMsNow) - started
      if elapsed ≥ leafBudgetMs then break
      trace[ViaLean.native] "mathlib leaf start: {spec.name}, elapsed={elapsed}ms, budget={leafBudgetMs}ms"
      match ← runClosedTactic request spec with
      | .ok proof =>
          trace[ViaLean.native] "mathlib leaf solved: {spec.name}"
          return {
            backend := .leanTactic spec.name
            proof? := some proof
            solved := true
            elapsedMs := (← IO.monoMsNow) - started
            progress := 1.0
            diagnostics? := if request.wantDiagnostics then some s!"closed by {spec.name}" else none
          }
      | .error message =>
          trace[ViaLean.native] "mathlib leaf failed: {spec.name}: {message}"
          if request.wantDiagnostics then diagnostics := diagnostics.push message
    return {
      backend := .leanTactic "mathlib-portfolio"
      solved := false
      proof? := none
      elapsedMs := (← IO.monoMsNow) - started
      diagnostics? := if request.wantDiagnostics then
        some (String.intercalate "\n" diagnostics.toList)
      else none
    }

private def hasLocalEquivalence (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        let type ← instantiateMVars decl.type
        if type.isAppOfArity `Equiv 2 then return true
    return false

/-- Keep the dependency-free native backend as an atomic fallback in this
adapter; ViaLean's main search owns logical decomposition. -/
private def atomicNativeLeafSolver (config : ProposeConfig) : LeafSolver where
  kind := .native
  solve request := do
    if !(← isGrindSafeGoal request) then
      return {
        backend := .native
        proof? := none
        solved := false
        elapsedMs := 0
        diagnostics? := if request.wantDiagnostics then
          some "higher-order local context skipped by eager native transforms"
        else none
      }
    if ← isStructuralGoal request then
      return {
        backend := .native
        proof? := none
        solved := false
        elapsedMs := 0
        diagnostics? := if request.wantDiagnostics then
          some "structural goal reserved for ViaLean decomposition"
        else none
      }

    let nativeBudgetMs := min request.budgetMs (config.directProbeSec * 1000)
    let equivalenceSemantics ← hasLocalEquivalence request
    let atomicConfig := {
      config with
        nativeTransforms := false
        nativeEquivTransport := equivalenceSemantics
        nativeCases := false
        nativeInduction := false
    }
    (nativeLeafSolver atomicConfig).solve { request with budgetMs := nativeBudgetMs }

/-- Detect whether an algebraic subterm depends on the current proof state.
Closed numeric denominators do not justify a symbolic branch. -/
private def containsLocalFVar (root : Expr) : Bool := Id.run do
  let mut pending := #[root]
  while !pending.isEmpty do
    let expr := pending.back!
    pending := pending.pop
    match expr with
    | .fvar _ => return true
    | .app fn arg => pending := (pending.push fn).push arg
    | .lam _ domain body _ | .forallE _ domain body _ =>
        pending := (pending.push domain).push body
    | .letE _ type value body _ =>
        pending := ((pending.push type).push value).push body
    | .mdata _ inner | .proj _ _ inner => pending := pending.push inner
    | _ => pure ()
  return false

/-- Collect distinct variable-dependent division denominators, smallest first.
This is operator-structural and independent of theorem names or external datasets. -/
private def divisionDenominators (roots : Array Expr) : Array Expr := Id.run do
  let mut pending := roots
  let mut result := #[]
  while !pending.isEmpty do
    let expr := pending.back!
    pending := pending.pop
    match expr with
    | .app fn arg => pending := (pending.push fn).push arg
    | .lam _ domain body _ | .forallE _ domain body _ =>
        pending := (pending.push domain).push body
    | .letE _ type value body _ =>
        pending := ((pending.push type).push value).push body
    | .mdata _ inner | .proj _ _ inner => pending := pending.push inner
    | _ => pure ()
    match expr.getAppFnArgs with
    | (``HDiv.hDiv, #[_, _, _, _, _, denominator]) =>
        if containsLocalFVar denominator && !denominator.hasLooseBVars &&
            !result.any (· == denominator) then
          result := result.push denominator
    | _ => pure ()
  return result.insertionSort fun left right => exprSize left < exprSize right

/-- Algebraic singularities become explicit Atlas transitions.  A model can
inspect/select these futures, while execution uses kernel-checked excluded
middle and ordinary recursive search on both branches. -/
private def algebraicCaseSplitProposals (snap : GoalSnapshot) : MetaM (Array Proposal) :=
  snap.goalId.withContext do
    let roots := #[snap.target] ++ snap.locals.map (·.type)
    let denominators := (divisionDenominators roots).take 4
    let mut proposals := #[]
    for denominator in denominators do
      let saved ← saveState
      try
        let denominatorType ← inferType denominator
        let zero ← mkAppOptM ``OfNat.ofNat
          #[some denominatorType, some (mkRawNatLit 0), none]
        let proposition ← mkEq denominator zero
        proposals := proposals.push {
          kind := .caseSplit
          payload := .caseSplit proposition
          origin := .normalization
          source := "algebraic-denominator"
          prior := 0.82
          estimatedCost := 1.35
          fingerprint := proposalFingerprint .caseSplit proposition
          explanation? := some "split a variable-dependent denominator into zero and nonzero futures"
        }
      catch _ =>
        restoreState saved
    return proposals
/-- Collect norm-like nonlinear atoms and typed numeral anchors from the current
state.  Pairing atoms with anchors is bounded below; no theorem or dataset name
participates in discovery. -/
private def normAtomsAndAnchors (roots : Array Expr) : Array Expr × Array Expr := Id.run do
  let mut pending := roots
  let mut atoms := #[]
  let mut anchors := #[]
  while !pending.isEmpty do
    let expr := pending.back!
    pending := pending.pop
    match expr with
    | .app fn arg => pending := (pending.push fn).push arg
    | .lam _ domain body _ | .forallE _ domain body _ =>
        pending := (pending.push domain).push body
    | .letE _ type value body _ =>
        pending := ((pending.push type).push value).push body
    | .mdata _ inner | .proj _ _ inner => pending := pending.push inner
    | _ => pure ()
    match expr.getAppFnArgs with
    | (``Norm.norm, args) =>
        if containsLocalFVar expr && !expr.hasLooseBVars &&
            !atoms.any (· == expr) && !args.isEmpty then
          atoms := atoms.push expr
    | _ =>
        if expr.numeral?.isSome && !expr.hasLooseBVars &&
            !anchors.any (· == expr) then
          anchors := anchors.push expr
  return (atoms.insertionSort fun left right => exprSize left < exprSize right,
    anchors.insertionSort fun left right => exprSize left > exprSize right)

private def verifiedHelperProposal
    (candidate proof : Expr) (source explanation : String)
    (prior cost : Float) : Proposal := {
  kind := .cut
  payload := .verifiedCut candidate proof
  origin := .normalization
  source
  prior
  estimatedCost := cost
  fingerprint := proposalFingerprint .cut candidate
  explanation? := some explanation
}

/-- Generate a small basis of universally valid quadratic facts around nonlinear
norm atoms.  These are theorem-produced, checked at execution, exposed to the
model, and composed by the ordinary recursive cut search. -/
private def quadraticHelperProposals (snap : GoalSnapshot) : MetaM (Array Proposal) :=
  snap.goalId.withContext do
    let roots := #[snap.target] ++ snap.locals.map (·.type)
    let (atoms, anchors) := normAtomsAndAnchors roots
    let mut proposals := #[]
    for atom in atoms.take 2 do
      let args := atom.getAppArgs
      if args.isEmpty then continue
      let argument := args.back!
      let saved ← saveState
      try
        let rawProof ← mkAppM ``sq_abs #[argument]
        let atomSquare ← mkAppM ``HPow.hPow #[atom, mkRawNatLit 2]
        let argumentSquare ← mkAppM ``HPow.hPow #[argument, mkRawNatLit 2]
        let candidate ← instantiateMVars (← mkEq atomSquare argumentSquare)
        let proof ← finalizeProof candidate rawProof
        proposals := proposals.push <| verifiedHelperProposal candidate proof
          "quadratic/norm-square" "normalize the square of a real norm/absolute-value atom" 0.88 1.05
      catch _ => restoreState saved
      for anchor in anchors.take 4 do
        let saved ← saveState
        try
          unless ← isDefEq (← inferType atom) (← inferType anchor) do
            restoreState saved
            continue
          let difference ← mkAppM ``HSub.hSub #[atom, anchor]
          let proof ← mkAppM ``sq_nonneg #[difference]
          let candidate ← instantiateMVars (← inferType proof)
          let proof ← finalizeProof candidate proof
          proposals := proposals.push <| verifiedHelperProposal candidate proof
            "quadratic/square-nonnegative"
            "add a nonnegative square relating a nonlinear atom to a visible scalar boundary"
            0.84 1.10
        catch _ => restoreState saved
    return (deduplicateProposals proposals).take 6

private def mathlibSymbolicProposals (snap : GoalSnapshot) : MetaM (Array Proposal) := do
  let splits ← algebraicCaseSplitProposals snap
  let helpers ← quadraticHelperProposals snap
  return deduplicateProposals (splits ++ helpers)
/-- Exact parser capabilities granted to model code by this trusted adapter.
The core router grants none, and the global forbidden-syntax check still runs
before this list is consulted. -/
def mathlibModelSyntaxKinds : Array Name := #[
  `Mathlib.Tactic.normNum,
  `Lean.Parser.Tactic.omega,
  `Mathlib.Tactic.linarith,
  `Mathlib.Tactic.linarithArgsRest,
  `Mathlib.Tactic.RingNF.ringNF,
  `Aesop.Frontend.Parser.aesopTactic
]

/-- Give the dependency-free semantic search a bounded, guaranteed window
before the tactic portfolio. Structural roots remain owned by ViaLean's main
search, and a failed native attempt leaves the rest of the shared budget to
mathlib instead of starving either side. -/
def mathlibRouter (config : ProposeConfig) : LeafRouter := {
  backends := #[fastNatPowModLeafSolver, atomicNativeLeafSolver config, mathlibLeafSolver]
  preSnapshotBackends := #[fastNatPowModLeafSolver]
  modelSyntaxKinds := mathlibModelSyntaxKinds
  symbolicProposals := mathlibSymbolicProposals
}

declare_config_elab proposeMathlibConfig ProposeConfig

/-- Search with ViaLean's graph/Atlas engine and the optional trusted mathlib
leaf portfolio. This command is available only when this integration is
imported. -/
elab (name := proposeMathlib) "propose_mathlib" config:optConfig : tactic => do
  let cfg ← proposeMathlibConfig config
  let goal ← getMainGoal
  match ← runSearchWithRouter goal cfg (mathlibRouter cfg) with
  | .solved proof _ =>
      goal.assign proof
      replaceMainGoal []
  | .failed stats =>
      throwError "ViaLean+mathlib found no proof within {cfg.timeoutSec}s; direct={stats.directAttempts}, proposals={stats.proposalAttempts}"

end ViaLean.Mathlib
