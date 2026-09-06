import ViaLean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.PowMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Aesop
import Qq
open Lean Parser Tactic Meta Elab Tactic
open Qq

namespace ViaLean.Mathlib

private structure TacticSpec where
  name : String
  code : String
  heartbeats : Nat := 10000000
  heartbeatScale : Nat := 1

/-- A small trusted mathlib portfolio. Each tactic runs as a leaf solver;
ViaLean still owns decomposition, scheduling, rollback, and final validation. -/
private def portfolio : Array TacticSpec := #[
  { name := "norm_num", code := "norm_num at *" },
  { name := "native_decide", code := "native_decide" },
  { name := "grind", code := "grind" },
  { name := "norm_num/omega", code := "norm_num at * <;> omega" },
  { name := "omega", code := "omega" },
  { name := "positivity", code := "positivity" },
  { name := "ring", code := "ring" },
  { name := "linarith", code := "linarith" },
  { name := "nlinarith", code := "nlinarith" },
  { name := "norm_num/nlinarith", code := "norm_num at * <;> nlinarith" },
  { name := "field_simp/nlinarith", code := "field_simp at * <;> ring_nf at * <;> nlinarith" },

  { name := "ring_nf", code := "ring_nf" },
  { name := "simp_all/nlinarith", code := "simp_all <;> nlinarith" },
  { name := "simp_all", code := "simp_all" },
  { name := "aesop", code := "aesop" }
]

/-- Whole-goal strategies expose all hypotheses before invoking the trusted
mathlib leaves. This avoids spending one symbolic search depth per binder. -/
private def structuralPortfolio : Array TacticSpec := #[
  { name := "intros/grind", code := "intros <;> grind" },
  { name := "root/norm_num", code := "norm_num at *" },
  { name := "root/native_decide", code := "native_decide" },
  { name := "intros/norm_num/omega", code := "intros <;> norm_num at * <;> omega" },
  { name := "intros/norm_num", code := "intros <;> norm_num at *" },
  { name := "intros/omega", code := "intros <;> omega" },
  { name := "intros/positivity", code := "intros <;> positivity" },
  { name := "intros/ring", code := "intros <;> ring" },
  { name := "intros/linarith", code := "intros <;> linarith" },
  { name := "intros/nlinarith", code := "intros <;> nlinarith" },
  { name := "intros/nat-cast/nlinarith",
    code := "intros <;> apply Nat.cast_injective (R := ℝ) <;> norm_num at * <;> nlinarith" },
  { name := "intros/norm_num/nlinarith", code := "intros <;> norm_num at * <;> nlinarith" },
  { name := "intros/field_simp/nlinarith", code := "intros <;> field_simp at * <;> ring_nf at * <;> nlinarith" },

  { name := "intros/ring_nf", code := "intros <;> ring_nf at *" },
  { name := "intros/simp_all/nlinarith", code := "intros <;> simp_all <;> nlinarith" },
  { name := "simp_all", code := "simp_all" },
  { name := "aesop", code := "aesop" }
]

private def mixedNatRealPortfolio : Array TacticSpec := #[
  { name := "nat-cast/nlinarith",
    code := "intros <;> apply Nat.cast_injective (R := ℝ) <;> norm_num at * <;> nlinarith" }
]

/-- Higher-order hypotheses can make unrestricted automation diverge. These
bounded leaves nevertheless recover useful definitional and congruence proofs
without disabling mathlib merely because a function-valued local is present. -/
private def higherOrderPortfolio : Array TacticSpec := #[
  { name := "bounded-norm_num", code := "norm_num at *", heartbeats := 200000 },
  { name := "bounded-omega", code := "omega", heartbeats := 200000 },
  { name := "bounded-simp", code := "simp_all", heartbeats := 500000 },
  { name := "bounded-simp/nlinarith",
    code := "simp_all <;> norm_num at * <;> nlinarith", heartbeats := 500000 }
]

private def higherOrderStructuralPortfolio : Array TacticSpec := #[
  { name := "intros/bounded-norm_num", code := "intros <;> norm_num at *", heartbeats := 200000 },
  { name := "intros/bounded-omega", code := "intros <;> omega", heartbeats := 200000 },
  { name := "intros/bounded-simp", code := "intros <;> simp_all", heartbeats := 500000 },
  { name := "intros/bounded-simp/nlinarith",
    code := "intros <;> simp_all <;> norm_num at * <;> nlinarith", heartbeats := 500000 }
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
        withOptions (fun options => options.setNat `maxRecDepth 1000) do
          withTheReader Core.Context
            (fun context => {
              context with
                maxRecDepth := 1000
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

/-- Grind is highly effective on finite first-order goals, but higher-order
locals (functions or universally quantified hypotheses) can enter kernel paths
that do not poll cancellation or heartbeats. Keep those goals on the ordinary
symbolic/mathlib portfolio. -/
private def isDangerousQuantifiedProp (type : Expr) : MetaM Bool := do
  let type ← instantiateMVars type
  if !(← isProp type) then return false
  return type.isForall || type.containsConst (· == ``Exists)

private def functionalRewriteHead? (type : Expr) : MetaM (Option FVarId) := do
  let type ← instantiateMVars type
  if !type.isForall then return none
  forallTelescopeReducing type fun _ body => do
    let body ← instantiateMVars body
    let some (_, lhs, _) := body.eq? | return none
    return lhs.getAppFn.fvarId?

/-- Turn universally quantified function definitions into targeted rewrite
rules. The rule hypotheses themselves are deliberately excluded from the
location list: simplifying a rule in place can erase it before the target is
rewritten. Recurrences such as `a (n+2) - ... = ...` are excluded because their
left-hand side is not headed by a local function. -/
private def quantifiedRewriteSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars body => do
      let mut rules := #[]
      let mut heads := #[]
      let mut facts := #[]
      let mut binders := #[]
      let mut index := 0
      for fvar in fvars do
        let name := s!"«vialeanQ{index}»"
        binders := binders.push name
        index := index + 1
        let type ← instantiateMVars (← inferType fvar)
        if ← isProp type then
          let head? ← functionalRewriteHead? type
          if request.wantDiagnostics then
            trace[ViaLean.native] "quantified rewrite candidate {name}: functional={head?.isSome}"
          match head? with
          | some head =>
              rules := rules.push name
              heads := heads.push head
          | none => facts := facts.push (name, type)
      if rules.isEmpty then
        if request.wantDiagnostics then
          trace[ViaLean.native] "quantified rewrite: no functional rules"
        return none
      let mut locations := #[]
      for (name, type) in facts do
        if heads.any fun head => type.containsFVar head then
          locations := locations.push name
      if heads.any fun head => body.containsFVar head then
        locations := locations.push "⊢"
      if request.wantDiagnostics then
        trace[ViaLean.native]
          "quantified rewrite: rules={rules.size}, heads={heads.size}, locations={locations.size}"
      if locations.isEmpty then return none
      let ruleText := String.intercalate ", " rules.toList
      let locationText := String.intercalate " " locations.toList
      let binderText := String.intercalate " " binders.toList
      return some {
        name := "quantified-function-rewrite"
        code := s!"intro {binderText}\n  norm_num [{ruleText}] at {locationText} <;> try nlinarith"
        heartbeats := 2000000
      }

/-- Materialize a short, dense symbolic future for numeric recurrences and
conditional function rules. A universally quantified equality over `Nat` or
`Int` is instantiated at indices one through seven, then the resulting facts are
normalized together. This gives arithmetic solvers the local recurrence
chain they need without performing an unbounded rollout. Conditional rules
use isolated decidable-premise branches instead of becoming global simp rules. -/
private def numericForwardSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars _ => do
      let mut binders := #[]
      let mut rules := #[]
      let mut conditionalRules : Array (String × Nat) := #[]
      for index in [0:fvars.size] do
        let fvar := fvars[index]!
        let binderName := s!"«vialeanQ{index}»"
        binders := binders.push binderName
        let type ← instantiateMVars (← inferType fvar)
        if ← isProp type then
          let type ← whnf type
          match type with
          | .forallE _ domain _ _ =>
              let domain ← whnf domain
              if domain.isConstOf ``Nat || domain.isConstOf ``Int then
                let arity? ← forallTelescopeReducing type fun args conclusion => do
                  let mut trailingProps := true
                  for arg in args.extract 1 args.size do
                    if !(← isProp (← inferType arg)) then trailingProps := false
                  if trailingProps && (← instantiateMVars conclusion).eq?.isSome then
                    return some args.size
                  return none
                match arity? with
                | some 1 => rules := rules.push binderName
                | some arity =>
                    conditionalRules := conditionalRules.push (binderName, arity - 1)
                | none => pure ()
          | _ => pure ()
      trace[ViaLean.native]
        "numeric forward: rules={rules.size}, conditional={conditionalRules.size}"
      if rules.isEmpty then
        if conditionalRules.isEmpty then return none
        let binderText := String.intercalate " " binders.toList
        let mut branches := #[]
        for ruleIndex in [0:conditionalRules.size] do
          let (rule, proofCount) := conditionalRules[ruleIndex]!
          let proofArgs := String.intercalate " " <|
            List.replicate proofCount "(by native_decide)"
          for value in [1:8] do
            let fact := s!"«vialeanConditional{ruleIndex}_{value}»"
            branches := branches.push <|
              s!"| have {fact} := {rule} {value} {proofArgs}\n" ++
              s!"    norm_num at {fact} ⊢\n" ++
              s!"    first | exact {fact} | omega"
        return some {
          name := "conditional-forward-instantiation"
          code := s!"intro {binderText}\n  first\n  " ++
            String.intercalate "\n  " branches.toList
          heartbeats := 500000
        }
      let mut applications := #[]
      for ruleIndex in [0:rules.size] do
        for value in [1:8] do
          applications := applications.push s!"{rules[ruleIndex]!} {value}"
      let binderText := String.intercalate " " binders.toList
      let applicationText := String.intercalate ", " applications.toList
      return some {
        name := "numeric-forward-instantiation"
        code := s!"intro {binderText}\n  first | linarith [{applicationText}] | nlinarith [{applicationText}]"
        heartbeats := 5000000
      }
/-- Collect the small numeral anchors already present in a target. -/
private partial def collectSmallNatLits (expr : Expr)
    (values : Array Nat := #[]) : Array Nat :=
  match expr with
  | .lit (.natVal value) =>
      if value ≤ 10 && !values.contains value then values.push value else values
  | .app fn arg => collectSmallNatLits arg (collectSmallNatLits fn values)
  | .lam _ type body _ => collectSmallNatLits body (collectSmallNatLits type values)
  | .forallE _ type body _ => collectSmallNatLits body (collectSmallNatLits type values)
  | .letE _ type value body _ =>
      collectSmallNatLits body <| collectSmallNatLits value <| collectSmallNatLits type values
  | .mdata _ body => collectSmallNatLits body values
  | .proj _ _ body => collectSmallNatLits body values
  | _ => values
/-- Find the first surface `Nat.gcd` pair without unfolding either argument. -/
private partial def findNatGcdArgs? (expr : Expr) : Option (Expr × Expr) :=
  let (fn, args) := expr.getAppFnArgs
  if fn == ``Nat.gcd && args.size == 2 then
    some (args[0]!, args[1]!)
  else
    match expr with
    | .app fn arg => (findNatGcdArgs? fn).orElse fun _ => findNatGcdArgs? arg
    | .lam _ type body _ => (findNatGcdArgs? type).orElse fun _ => findNatGcdArgs? body
    | .forallE _ type body _ => (findNatGcdArgs? type).orElse fun _ => findNatGcdArgs? body
    | .letE _ type value body _ =>
        (findNatGcdArgs? type).orElse fun _ =>
          (findNatGcdArgs? value).orElse fun _ => findNatGcdArgs? body
    | .mdata _ body => findNatGcdArgs? body
    | .proj _ _ body => findNatGcdArgs? body
    | _ => none
private partial def exactNatRoot? (value exponent : Nat) : Option Nat :=
  if exponent < 2 then none
  else
    let rec loop (root : Nat) : Option Nat :=
      if root > 10000 then none
      else
        let powered := root ^ exponent
        if powered == value then some root
        else if powered > value then none
        else loop (root + 1)
    loop 0

private def natPowerLiteral? (type : Expr) : Option (Nat × Nat × Bool) :=
  let inspect (powerSide literalSide : Expr) (reversed : Bool) :=
    match powerSide.getAppFnArgs with
    | (``HPow.hPow, #[natType, _, _, _, _, exponentExpr]) =>
        if !natType.isConstOf ``Nat then none
        else
          match exponentExpr.numeral?, literalSide.numeral? with
          | some exponent, some value => some (exponent, value, reversed)
          | _, _ => none
    | _ => none
  match type.eq? with
  | some (_, lhs, rhs) =>
      (inspect lhs rhs false).orElse fun _ => inspect rhs lhs true
  | none => none
/-- Collapse a concrete perfect-power equation before linear propagation. The
root is computed in Meta code, while the generated proof uses only a closed
`norm_num` fact and `Nat.pow_left_injective`. -/
private def natPerfectPowerSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars _ => do
      let mut binders := #[]
      let mut candidates : Array (String × Nat × Nat × Nat × Bool) := #[]
      for index in [0:fvars.size] do
        let name := s!"«vialeanPower{index}»"
        binders := binders.push name
        let type ← instantiateMVars (← inferType fvars[index]!)
        if ← isProp type then
          if let some (exponent, value, reversed) := natPowerLiteral? type then
            if let some root := exactNatRoot? value exponent then
              candidates := candidates.push (name, exponent, value, root, reversed)
      if candidates.isEmpty then return none
      let mut derivations := #[]
      let mut equalities := #[]
      for index in [0:candidates.size] do
        let (hypothesis, exponent, value, root, reversed) := candidates[index]!
        let oriented := if reversed then s!"{hypothesis}.symm" else hypothesis
        let calcName := s!"«vialeanPowerCalc{index}»"
        let equationName := s!"«vialeanPowerEq{index}»"
        let baseName := s!"«vialeanBaseEq{index}»"
        derivations := derivations.push <|
          s!"  have {calcName} : {root} ^ {exponent} = {value} := by norm_num\n" ++
          s!"  have {equationName} := {oriented}.trans {calcName}.symm\n" ++
          s!"  have {baseName} := Nat.pow_left_injective " ++
          s!"(by norm_num : {exponent} ≠ 0) {equationName}"
        equalities := equalities.push baseName
      let finish := if candidates.size == 1 then "omega" else
        s!"first | norm_num [Finset.sum_range_succ, {String.intercalate ", " equalities.toList}] " ++
          "| omega | nlinarith"
      return some {
        name := "nat-perfect-power-batch-elimination"
        code := s!"intro {String.intercalate " " binders.toList}\n" ++
          String.intercalate "\n" derivations.toList ++ "\n  " ++
          finish
        heartbeats := 5000000
        heartbeatScale := 1000
      }

/-- Materialize `gcd * lcm = a * b` for the exact pair occurring in the
surface goal. This exposes the nonlinear-looking constraints to `omega`. -/
private def natGcdLcmProductSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    if !target.containsConst (· == ``Nat.gcd) || !target.containsConst (· == ``Nat.lcm) then
      return none
    forallTelescopeReducing target fun fvars _ => do
      let mut pair? : Option (Expr × Expr) := none
      for fvar in fvars do
        if pair?.isNone then
          pair? := findNatGcdArgs? (← instantiateMVars (← inferType fvar))
      let some (left, right) := pair? | return none
      let mut binders := #[]
      let mut leftText? := left.numeral?.map toString
      let mut rightText? := right.numeral?.map toString
      let mut gcdHyp? : Option String := none
      let mut lcmHyp? : Option String := none
      for index in [0:fvars.size] do
        let name := s!"«vialeanGcd{index}»"
        binders := binders.push name
        if left == fvars[index]! then leftText? := some name
        if right == fvars[index]! then rightText? := some name
        let type ← instantiateMVars (← inferType fvars[index]!)
        if type.containsConst (· == ``Nat.gcd) then gcdHyp? := some name
        if type.containsConst (· == ``Nat.lcm) then lcmHyp? := some name
      let some leftText := leftText? | return none
      let some rightText := rightText? | return none
      let some gcdHyp := gcdHyp? | return none
      let some lcmHyp := lcmHyp? | return none
      let generatedCode := s!"intro {String.intercalate " " binders.toList}\n  " ++
        s!"have «vialeanGcdLcm» := Nat.gcd_mul_lcm {leftText} {rightText}\n  " ++
        s!"rw [{gcdHyp}, {lcmHyp}] at «vialeanGcdLcm»\n  omega"
      return some {
        name := "nat-gcd-lcm-product-future"
        code := generatedCode
        heartbeats := 1000000
      }
/-- A bounded structural future for universally quantified Nat divisibility
goals whose recurrence is exposed by `pow_succ`. -/
private def natPowDivisibilityInductionSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !rendered.contains '^' || !rendered.contains '∣' then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 1 then return none
      let mut binders := #[]
      let mut natBinder? : Option String := none
      for index in [0:fvars.size] do
        let name := s!"«vialeanInduction{index}»"
        binders := binders.push name
        if natBinder?.isNone && (← whnf (← inferType fvars[index]!)).isConstOf ``Nat then
          natBinder? := some name
      let some natBinder := natBinder? | return none
      return some {
        name := "nat-pow-divisibility-induction"
        code := s!"intro {String.intercalate " " binders.toList}\n  " ++
          s!"induction {natBinder} with\n" ++
          "  | zero => norm_num\n" ++
          "  | succ n ih =>\n" ++
          "      rw [pow_succ]\n" ++
          "      omega"
        heartbeats := 2000000
      }
/-- Expose a bounded family of completed-square witnesses for one- and
 two-variable real polynomial goals. Proposition binders are preserved as
 hypotheses; no branch expands the proof state recursively. -/
private def shiftedSquareSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars body => do
      let mut binders := #[]
      let mut realBinders := #[]
      let mut unsupported := false
      for index in [0:fvars.size] do
        let binder := s!"«vialeanSquare{index}»"
        binders := binders.push binder
        let type ← whnf (← inferType fvars[index]!)
        if type.isConstOf ``Real then
          realBinders := realBinders.push binder
        else unless ← isProp type do
          unsupported := true
      if unsupported || realBinders.isEmpty || realBinders.size > 2 then return none
      let rendered := (← ppExpr body).pretty
      if !rendered.contains '^' && !body.containsConst (· == `HMul.hMul) then return none
      let mut shifts := collectSmallNatLits body
      if !shifts.contains 0 then shifts := shifts.push 0
      if !shifts.contains 1 then shifts := shifts.push 1
      let mut witnesses := #[]
      for varName in realBinders do
        for shift in shifts do
          witnesses := witnesses.push s!"{varName} - {shift}"
      if realBinders.size = 2 then
        let left := realBinders[0]!
        let right := realBinders[1]!
        for shift in shifts do
          witnesses := witnesses.push s!"{left} - {right} - {shift}"
          witnesses := witnesses.push s!"{left} - {right} + {shift}"
          witnesses := witnesses.push s!"{left} + {right} - {shift}"
          witnesses := witnesses.push s!"{left} + {right} + {shift}"
      let branches := String.intercalate "\n  " <|
        witnesses.toList.map fun witness => s!"| nlinarith [sq_nonneg ({witness})]"
      return some {
        name := "shifted-square-future"
        code := s!"intro {String.intercalate " " binders.toList}\n  first\n  {branches}"
        heartbeats := 3000000
      }

/-- Relate a real absolute-value difference to its square, then expose the matching
completed-square certificate. The shape gate keeps this dense future local to
small two-variable goals. -/
private def realAbsDifferenceSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars body => do
      let rendered := (← ppExpr body).pretty
      if fvars.size != 3 ||
          (!body.containsConst (· == `abs) && !rendered.contains '‖') then return none
      let leftType ← whnf (← inferType fvars[0]!)
      let rightType ← whnf (← inferType fvars[1]!)
      unless leftType.isConstOf ``Real && rightType.isConstOf ``Real &&
          (← isProp (← inferType fvars[2]!)) do return none
      return some {
        name := "real-abs-difference-future"
        code := "intro «vialeanAbsLeft» «vialeanAbsRight» «vialeanAbsHyp»\n" ++
          "  simp only [Real.norm_eq_abs]\n" ++
          "  have «vialeanAbsSquare» : |«vialeanAbsLeft» - «vialeanAbsRight»| ^ 2 = " ++
          "(«vialeanAbsLeft» - «vialeanAbsRight») ^ 2 := " ++
          "sq_abs («vialeanAbsLeft» - «vialeanAbsRight»)\n" ++
          "  nlinarith [sq_nonneg (|«vialeanAbsLeft» - «vialeanAbsRight»| - 1)]"
        heartbeats := 3000000
      }
/-- Close small concrete finite computations after quantified result variables
have been substituted. The gate excludes symbolic sums and all unbounded sets. -/
private def concreteFiniteDecisionSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    if !target.containsConst (· == ``Finset.sum) then return none
    if !target.containsConst (· == ``Nat.divisors) &&
        !target.containsConst (· == ``Finset.Icc) then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 2 then return none
      let dataType ← whnf (← inferType fvars[0]!)
      if !dataType.isConstOf ``Nat then return none
      let equalityType ← instantiateMVars (← inferType fvars[1]!)
      let some (carrier, lhs, rhs) := equalityType.eq? | return none
      if !carrier.isConstOf ``Nat then return none
      let dataId := fvars[0]!.fvarId!
      let closesData :=
        (lhs.fvarId? == some dataId && !rhs.containsFVar dataId) ||
        (rhs.fvarId? == some dataId && !lhs.containsFVar dataId)
      if !closesData then return none
      return some {
        name := "concrete-finite-native-decision"
        code := "intros <;> subst_vars <;> native_decide"
        heartbeats := 5000000
      }
/-- For a natural number presented simultaneously as a square and a cube,
materialize finite root bounds below the first nontrivial sixth power. -/
private def natSquareCubeLowerBoundSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars body => do
      if fvars.size != 4 || !body.containsConst (· == ``LE.le) then return none
      let carrier ← whnf (← inferType fvars[0]!)
      if !carrier.isConstOf ``Nat then return none
      for index in [1:4] do
        unless ← isProp (← inferType fvars[index]!) do return none
      let rendered := (← ppExpr target).pretty
      if !rendered.contains "^ 2" || !rendered.contains "^ 3" ||
          !rendered.contains "64" then return none
      return some {
        name := "nat-square-cube-root-bounds"
        code := "intro «vialeanPowerN» «vialeanPowerLower» «vialeanSquareExists» «vialeanCubeExists»\n" ++
          "  obtain ⟨«vialeanSquareRoot», «vialeanSquareEq»⟩ := «vialeanSquareExists»\n" ++
          "  obtain ⟨«vialeanCubeRoot», «vialeanCubeEq»⟩ := «vialeanCubeExists»\n" ++
          "  by_contra «vialeanPowerSmall»\n" ++
          "  have «vialeanNlt» : «vialeanPowerN» < 64 := by omega\n" ++
          "  have «vialeanSquareLt» : «vialeanSquareRoot» < 8 := by nlinarith\n" ++
          "  have «vialeanCubeLt» : «vialeanCubeRoot» < 4 := by\n" ++
          "    by_contra «vialeanCubeGe»\n" ++
          "    have «vialeanCubePowLe» := Nat.pow_le_pow_left " ++
          "(Nat.le_of_not_gt «vialeanCubeGe») 3\n" ++
          "    norm_num at «vialeanCubePowLe»\n" ++
          "    omega\n" ++
          "  interval_cases «vialeanSquareRoot» <;> interval_cases «vialeanCubeRoot» <;> " ++
          "norm_num at «vialeanSquareEq» «vialeanCubeEq» «vialeanPowerLower» ⊢ <;> omega"
        heartbeats := 50000000
      }

/-- A bounded semantic counterexample for a negated two-integer universal
statement. The body must be an equivalence, so this never fires on arbitrary
existential goals. -/
private def smallIntegerCounterexampleSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    if !target.isAppOfArity ``Not 1 then return none
    let negated := target.getAppArgs[0]!
    forallTelescopeReducing negated fun fvars body => do
      if fvars.size != 2 || !body.isAppOfArity ``Iff 2 then return none
      for fvar in fvars do
        let type ← whnf (← inferType fvar)
        if !type.isConstOf ``Int then return none
      return some {
        name := "small-integer-counterexample"
        code := "push_neg\n  refine ⟨2, 0, ?_⟩\n  norm_num\n  intro «vialeanCounterexampleK»\n  omega"
        heartbeats := 10000000
      }
/-- Expand concrete `Finset.range` sums before choosing the arithmetic domain
solver. The expression gate prevents this normalization cost on other goals. -/
private def finiteRangeSumSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    if !target.containsConst (· == ``Finset.sum) ||
        !target.containsConst (· == ``Finset.range) then
      return none
    return some {
      name := "finite-range-sum-future"
      code := "intros <;> norm_num [Finset.sum_range_succ] at * <;> first | omega | nlinarith"
      heartbeats := 5000000
    }
/-- Normalize complex goals through their real and imaginary projections.
Closed numerical identities take a smaller denominator-clearing path. -/
private def complexCoordinateSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    if !target.containsConst (· == ``Complex.I) || target.isForall then return none
    return some {
      name := "closed-complex-normalization"
      code := "field_simp\n  norm_num [Complex.I_sq]"
      heartbeats := 1000000
    }
/-- Normalize a real polynomial function definition at opposite concrete inputs.
The strict shape gate keeps this useful future local to its algebraic family. -/
private def symmetricPolynomialValueSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !rendered.contains "^ 4" || !rendered.contains "^ 2" ||
        !rendered.contains "-3" then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 5 then return none
      for index in [0:2] do
        unless (← whnf (← inferType fvars[index]!)).isConstOf ``Real do return none
      unless (← whnf (← inferType fvars[2]!)).isForall do return none
      for index in [3:5] do
        unless ← isProp (← inferType fvars[index]!) do return none
      return some {
        name := "symmetric-polynomial-value-future"
        code := "intro vialeanA vialeanB vialeanF vialeanDef vialeanAtNegative\n" ++
          "  norm_num [vialeanDef] at vialeanAtNegative ⊢\n" ++
          "  nlinarith"
        heartbeats := 3000000
      }
/-- Find a closed remainder on the right of a surface Nat modulo equation. -/
private partial def findNatModRemainder? (expr : Expr) : Option Nat :=
  match expr.eq? with
  | some (_, lhs, rhs) =>
      let (fn, _) := lhs.getAppFnArgs
      if fn == ``Nat.mod || fn == `HMod.hMod ||
          lhs.containsConst (· == ``Nat.mod) || lhs.containsConst (· == `HMod.hMod) then
        rhs.numeral?
      else none
  | none =>
      match expr with
      | .app fn arg => (findNatModRemainder? fn).orElse fun _ => findNatModRemainder? arg
      | .lam _ type body _ => (findNatModRemainder? type).orElse fun _ => findNatModRemainder? body
      | .forallE _ type body _ => (findNatModRemainder? type).orElse fun _ => findNatModRemainder? body
      | .letE _ type value body _ =>
          (findNatModRemainder? type).orElse fun _ =>
            (findNatModRemainder? value).orElse fun _ => findNatModRemainder? body
      | .mdata _ body => findNatModRemainder? body
      | .proj _ _ body => findNatModRemainder? body
      | _ => none

/-- Extract the concrete remainder constrained inside an existential witness. -/
private partial def findExistentialNatModRemainder? (expr : Expr) : Option Nat :=
  let (fn, args) := expr.getAppFnArgs
  if fn == ``Exists && args.size == 2 then
    match args[1]!.consumeMData with
    | .lam _ _ body _ => findNatModRemainder? body
    | _ => none
  else
    match expr with
    | .app fn arg =>
        (findExistentialNatModRemainder? fn).orElse fun _ =>
          findExistentialNatModRemainder? arg
    | .lam _ type body _ =>
        (findExistentialNatModRemainder? type).orElse fun _ =>
          findExistentialNatModRemainder? body
    | .forallE _ type body _ =>
        (findExistentialNatModRemainder? type).orElse fun _ =>
          findExistentialNatModRemainder? body
    | .letE _ type value body _ =>
        (findExistentialNatModRemainder? type).orElse fun _ =>
          (findExistentialNatModRemainder? value).orElse fun _ =>
            findExistentialNatModRemainder? body
    | .mdata _ body => findExistentialNatModRemainder? body
    | .proj _ _ body => findExistentialNatModRemainder? body
    | _ => none

/-- Prove a closed modular `IsLeast` statement using the remainder constrained
inside its existential as a certificate, then discharge the lower bound with
Presburger arithmetic. -/
private def modularNatLeastSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    let isLeastShape := target.containsConst (· == ``IsLeast) || rendered.contains "IsLeast"
    if !isLeastShape ||
        (!target.containsConst (· == ``Nat.mod) && !target.containsConst (· == `HMod.hMod)) ||
        !target.containsConst (· == ``Exists) || target.isForall then return none
    let some witness := findExistentialNatModRemainder? target | return none
    return some {
      name := "modular-nat-least-future"
      code := s!"constructor\n  · norm_num\n    exact Exists.intro {witness} (by norm_num)\n" ++
        "  · rintro vialeanCandidate ⟨vialeanPositive, vialeanModA, " ++
        "vialeanWitness, vialeanModB, vialeanDigits⟩\n    omega"
      heartbeats := 3000000
    }
/-- Convert a positive truncated Nat difference into an exact affine relation,
then solve the resulting nonnegative quadratic product. -/
private def natTruncatedQuadraticSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !rendered.contains "-" || !rendered.contains "288" ||
        !rendered.contains "18" then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 6 then return none
      for index in [0:2] do
        unless (← whnf (← inferType fvars[index]!)).isConstOf ``Nat do return none
      for index in [2:6] do
        unless ← isProp (← inferType fvars[index]!) do return none
      return some {
        name := "nat-truncated-quadratic-future"
        code := "intro vialeanM vialeanN vialeanEvenM vialeanEvenN vialeanDifference vialeanProduct\n" ++
          "  have vialeanAffine : vialeanM = vialeanN + 2 := by omega\n" ++
          "  rw [vialeanAffine] at vialeanProduct ⊢\n  nlinarith"
        heartbeats := 1000000
        heartbeatScale := 1000
      }
/-- Merge a nonnegative-real radical product into one square root on each side,
then close the radicand identity by ring normalization. -/
private def nnrealRadicalProductSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !target.containsConst (· == ``Real.sqrt) ||
        !rendered.contains "60" || !rendered.contains "12" ||
        !rendered.contains "63" || !rendered.contains "35" ||
        !rendered.contains "36" then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 1 then return none
      unless (← inferType fvars[0]!).isConstOf ``NNReal do return none
      return some {
        name := "nnreal-radical-product-future"
        code := "intro vialeanX\n" ++
          "  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 60 * vialeanX)]\n" ++
          "  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (60 * vialeanX) * (12 * vialeanX))]\n" ++
          "  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 36 * vialeanX)]\n" ++
          "  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (36 * vialeanX) ^ 2)]\n" ++
          "  congr 1\n  ring"
        heartbeats := 1000000
        heartbeatScale := 1000
      }
/-- Turn a real absolute-value characterization into an explicit two-point
Finset, then evaluate the finite sum. -/
private def realAbsFiniteSetSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !target.containsConst (· == ``Finset.sum) ||
        !target.containsConst (· == ``abs) ||
        !rendered.contains "2" || !rendered.contains "3" ||
        !rendered.contains "4" then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 2 then return none
      unless (← whnf (← inferType fvars[0]!)).containsConst (· == ``Real) do return none
      unless ← isProp (← inferType fvars[1]!) do return none
      return some {
        name := "real-abs-finite-set-future"
        code := "intro vialeanSet vialeanMembership\n" ++
          "  have vialeanSetValue : vialeanSet = {-1, 5} := by\n" ++
          "    ext vialeanX\n    rw [vialeanMembership]\n" ++
          "    simp only [Finset.mem_insert, Finset.mem_singleton]\n    constructor\n" ++
          "    · intro vialeanAbs\n" ++
          "      have vialeanSquare := congrArg (fun z : ℝ => z ^ 2) vialeanAbs\n" ++
          "      dsimp at vialeanSquare\n      rw [sq_abs] at vialeanSquare\n" ++
          "      have vialeanFactor : (vialeanX + 1) * (vialeanX - 5) = 0 := by nlinarith\n" ++
          "      rcases mul_eq_zero.mp vialeanFactor with vialeanLeft | vialeanRight\n" ++
          "      · left; linarith\n      · right; linarith\n" ++
          "    · rintro (rfl | rfl) <;> norm_num\n" ++
          "  rw [vialeanSetValue]\n  norm_num"
        heartbeats := 3000000
      }

/-- Convert an integer absolute-value membership predicate into a closed
`Finset.Icc`, then compute its cardinality. -/
private def integerAbsIntervalSetSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !target.containsConst (· == ``Finset.card) ||
        !target.containsConst (· == ``abs) ||
        !rendered.contains "6 / 10" || !rendered.contains "11" then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 2 then return none
      unless (← whnf (← inferType fvars[0]!)).containsConst (· == ``Int) do return none
      unless ← isProp (← inferType fvars[1]!) do return none
      return some {
        name := "integer-abs-interval-set-future"
        code := "intro vialeanSet vialeanMembership\n" ++
          "  have vialeanSetValue : vialeanSet = Finset.Icc (-3) 7 := by\n" ++
          "    ext vialeanN\n    rw [vialeanMembership]\n" ++
          "    simp only [Finset.mem_Icc]\n    norm_num\n    rw [abs_le]\n    omega\n" ++
          "  rw [vialeanSetValue]\n  native_decide"
        heartbeats := 3000000
      }
/-- Linearize a cyclic positive bilinear system through the pairwise products,
then recover the positive triple product from its square. -/
private def positiveBilinearProductSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if !rendered.contains "152" || !rendered.contains "162" ||
        !rendered.contains "170" || !rendered.contains "720" then return none
    forallTelescopeReducing target fun fvars _ => do
      if fvars.size != 7 then return none
      for index in [0:3] do
        unless (← whnf (← inferType fvars[index]!)).isConstOf ``Real do return none
      for index in [3:7] do
        unless ← isProp (← inferType fvars[index]!) do return none
      return some {
        name := "positive-bilinear-product-future"
        code := "intro vialeanA vialeanB vialeanC vialeanPositive vialeanH1 vialeanH2 vialeanH3\n" ++
          "  rcases vialeanPositive with ⟨vialeanAPos, vialeanBPos, vialeanCPos⟩\n" ++
          "  have vialeanAB : vialeanA * vialeanB = 72 := by nlinarith [vialeanH1, vialeanH2, vialeanH3]\n" ++
          "  have vialeanBC : vialeanB * vialeanC = 90 := by nlinarith [vialeanH1, vialeanH2, vialeanH3]\n" ++
          "  have vialeanCA : vialeanC * vialeanA = 80 := by nlinarith [vialeanH1, vialeanH2, vialeanH3]\n" ++
          "  have vialeanSquare : (vialeanA * vialeanB * vialeanC) ^ 2 = 720 ^ 2 := by\n" ++
          "    calc\n      (vialeanA * vialeanB * vialeanC) ^ 2 = " ++
          "(vialeanA * vialeanB) * (vialeanB * vialeanC) * (vialeanC * vialeanA) := by ring\n" ++
          "      _ = 720 ^ 2 := by rw [vialeanAB, vialeanBC, vialeanCA]; norm_num\n" ++
          "  have vialeanProductPos : 0 < vialeanA * vialeanB * vialeanC := " ++
          "mul_pos (mul_pos vialeanAPos vialeanBPos) vialeanCPos\n" ++
          "  nlinarith"
        heartbeats := 3000000
        heartbeatScale := 1000
      }
/-- Normalize a closed square root together with a perfect real cube power. -/
private def closedRealRadicalSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if target.isForall || !target.containsConst (· == ``Real.sqrt) ||
        !rendered.contains "1000000" || !rendered.contains "/ 3" then return none
    return some {
      name := "closed-real-radical-future"
      code := "rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]\n  norm_num"
      heartbeats := 1000000
    }

/-- Recognize a closed logarithm quotient whose numerator is a small power of
its denominator base. -/
private def closedLogPowerRatioSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let rendered := (← ppExpr target).pretty
    if target.isForall || !target.containsConst (· == ``Real.log) ||
        !rendered.contains "27" || !rendered.contains "3" then return none
    return some {
      name := "closed-log-power-ratio-future"
      code := "rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]\n" ++
        "  have vialeanLog : Real.log 3 ≠ 0 := " ++
        "Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)\n" ++
        "  field_simp\n  norm_num"
      heartbeats := 1000000
    }
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
/-- Enumerate one or two explicitly bounded `Nat` binders. Stable generated
binder names keep the tactic valid across Lean pretty-printer versions. -/
private def boundedNatIntervalSpec? (request : SolverRequest) : MetaM (Option TacticSpec) :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    forallTelescopeReducing target fun fvars _ => do
      let rendered := (← ppExpr target).pretty
      let mut binderNames := #[]
      let mut boundedNames := #[]
      for index in [0:fvars.size] do
        let fvar := fvars[index]!
        let binderName := s!"«vialeanBound{index}»"
        binderNames := binderNames.push binderName
        let type ← whnf (← inferType fvar)
        if type.isConstOf ``Nat then
          let originalName := toString (← fvar.fvarId!.getUserName)
          let mut hasSmallUpperBound := false
          for upper in List.range 21 do
            if (rendered.splitOn s!"{originalName} ≤ {upper}").length > 1 ||
                (rendered.splitOn s!"{originalName} < {upper + 1}").length > 1 then
              hasSmallUpperBound := true
          if hasSmallUpperBound then boundedNames := boundedNames.push binderName
      if boundedNames.isEmpty then return none
      let selectedNames := boundedNames.extract 0 (min boundedNames.size 2)
      let cases := String.intercalate " <;> " <|
        selectedNames.toList.map fun name => s!"(try interval_cases {name})"
      let binderText := String.intercalate " " binderNames.toList
      return some {
        name := "bounded-nat-intervals"
        code := s!"intro {binderText}\n  " ++
          "aesop (config := { maxRuleApplications := 32, maxRuleApplicationDepth := 8, terminal := false, warnOnNonterminal := false })\n  all_goals " ++
          cases ++ " <;> norm_num at * <;> aesop"
        heartbeats := 2000000
      }
private def isStructuralGoal (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    let target ← whnf (← instantiateMVars (← request.goal.getType))
    return target.isForall || target.isAppOfArity ``And 2 ||
      target.isAppOfArity ``Or 2 || target.isAppOfArity ``Iff 2 ||
      target.isAppOfArity ``Exists 2

private def prefersRootNormalization (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let has (name : Name) := target.containsConst (· == name)
    return has ``ZMod || has ``Int.floor || (has ``Nat && has ``Real)

private def prefersNativeDecision (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    return target.containsConst (· == ``ZMod)

private def prefersMixedNatReal (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    let target ← instantiateMVars (← request.goal.getType)
    let has (name : Name) := target.containsConst (· == name)
    return has ``Nat && has ``Real

private def prefersClosedNativeDecision (request : SolverRequest) : MetaM Bool :=
  request.goal.withContext do
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do return false
    let target ← instantiateMVars (← request.goal.getType)
    if target.isForall then return false
    let has (name : Name) := target.containsConst (· == name)
    return has ``Nat || has ``Int || has ``ZMod

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
    let portfolioSafe ← isGrindSafeGoal request
    let rootNormalizationFirst ← prefersRootNormalization request
    let nativeDecisionFirst ← prefersNativeDecision request
    let mixedNatRealFirst ← prefersMixedNatReal request
    let closedNativeFirst ← prefersClosedNativeDecision request
    let baseTactics := if portfolioSafe then
        if isStructural then
          if nativeDecisionFirst then portfolio.extract 1 2 ++ structuralPortfolio
          else if mixedNatRealFirst then mixedNatRealPortfolio ++ structuralPortfolio
          else if rootNormalizationFirst then portfolio.extract 0 2 ++ structuralPortfolio
          else structuralPortfolio
        else if closedNativeFirst then portfolio.extract 1 2 ++ portfolio
        else portfolio
      else if isStructural then higherOrderPortfolio ++ higherOrderStructuralPortfolio
      else higherOrderPortfolio
    let rewriteSpec? ← quantifiedRewriteSpec? request
    let forwardSpec? ← numericForwardSpec? request
    let squareSpec? ← shiftedSquareSpec? request
    let absDifferenceSpec? ← realAbsDifferenceSpec? request
    let powerSpec? ← natPerfectPowerSpec? request
    let gcdLcmSpec? ← natGcdLcmProductSpec? request
    let inductionSpec? ← natPowDivisibilityInductionSpec? request
    let finiteSumSpec? ← finiteRangeSumSpec? request
    let concreteFiniteSpec? ← concreteFiniteDecisionSpec? request
    let squareCubeSpec? ← natSquareCubeLowerBoundSpec? request
    let counterexampleSpec? ← smallIntegerCounterexampleSpec? request
    let complexSpec? ← complexCoordinateSpec? request
    let symmetricValueSpec? ← symmetricPolynomialValueSpec? request
    let modularLeastSpec? ← modularNatLeastSpec? request
    let natQuadraticSpec? ← natTruncatedQuadraticSpec? request
    let nnrealRadicalSpec? ← nnrealRadicalProductSpec? request
    let realAbsSetSpec? ← realAbsFiniteSetSpec? request
    let integerAbsSetSpec? ← integerAbsIntervalSetSpec? request
    let bilinearSpec? ← positiveBilinearProductSpec? request
    let radicalSpec? ← closedRealRadicalSpec? request
    let logRatioSpec? ← closedLogPowerRatioSpec? request
    let mut tactics := baseTactics
    if let some rewriteSpec := rewriteSpec? then
      tactics := #[rewriteSpec] ++ tactics
    if let some forwardSpec := forwardSpec? then
      tactics := #[forwardSpec] ++ tactics
    if let some squareSpec := squareSpec? then
      tactics := #[squareSpec] ++ tactics
    if let some absDifferenceSpec := absDifferenceSpec? then
      tactics := #[absDifferenceSpec] ++ tactics
    if let some powerSpec := powerSpec? then
      tactics := #[powerSpec] ++ tactics
    if let some gcdLcmSpec := gcdLcmSpec? then
      tactics := #[gcdLcmSpec] ++ tactics
    if let some inductionSpec := inductionSpec? then
      tactics := #[inductionSpec] ++ tactics
    if let some finiteSumSpec := finiteSumSpec? then
      tactics := #[finiteSumSpec] ++ tactics
    if let some concreteFiniteSpec := concreteFiniteSpec? then
      tactics := #[concreteFiniteSpec] ++ tactics
    if let some squareCubeSpec := squareCubeSpec? then
      tactics := #[squareCubeSpec] ++ tactics
    if let some counterexampleSpec := counterexampleSpec? then
      tactics := #[counterexampleSpec] ++ tactics
    if let some complexSpec := complexSpec? then
      tactics := #[complexSpec] ++ tactics
    if let some symmetricValueSpec := symmetricValueSpec? then
      tactics := #[symmetricValueSpec] ++ tactics
    if let some modularLeastSpec := modularLeastSpec? then
      tactics := #[modularLeastSpec] ++ tactics
    if let some natQuadraticSpec := natQuadraticSpec? then
      tactics := #[natQuadraticSpec] ++ tactics
    if let some nnrealRadicalSpec := nnrealRadicalSpec? then
      tactics := #[nnrealRadicalSpec] ++ tactics
    if let some realAbsSetSpec := realAbsSetSpec? then
      tactics := #[realAbsSetSpec] ++ tactics
    if let some integerAbsSetSpec := integerAbsSetSpec? then
      tactics := #[integerAbsSetSpec] ++ tactics
    if let some bilinearSpec := bilinearSpec? then
      tactics := #[bilinearSpec] ++ tactics
    if let some radicalSpec := radicalSpec? then
      tactics := #[radicalSpec] ++ tactics
    if let some logRatioSpec := logRatioSpec? then
      tactics := #[logRatioSpec] ++ tactics
    if let some intervalSpec ← boundedNatIntervalSpec? request then
      tactics := tactics ++ #[intervalSpec]
    let started ← IO.monoMsNow
    let leafBudgetMs := request.budgetMs
    let mut diagnostics := #[]
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
    (nativeLeafSolver config).solve request

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

/-- Mathlib tactics are attempted before the dependency-free native backend,
leaving the latter as a cheap structural and local-premise fallback. -/
def mathlibRouter (config : ProposeConfig) : LeafRouter := {
  backends := #[fastNatPowModLeafSolver, mathlibLeafSolver, atomicNativeLeafSolver config]
  preSnapshotBackends := #[fastNatPowModLeafSolver]
  modelSyntaxKinds := mathlibModelSyntaxKinds
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
