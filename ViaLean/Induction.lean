import Lean.Meta.Tactic.Induction

open Lean Meta

namespace ViaLean

/-- Induction is informative only when the major premise occurs structurally.
For equality goals, a bare side such as x = y should use equality reasoning
rather than recursively splitting either variable. -/
def targetBenefitsFromInduction (target : Expr) (major : FVarId) : MetaM Bool := do
  if target.isAppOfArity "Eq".toName 3 then
    let args := target.getAppArgs
    let lhs := args[1]!
    let rhs := args[2]!
    let majorExpr := mkFVar major
    return ((← exprDependsOn lhs major) && lhs != majorExpr) ||
      ((← exprDependsOn rhs major) && rhs != majorExpr)
  return (← exprDependsOn target major)

/-- Return the generated recursor for a genuinely recursive inductive type.
This is intentionally type-directed: callers do not need to know whether the
major premise is a natural number, a list, a tree, or a project-defined type. -/
def inductionRecursor? (type : Expr) : MetaM (Option Name) := do
  let type ← whnf (← instantiateMVars type)
  let .const typeName _ := type.getAppFn | return none
  match (← getEnv).find? typeName with
  | some (.inductInfo info) =>
      if !info.isRec then return none
      let recursor := mkRecName typeName
      match (← getEnv).find? recursor with
      | some (.recInfo _) => return some recursor
      | _ => return none
  | _ => return none

end ViaLean