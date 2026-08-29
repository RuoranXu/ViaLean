import ViaLean.Fingerprint
import ViaLean.Config

open Lean Meta

namespace ViaLean

def hasUnresolvedMVar (e : Expr) : MetaM Bool := do
  return (← instantiateMVars e).hasMVar

def validateCommon (cfg : ProposeConfig) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLooseBVar 0 || exprSize e > cfg.maxProposalSize then
    return none
  try
    discard <| inferType e
    return some e
  catch _ => return none

def validateCutType
    (cfg : ProposeConfig) (goal : GoalSnapshot) (candidate : Expr) : MetaM (Option Expr) := do
  let some candidate ← validateCommon cfg candidate | return none
  let candidateType ← whnf (← inferType candidate)
  unless candidateType.isSort do return none
  if !cfg.allowTypeCuts && !(← isProp candidate) then return none
  if ← isDefEq candidate goal.target then return none
  if candidate.isConstOf ``True then return none
  for info in goal.locals do
    if ← isDefEq info.type candidate then return none
  return some candidate

def eqTarget? (target : Expr) : Option (Expr × Expr × Expr) :=
  if target.isAppOfArity ``Eq 3 then
    let args := target.getAppArgs
    some (args[0]!, args[1]!, args[2]!)
  else none

def validateEqualityMid
    (cfg : ProposeConfig) (goal : GoalSnapshot) (candidate : Expr) : MetaM (Option Expr) := do
  let some (carrier, lhs, rhs) := eqTarget? goal.target | return none
  let some candidate ← validateCommon cfg candidate | return none
  unless ← isDefEq (← inferType candidate) carrier do return none
  if ← isDefEq candidate lhs then return none
  if ← isDefEq candidate rhs then return none
  return some candidate

def iffTarget? (target : Expr) : Option (Expr × Expr) :=
  if target.isAppOfArity ``Iff 2 then
    let args := target.getAppArgs
    some (args[0]!, args[1]!)
  else none

def validateIffMid
    (cfg : ProposeConfig) (goal : GoalSnapshot) (candidate : Expr) : MetaM (Option Expr) := do
  let some (lhs, rhs) := iffTarget? goal.target | return none
  let some candidate ← validateCommon cfg candidate | return none
  unless ← isProp candidate do return none
  if ← isDefEq candidate lhs then return none
  if ← isDefEq candidate rhs then return none
  return some candidate

def existsTarget? (target : Expr) : Option (Expr × Expr) :=
  if target.isAppOfArity ``Exists 2 then
    let args := target.getAppArgs
    some (args[0]!, args[1]!)
  else none

def validateWitness
    (cfg : ProposeConfig) (goal : GoalSnapshot) (candidate : Expr) : MetaM (Option Expr) := do
  let some (carrier, _) := existsTarget? goal.target | return none
  let some candidate ← validateCommon cfg candidate | return none
  unless ← isDefEq (← inferType candidate) carrier do return none
  return some candidate

end ViaLean
