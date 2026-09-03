import ViaLean.Basic

open Lean Meta

namespace ViaLean

inductive LocalKeyKind
  | local
  | letDecl
deriving BEq, Hashable, Repr, Inhabited

/-- Name-insensitive semantic content of a local declaration. -/
structure LocalKey where
  kind   : LocalKeyKind
  type   : Expr
  value? : Option Expr := none
deriving BEq, Hashable, Repr, Inhabited

/-- Strict proof-state identity used for cycles and transpositions.
The expressions are canonicalized over local free variables and binder names. -/
structure GoalKey where
  target : Expr
  locals : Array LocalKey
deriving BEq, Hashable, Repr, Inhabited

private partial def eraseBinderNames : Expr → Expr
  | .forallE _ domain body info =>
      .forallE .anonymous (eraseBinderNames domain) (eraseBinderNames body) info
  | .lam _ domain body info =>
      .lam .anonymous (eraseBinderNames domain) (eraseBinderNames body) info
  | .letE _ type value body nondep =>
      .letE .anonymous (eraseBinderNames type) (eraseBinderNames value)
        (eraseBinderNames body) nondep
  | .app fn arg => .app (eraseBinderNames fn) (eraseBinderNames arg)
  | .mdata _ body => eraseBinderNames body
  | .proj typeName index body => .proj typeName index (eraseBinderNames body)
  | expr => expr

private def canonicalizeLocals (fvars : Array Expr) (expr : Expr) : Expr := Id.run do
  let mut replacements : Array Expr := #[]
  for index in [0:fvars.size] do
    replacements := replacements.push (mkBVar index)
  return eraseBinderNames (expr.replaceFVars fvars replacements)

/-- Build the only strict goal identity used by ViaLean. Let values are semantic. -/
def mkGoalKey (goal : MVarId) : MetaM GoalKey := goal.withContext do
  let mut fvars : Array Expr := #[]
  let mut locals : Array LocalKey := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      let value? ← decl.value? (allowNondep := true).mapM instantiateMVars
      locals := locals.push {
        kind := if decl.isLet then .letDecl else .local
        type := canonicalizeLocals fvars type
        value? := value?.map (canonicalizeLocals fvars)
      }
      fvars := fvars.push (mkFVar decl.fvarId)
  let target ← instantiateMVars (← goal.getType)
  return {
    target := canonicalizeLocals fvars target
    locals
  }

def GoalKey.bucket (key : GoalKey) : UInt64 := hash key

def GoalKey.strictEq (left right : GoalKey) : Bool := left == right

/-- Hash-indexed set whose membership always confirms the full strict key. -/
structure StrictGoalSet where
  buckets : Std.HashMap UInt64 (Array GoalKey) := {}
deriving Inhabited

def StrictGoalSet.containsAt (set : StrictGoalSet) (bucket : UInt64) (key : GoalKey) : Bool :=
  (set.buckets.get? bucket).any fun keys => keys.any (·.strictEq key)

def StrictGoalSet.contains (set : StrictGoalSet) (key : GoalKey) : Bool :=
  set.containsAt key.bucket key

def StrictGoalSet.insertAt
    (set : StrictGoalSet) (bucket : UInt64) (key : GoalKey) : StrictGoalSet :=
  if set.containsAt bucket key then set
  else
    let keys := (set.buckets.get? bucket).getD #[]
    { buckets := set.buckets.insert bucket (keys.push key) }

def StrictGoalSet.insert (set : StrictGoalSet) (key : GoalKey) : StrictGoalSet :=
  set.insertAt key.bucket key

end ViaLean
