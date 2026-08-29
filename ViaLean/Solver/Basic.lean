import ViaLean.Config

open Lean Meta

namespace ViaLean

inductive SolverKind
  | native
  | leanTactic (name : String)
  | external (name : String)
  | custom (name : String)
deriving BEq, Hashable, Repr, Inhabited

structure SolverRequest where
  goal            : MVarId
  budgetMs        : Nat
  extraPremises   : Array Name := #[]
  wantDiagnostics : Bool := false

structure SolverAttempt where
  backend      : SolverKind
  proof?       : Option Expr
  solved       : Bool
  elapsedMs    : Nat
  progress     : Float := 0.0
  diagnostics? : Option String := none

structure LeafSolver where
  kind  : SolverKind
  solve : SolverRequest → MetaM SolverAttempt

def tryBackend (solver : LeafSolver) (request : SolverRequest) : MetaM SolverAttempt :=
  solver.solve request

end ViaLean
