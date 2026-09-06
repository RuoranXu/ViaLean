import ViaLean.Solver.Native

open Lean Meta

namespace ViaLean

structure LeafRouter where
  backends : Array LeafSolver
  /-- Strict, low-cost solvers that may run before a `GoalSnapshot` is built. -/
  preSnapshotBackends : Array LeafSolver := #[]
  /-- Exact, reviewed parser kinds that an optional integration may expose to
  the experimental model-code path. Forbidden syntax always remains forbidden;
  the dependency-free router grants no extensions. -/
  modelSyntaxKinds : Array Name := #[]
  /-- A stable policy hook for future portfolios. -/
  stopAfterSolved : Bool := true

def LeafRouter.nativeOnly (cfg : ProposeConfig) : LeafRouter :=
  { backends := #[nativeLeafSolver cfg] }

/-- Route a leaf through registered backends under one shared millisecond budget. -/
def LeafRouter.solve
    (router : LeafRouter) (request : SolverRequest) : MetaM SolverAttempt := do
  let started ← IO.monoMsNow
  let mut best : SolverAttempt := {
    backend := .custom "none"
    proof? := none
    solved := false
    elapsedMs := 0
  }
  let mut attempted := false
  for backend in router.backends do
    let elapsed := (← IO.monoMsNow) - started
    if elapsed ≥ request.budgetMs then break
    let saved ← getMCtx
    let attempt ← try
      tryBackend backend {
        request with budgetMs := request.budgetMs - elapsed
      }
    catch _ =>
      setMCtx saved
      pure {
        backend := backend.kind
        proof? := none
        solved := false
        elapsedMs := (← IO.monoMsNow) - started
      }
    if !attempted || attempt.progress > best.progress then best := attempt
    attempted := true
    if router.stopAfterSolved && attempt.solved && attempt.proof?.isSome then
      return attempt
  return { best with elapsedMs := (← IO.monoMsNow) - started }
/-- Run only strict pre-snapshot recognizers, under the same router budget rules. -/
def LeafRouter.solvePreSnapshot
    (router : LeafRouter) (request : SolverRequest) : MetaM SolverAttempt :=
  { router with
      backends := router.preSnapshotBackends
      preSnapshotBackends := #[] }.solve request

end ViaLean
