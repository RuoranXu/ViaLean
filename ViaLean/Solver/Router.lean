import ViaLean.Solver.Native

open Lean Meta

namespace ViaLean

structure LeafRouter where
  backends : Array LeafSolver
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
  for backend in router.backends do
    let elapsed := (← IO.monoMsNow) - started
    if elapsed ≥ request.budgetMs then break
    let attempt ← tryBackend backend {
      request with budgetMs := request.budgetMs - elapsed
    }
    if attempt.progress > best.progress then best := attempt
    if router.stopAfterSolved && attempt.solved && attempt.proof?.isSome then
      return attempt
  return { best with elapsedMs := (← IO.monoMsNow) - started }

end ViaLean
