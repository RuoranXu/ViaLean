import ViaLean.Basic

open Lean Meta

namespace ViaLean.SearchController

private partial def monitorBudgetCancellation
    (budget : Budget) (token : IO.CancelToken) (parent? : Option IO.CancelToken)
    (finished : IO.Ref Bool) : IO Unit := do
  if ← finished.get then return
  if let some parent := parent? then
    if ← parent.isSet then
      token.set
      return
  let remaining ← budget.remainingMs
  if remaining = 0 then
    token.set
  else
    IO.sleep (UInt32.ofNat (min 10 remaining))
    monitorBudgetCancellation budget token parent? finished

/-- Install one cancellation token over the complete search, including provider,
Atlas, premise retrieval, synthesis and solver calls. -/
def withinBudget? (budget : Budget) (action : MetaM α) : MetaM (Option α) := do
  let parentCancel? := (← readThe Core.Context).cancelTk?
  let localCancel ← IO.CancelToken.new
  let finished ← IO.mkRef false
  let _monitor ← IO.asTask
    (monitorBudgetCancellation budget localCancel parentCancel? finished) .dedicated
  -- Local budget cancellation uses Lean's interrupt exception, which deliberately
  -- bypasses ordinary `try`/`catch`. Catch it here so a local timeout becomes
  -- `none`, while the parent-interrupt branch below is still rethrown.
  let _ : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
  let attempt ← try
    let result ← withTheReader Core.Context (fun context =>
      { context with cancelTk? := some localCancel }) action
    pure (Except.ok result : Except Exception α)
  catch error => pure (Except.error error : Except Exception α)
  finished.set true
  match attempt with
  | .ok result =>
      if let some parent := parentCancel? then
        if ← parent.isSet then throwInterruptException
      if (← localCancel.isSet) || (← budget.remainingMs) = 0 then return none
      return some result
  | .error error =>
      if let some parent := parentCancel? then
        if ← parent.isSet then throw error
      if ← localCancel.isSet then return none
      throw error

end ViaLean.SearchController
