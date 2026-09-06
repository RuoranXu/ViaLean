import ViaLean.Basic

open Lean Meta

namespace ViaLean.ExecutionBoundary

/-- Discard messages produced by speculative work while preserving its result
and successful metavariable assignments. Exceptions are rethrown after cleanup. -/
def withoutSpeculativeMessages (action : MetaM α) : MetaM α := do
  let initialLog ← Core.getMessageLog
  try
    let result ← action
    Core.setMessageLog initialLog
    return result
  catch ex =>
    Core.setMessageLog initialLog
    throw ex

/-- Run a speculative Meta branch transactionally. A failed result or exception
restores the metavariable context; successful proofs still cross finalizeProof. -/
def observingMeta? (action : MetaM (Option α)) : MetaM (Option α) := do
  let saved ← getMCtx
  try
    let result ← withoutSpeculativeMessages action
    if result.isNone then setMCtx saved
    return result
  catch _ =>
    setMCtx saved
    return none

end ViaLean.ExecutionBoundary
