import ViaLean.Config

namespace ViaLean

initialize Lean.registerTraceClass `ViaLean
initialize Lean.registerTraceClass `ViaLean.proposal
initialize Lean.registerTraceClass `ViaLean.scheduler
initialize Lean.registerTraceClass `ViaLean.native
initialize Lean.registerTraceClass `ViaLean.external

end ViaLean
