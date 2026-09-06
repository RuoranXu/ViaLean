import ViaLean.Model.Protocol

namespace ViaLean.SearchReplay

/-- Resolve replay references against the exact offered action array. Unknown or
out-of-range IDs are inert and never become executable model code. -/
def resolveAction (selection : ModelSelection)
    (actions : Array ProofAction) : Option ProofAction :=
  match selection.actionId? with
  | some id => actions.find? fun action => action.fingerprint == id
  | none => selection.index?.bind fun index => actions[index]?

/-- Only probes marked executable may cross the replay boundary. -/
def resolveProbe (selection : ModelSelection)
    (frontier : Array FrontierProbe) : Option FrontierProbe :=
  match selection.probeId? with
  | some id => frontier.find? fun probe => probe.id == id && probe.executable
  | none =>
      selection.probeIndex?.bind fun index =>
        frontier[index]?.filter fun probe => probe.executable

end ViaLean.SearchReplay
