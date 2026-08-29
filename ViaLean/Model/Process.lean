import ViaLean.Model.Protocol

namespace ViaLean

structure BoundedProcessOutput where
  exitCode : UInt32
  stdout   : String
  stderr   : String

deriving Inhabited

private def boundedStderr (text : String) : String :=
  if text.length ≤ 1000 then text else (text.take 1000).toString ++ "…"

/-- Run a provider process without a shell and terminate it when its budget expires. -/
def runBoundedProcess
    (cmd : String) (args : Array String) (input : String)
    (timeoutMs : Nat) (maxOutputChars : Nat := 65536) :
    IO (Except String BoundedProcessOutput) := do
  if cmd.isEmpty then return .error "model command is empty"
  if timeoutMs = 0 then return .error "model process budget is exhausted"
  try
    let spawned ← IO.Process.spawn {
      cmd
      args
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let (stdin, child) ← spawned.takeStdin
    stdin.putStr input
    stdin.flush
    let stdoutTask ← IO.asTask child.stdout.readToEnd .dedicated
    let stderrTask ← IO.asTask child.stderr.readToEnd .dedicated
    let quantum := 10
    let ticks := (timeoutMs + quantum - 1) / quantum
    let rec waitLoop : Nat → IO (Option UInt32)
      | 0 => child.tryWait
      | n + 1 => do
          match ← child.tryWait with
          | some code => return some code
          | none =>
              IO.sleep (UInt32.ofNat quantum)
              waitLoop n
    match ← waitLoop ticks with
    | some exitCode =>
        let stdout ← IO.ofExcept stdoutTask.get
        let stderr ← IO.ofExcept stderrTask.get
        if stdout.length > maxOutputChars then
          return .error s!"model response exceeds {maxOutputChars} characters"
        if exitCode = 0 then
          return .ok { exitCode, stdout, stderr }
        return .error s!"model process exited with {exitCode}: {boundedStderr stderr}"
    | none =>
        child.kill
        discard child.wait
        discard <| IO.ofExcept stdoutTask.get
        discard <| IO.ofExcept stderrTask.get
        return .error s!"model process timed out after {timeoutMs}ms"
  catch error =>
    return .error s!"model process failed: {error}"

end ViaLean