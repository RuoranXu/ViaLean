import ViaLean.Model.Protocol

namespace ViaLean

structure BoundedProcessOutput where
  exitCode : UInt32
  stdout   : String
  stderr   : String

deriving Inhabited

private def boundedStderr (text : String) : String :=
  if text.length ≤ 1000 then text else (text.take 1000).toString ++ "…"

private partial def drainStream (handle : IO.FS.Handle) : IO Unit := do
  let chunk ← handle.read 4096
  unless chunk.isEmpty do drainStream handle

/-- Read incrementally. At most four UTF-8 bytes per allowed character plus one sentinel byte
are retained, so an untrusted provider cannot force an unbounded `readToEnd` allocation. -/
private partial def readBounded
    (handle : IO.FS.Handle) (maxChars : Nat)
    (overflow? : Option (IO.Ref Bool) := none) : IO String := do
  let byteLimit := maxChars * 4
  let rec loop (acc : ByteArray) : IO String := do
    let room := byteLimit + 1 - min (byteLimit + 1) acc.size
    let readSize := max 1 (min 4096 room)
    let chunk ← handle.read readSize.toUSize
    if chunk.isEmpty then
      match String.fromUTF8? acc with
      | some text => return text
      | none => throw <| IO.userError "model process emitted invalid UTF-8"
    let next := acc ++ chunk
    let overflowed := next.size > byteLimit ||
      match String.fromUTF8? next with
      | some text => text.length > maxChars
      | none => false
    if overflowed then
      if let some flag := overflow? then flag.set true
      let prefixText := (String.fromUTF8? acc).getD ""
      drainStream handle
      return prefixText
    loop next
  loop .empty

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
    let child ← do
      let (stdin, child) ← spawned.takeStdin
      stdin.putStr input
      stdin.flush
      pure child
    let stdoutOverflow ← IO.mkRef false
    let stdoutTask ← IO.asTask (readBounded child.stdout maxOutputChars (some stdoutOverflow)) .dedicated
    let stderrTask ← IO.asTask (readBounded child.stderr 1000) .dedicated
    let quantum := 10
    let ticks := (timeoutMs + quantum - 1) / quantum
    let rec waitLoop : Nat → IO (Option UInt32)
      | 0 => child.tryWait
      | n + 1 => do
          if ← stdoutOverflow.get then return none
          else
            match ← child.tryWait with
            | some code => return some code
            | none =>
                IO.sleep (UInt32.ofNat quantum)
                waitLoop n
    match ← waitLoop ticks with
    | some exitCode =>
        let stdout ← IO.ofExcept stdoutTask.get
        let stderr ← IO.ofExcept stderrTask.get
        if (← stdoutOverflow.get) || stdout.length > maxOutputChars then
          return .error s!"model response exceeds {maxOutputChars} characters"
        if exitCode = 0 then
          return .ok { exitCode, stdout, stderr }
        return .error s!"model process exited with {exitCode}: {boundedStderr stderr}"
    | none =>
        try child.kill catch _ => pure ()
        discard child.wait
        discard <| IO.ofExcept stdoutTask.get
        discard <| IO.ofExcept stderrTask.get
        if ← stdoutOverflow.get then
          return .error s!"model response exceeds {maxOutputChars} characters"
        return .error s!"model process timed out after {timeoutMs}ms"
  catch error =>
    return .error s!"model process failed: {error}"

end ViaLean
