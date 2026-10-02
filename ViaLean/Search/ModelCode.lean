import ViaLean.Search.State
import ViaLean.Model.Syntax

open Lean

namespace ViaLean

structure ModelCodeAttempt where
  proof? : Option Expr := none
  outcome : String := "failed"
  detail : String := ""

def boundedText (limit : Nat) (text : String) : String :=
  if text.length <= limit then text else (text.take limit).toString ++ "…"

end ViaLean
