import ViaLean.Search.State
import Lean.Parser

open Lean

namespace ViaLean

structure ModelCodeAttempt where
  proof? : Option Expr := none
  outcome : String := "failed"
  detail : String := ""

def boundedText (limit : Nat) (text : String) : String :=
  if text.length <= limit then text else (text.take limit).toString ++ "…"

private def forbiddenModelSyntaxKind (kind : Name) : Bool :=
  let name := kind.toString.toLower
  name.contains "runtac" || name.contains "run_tac" || name.contains "eval" ||
  name.contains "native" || name.contains "setoption" || name.contains "set_option" ||
  name.contains "sleep" || name.contains "command" || name.contains "syntaxquotation" ||
  name.contains "macro"

/-- Exact syntax kinds supported by the experimental raw-code compatibility path.
Namespace-prefix checks are deliberately forbidden: extensions must be reviewed explicitly. -/
private def allowedModelSyntaxKinds : Array String := #[
  "null", "group", "num", "scientific", "str", "char",
  "Lean.Parser.Term.byTactic", "Lean.Parser.Term.app", "Lean.Parser.Term.paren",
  "Lean.Parser.Term.explicit", "Lean.Parser.Term.namedArgument", "Lean.Parser.Term.typed",
  "Lean.Parser.Term.fun", "Lean.Parser.Term.funBinder", "Lean.Parser.Term.bracketedBinder",
  "Lean.Parser.Term.explicitBinder", "Lean.Parser.Term.implicitBinder",
  "Lean.Parser.Term.strictImplicitBinder", "Lean.Parser.Term.anonymousCtor",
  "Lean.Parser.Term.tuple", "Lean.Parser.Term.proj", "Lean.Parser.Term.arrow",
  "Lean.Parser.Term.let", "Lean.Parser.Term.letDecl", "Lean.Parser.Term.have",
  "Lean.Parser.Term.show", "Lean.Parser.Term.calc", "Lean.Parser.Term.calcStep",
  "Lean.Parser.Tactic.tacticSeq", "Lean.Parser.Tactic.tacticSeq1Indented",
  "Lean.Parser.Tactic.tacticSeqBracketed", "Lean.Parser.Tactic.tactic_<;>_",
  "Lean.Parser.Tactic.exact", "Lean.Parser.Tactic.apply", "Lean.Parser.Tactic.intro",
  "Lean.Parser.Tactic.constructor", "Lean.Parser.Tactic.cases",
  "Lean.Parser.Tactic.elimTarget", "Lean.Parser.Tactic.inductionAlts",
  "Lean.Parser.Tactic.inductionAlt", "Lean.Parser.Tactic.inductionAltLHS",
  "Lean.Parser.Tactic.rwSeq", "Lean.Parser.Tactic.rwRuleSeq", "Lean.Parser.Tactic.rwRule",
  "Lean.Parser.Tactic.simp", "Lean.Parser.Tactic.simpa", "Lean.Parser.Tactic.simpaArgsRest",
  "Lean.Parser.Tactic.simpArgs", "Lean.Parser.Tactic.simpArg",
  "Lean.Parser.Tactic.simpLocation", "Lean.Parser.Tactic.optConfig",
  "Lean.Parser.Tactic.assumption", "Lean.Parser.Tactic.contradiction",
  "Lean.Parser.Tactic.rfl", "Lean.Parser.Tactic.simpAll"
]

private def allowedModelSyntaxKind (kind : Name) : Bool :=
  kind.isAnonymous || allowedModelSyntaxKinds.contains kind.toString

private partial def validateModelSyntax (stx : Syntax) : Except String Unit := do
  match stx with
  | .missing | .atom .. | .ident .. => pure ()
  | .node _ kind args =>
      if forbiddenModelSyntaxKind kind then
        throw s!"unsafe Lean syntax is not permitted for model code: {kind}"
      unless allowedModelSyntaxKind kind do
        throw s!"unsupported non-core syntax in model code: {kind}"
      for arg in args do validateModelSyntax arg

/-- Parse model text as a small reviewed core tactic subset. Execution remains opt-in. -/
def parseSafeModelTactic (env : Environment) (code : String) : Except String Syntax := do
  let wrapped := if code.startsWith "by" then code else "by\n  " ++ code
  let term ← Parser.runParserCategory env `term wrapped
  validateModelSyntax term
  match term with
  | .node _ kind args =>
      unless kind.toString == "Lean.Parser.Term.byTactic" do
        throw "model Lean code must be a by-proof or a tactic sequence"
      let some tactics := args[1]? | throw "malformed by-proof"
      return tactics
  | _ => throw "model Lean code must be a by-proof or a tactic sequence"

end ViaLean
