import ViaLean.Premise.Basic
import Lean.LibrarySuggestions

open Lean Meta Lean.LibrarySuggestions

namespace ViaLean

private partial def collectConstants (e : Expr) (found : NameSet := {}) : NameSet :=
  match e with
  | .const name _ => found.insert name
  | .app f a => collectConstants a (collectConstants f found)
  | .lam _ d b _ | .forallE _ d b _ => collectConstants b (collectConstants d found)
  | .letE _ t v b _ => collectConstants b (collectConstants v (collectConstants t found))
  | .mdata _ e | .proj _ _ e => collectConstants e found
  | _ => found

/-- Retain symbol-relevant declarations from the current file without scanning the
imported environment.  This complements Lean's ranked selector for both kernel
axioms (common in abstract interfaces) and small bridge theorems that become
applicable only after a structural split. -/
private def currentFileDeclarations
    (goal : GoalSnapshot) (limit : Nat) : MetaM (Array PremiseCandidate) := do
  if limit = 0 then return #[]
  let mut goalSymbols := collectConstants goal.target
  for info in goal.locals do
    goalSymbols := collectConstants info.type goalSymbols
  let env ← getEnv
  let mut result := #[]
  for (name, info) in env.constants.map₂.toList do
    if name == "sorryAx".toName || name.isInternalDetail then continue
    let type? := match info with
      | .axiomInfo value => some value.type
      | .thmInfo value => some value.type
      | _ => none
    let some type := type? | continue
    let symbols := collectConstants type
    let mut overlap := 0
    for symbol in symbols.toArray do
      if goalSymbols.contains symbol then overlap := overlap + 1
    if overlap > 0 then
      result := result.push {
        name
        score := 1.0 + Float.ofNat overlap / 100.0
        source := "current-file-declaration"
      }
  return (result.insertionSort fun a b => a.score > b.score).take limit

def libraryPremiseProvider : PremiseProvider where
  name := "Lean.LibrarySuggestions"
  retrieve goal limit := do
    let suggestions ← select goal.goalId { maxSuggestions := limit }
    let selected := (suggestions.map fun suggestion => {
      name := suggestion.name
      score := suggestion.score
      source := "Lean.LibrarySuggestions"
    }).insertionSort fun a b => a.score > b.score
    let currentFile ← currentFileDeclarations goal limit
    let combined := (currentFile ++ selected).insertionSort fun a b => a.score > b.score
    let mut result := #[]
    let mut seen : NameSet := {}
    for candidate in combined do
      if result.size ≥ limit then break
      unless seen.contains candidate.name do
        seen := seen.insert candidate.name
        result := result.push candidate
    return result

end ViaLean
