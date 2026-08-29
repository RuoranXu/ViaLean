import ViaLean.Premise.Basic
import Lean.LibrarySuggestions

open Lean Meta Lean.LibrarySuggestions

namespace ViaLean

def libraryPremiseProvider : PremiseProvider where
  name := "Lean.LibrarySuggestions"
  retrieve goal limit := do
    let suggestions ← select goal.goalId
    let suggestions := suggestions.insertionSort (fun a b => a.score > b.score)
    return (suggestions.take limit).map fun suggestion => {
      name := suggestion.name
      score := suggestion.score
      source := "Lean.LibrarySuggestions"
    }

end ViaLean
