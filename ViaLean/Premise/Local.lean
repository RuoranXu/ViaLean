import ViaLean.Premise.Basic

open Lean Meta

namespace ViaLean

private partial def collectConstants (e : Expr) (found : NameSet := {}) : NameSet :=
  match e with
  | .const name _ => found.insert name
  | .app f a => collectConstants a (collectConstants f found)
  | .lam _ d b _ | .forallE _ d b _ => collectConstants b (collectConstants d found)
  | .letE _ t v b _ => collectConstants b (collectConstants v (collectConstants t found))
  | .mdata _ e | .proj _ _ e => collectConstants e found
  | _ => found

def localPremiseProvider : PremiseProvider where
  name := "local-symbols"
  retrieve goal limit := do
    let mut names := collectConstants goal.target
    for info in goal.locals do
      names := collectConstants info.type names
    let env ← getEnv
    let mut result := #[]
    for name in names.toArray do
      if env.contains name then
        result := result.push { name, score := 0.5, source := "local-symbols" }
    return result.take limit

end ViaLean
