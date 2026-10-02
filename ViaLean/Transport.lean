import ViaLean.Validate
import Lean.Meta.Tactic.Simp.Main

open Lean Meta

namespace ViaLean

/-- A small, kernel-checked fact obtained by transporting a local equality
through a local equivalence. These facts are shared by native search and the
model-visible proposal layer, so both sides reason about the same futures. -/
structure TransportFact where
  type   : Expr
  proof  : Expr
  source : String
deriving Inhabited

/-- Generate a bounded collection of normalized equality transports. The
implementation deliberately refers to `Equiv` by runtime names: core ViaLean
does not import mathlib, while environments that provide equivalences can use
the stronger closure without a compile-time dependency. -/
def equivTransportFacts
    (maxSources maxFacts maxSize : Nat) : MetaM (Array TransportFact) := do
  if maxSources = 0 || maxFacts = 0 then return #[]
  let env ← getEnv
  unless env.contains `Equiv && env.contains `Equiv.toFun &&
      env.contains `Equiv.invFun do
    return #[]
  let lctx ← getLCtx
  let mut equivalences : Array Expr := #[]
  let mut equalities : Array Expr := #[]
  let mut equalityTypes : Array Expr := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      if type.isAppOfArity `Equiv 2 && equivalences.size < maxSources then
        equivalences := equivalences.push (mkFVar decl.fvarId)
      if type.isEq && equalities.size < maxSources then
        equalities := equalities.push (mkFVar decl.fvarId)
        equalityTypes := equalityTypes.push type
  let mut facts : Array TransportFact := #[]
  for equivalence in equivalences do
    let forward ← mkAppM `Equiv.toFun #[equivalence]
    let backward ← mkAppM `Equiv.invFun #[equivalence]
    let functions : Array (Expr × String) :=
      #[(forward, "forward"), (backward, "backward")]
    -- Interleave the two directions for each source equality. A small fact
    -- budget therefore still exposes qualitatively different futures.
    for equality in equalities do
      for (function, direction) in functions do
        if facts.size ≥ maxFacts then return facts
        let saved ← saveState
        try
          let rawProof ← mkAppM ``congrArg #[function, equality]
          let rawType ← instantiateMVars (← inferType rawProof)
          let simpCtx ← Simp.Context.mkDefault
          let (simplified, _) ← simp rawType simpCtx
          let factType ← instantiateMVars simplified.expr
          unless factType.isEq do
            saved.restore
            continue
          if exprSize factType > maxSize ||
              equalityTypes.any (fun type => type == factType) ||
              facts.any (fun fact => fact.type == factType) then
            saved.restore
            continue
          let some (_, lhs, rhs) := eqTarget? factType | unreachable!
          if ← isDefEq lhs rhs then
            saved.restore
            continue
          let proof ← simplified.mkEqMP rawProof
          let proof ← finalizeProof factType proof
          facts := facts.push {
            type := factType
            proof
            source := s!"equiv-transport-{direction}"
          }
        catch _ =>
          saved.restore
  return facts

end ViaLean
