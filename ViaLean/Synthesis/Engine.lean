import ViaLean.Synthesis.Local

open Lean Meta

namespace ViaLean

structure SynthesizedTerm where
  term : Expr
  type : Expr
  depth : Nat
  origin : String
deriving Inhabited

structure LocalSynthesisResult where
  candidates : Array SynthesisCandidate := #[]
  discovered : Array SynthesizedTerm := #[]
  gaps : Array Expr := #[]
deriving Inhabited

namespace LocalSynthesizer

private def sameType (left right : Expr) : MetaM Bool := do
  let saved ← saveState
  let result ← try isDefEq left right catch _ => pure false
  saved.restore
  return result

private def pushTerm (terms : Array SynthesizedTerm) (candidate : SynthesizedTerm)
    (limit : Nat) : Array SynthesizedTerm :=
  if terms.size >= limit || terms.any (fun term => term.term == candidate.term) then terms
  else terms.push candidate

/-- Bounded typed closure over the local context. Each tick applies every newly
constructed function to compatible known terms and retains intermediate results. -/
def deriveUseful (snap : GoalSnapshot) (cfg : ProposeConfig) :
    MetaM (Array SynthesizedTerm) := snap.goalId.withContext do
  let limit := max 1 cfg.localSynthMaxTerms
  let mut pool : Array SynthesizedTerm := #[]
  for info in snap.locals do
    if pool.size >= limit then break
    pool := pushTerm pool {
      term := mkFVar info.fvarId
      type := ← instantiateMVars info.type
      depth := 0
      origin := s!"local:{info.userName}"
    } limit
  let mut frontier := pool
  for step in [0:cfg.localSynthDepth] do
    if frontier.isEmpty || pool.size >= limit then break
    let mut next : Array SynthesizedTerm := #[]
    for function in frontier do
      if pool.size + next.size >= limit then break
      match ← whnf function.type with
      | .forallE _ domain body _ =>
          for argument in pool do
            if pool.size + next.size >= limit then break
            let saved ← saveState
            let compatible ← try isDefEq argument.type domain catch _ => pure false
            if compatible then
              let term ← instantiateMVars (mkApp function.term argument.term)
              let type ← instantiateMVars (body.instantiate1 argument.term)
              saved.restore
              next := pushTerm next {
                term
                type
                depth := step + 1
                origin := s!"apply({function.origin},{argument.origin})"
              } (limit - min limit pool.size)
            else
              saved.restore
      | _ => pure ()
    for candidate in next do
      pool := pushTerm pool candidate limit
    frontier := next
  return pool

private partial def residualDomains (type : Expr) (fuel : Nat) :
    MetaM (Array Expr) := do
  if fuel == 0 then return #[]
  match ← whnf type with
  | .forallE _ domain body _ =>
      if body.hasLooseBVar 0 then return #[domain]
      return #[domain] ++ (← residualDomains body (fuel - 1))
  | _ => return #[]

private def pushCandidate (candidates : Array SynthesisCandidate)
    (candidate : SynthesisCandidate) (limit : Nat) : Array SynthesisCandidate :=
  if candidates.size >= limit || candidates.any (fun old => old.term == candidate.term) then
    candidates
  else candidates.push candidate

private def directConstructions (snap : GoalSnapshot)
    (pool : Array SynthesizedTerm) (limit : Nat) :
    MetaM (Array SynthesisCandidate) := snap.goalId.withContext do
  let mut result := #[]
  let target ← whnf snap.target
  if target.isAppOfArity "And".toName 2 then
    let args := target.getAppArgs
    for left in pool do
      if result.size >= limit then break
      if ← sameType left.type args[0]! then
        for right in pool do
          if result.size >= limit then break
          if ← sameType right.type args[1]! then
            try
              let proof ← mkAppM "And.intro".toName #[left.term, right.term]
              result := pushCandidate result {
                term := proof, operation := .exactTerm proof
                cost := left.depth + right.depth + 1 } limit
            catch _ => pure ()
  if target.isAppOfArity "Or".toName 2 then
    let args := target.getAppArgs
    for term in pool do
      if result.size >= limit then break
      if ← sameType term.type args[0]! then
        try
          let proof ← mkAppM "Or.inl".toName #[term.term]
          result := pushCandidate result {
            term := proof, operation := .exactTerm proof, cost := term.depth + 1 } limit
        catch _ => pure ()
      if result.size < limit && (← sameType term.type args[1]!) then
        try
          let proof ← mkAppM "Or.inr".toName #[term.term]
          result := pushCandidate result {
            term := proof, operation := .exactTerm proof, cost := term.depth + 1 } limit
        catch _ => pure ()
  if let some (_, predicate) := existsTarget? snap.target then
    for witness in pool do
      if result.size >= limit then break
      let property := mkApp predicate witness.term
      for evidence in pool do
        if result.size >= limit then break
        if ← sameType evidence.type property then
          try
            let proof ← mkAppM "Exists.intro".toName #[witness.term, evidence.term]
            result := pushCandidate result {
              term := proof, operation := .exactTerm proof
              cost := witness.depth + evidence.depth + 1 } limit
          catch _ => pure ()
  return result

/-- Enumerate complete inhabitants, partial applications and reusable typed terms. -/
def synthesizeDetailed (snap : GoalSnapshot) (cfg : ProposeConfig)
    (maxCandidates : Nat) : MetaM LocalSynthesisResult := snap.goalId.withContext do
  let limit := min maxCandidates cfg.localSynthMaxTerms
  if limit == 0 then return {}
  let pool ← deriveUseful snap cfg
  let mut candidates : Array SynthesisCandidate := #[]
  let mut gaps : Array Expr := #[]
  for term in pool do
    if candidates.size >= limit then break
    if ← sameType term.type snap.target then
      candidates := pushCandidate candidates {
        term := term.term, operation := .exactTerm term.term, cost := term.depth } limit
    else
      let obligations ← residualDomains term.type cfg.localSynthDepth
      unless obligations.isEmpty do
        candidates := pushCandidate candidates {
          term := term.term
          obligations
          operation := .sketch obligations
          cost := term.depth + obligations.size
        } limit
        for obligation in obligations do
          if gaps.size < cfg.localSynthMaxGaps &&
              !gaps.any (· == obligation) then gaps := gaps.push obligation
  for construction in ← directConstructions snap pool
      (limit - min limit candidates.size) do
    candidates := pushCandidate candidates construction limit
  if candidates.size < limit then
    if let some (_, lhs, rhs) := eqTarget? snap.target then
      if ← sameType lhs rhs then
        let proof ← mkAppM "Eq.refl".toName #[lhs]
        candidates := pushCandidate candidates {
          term := proof, operation := .simplifyTarget, cost := 0 } limit
  if candidates.size < limit && snap.target.isConstOf "True".toName then
    candidates := pushCandidate candidates {
      term := mkConst "True.intro".toName
      operation := .constructor "True.intro".toName
      cost := 0 } limit
  return { candidates, discovered := pool, gaps }

end LocalSynthesizer
end ViaLean
