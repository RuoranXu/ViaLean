import ViaLean

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  propose (directProbeSec := 0) via_eq b

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  propose (directProbeSec := 0)

-- The first local midpoint fails; its metavariable state must not leak into the next one.
example (_bad a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  propose (directProbeSec := 0) (candidateProbeSec := 1)
