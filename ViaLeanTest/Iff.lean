import ViaLean

example (A M B : Prop) (h₁ : A ↔ M) (h₂ : M ↔ B) : A ↔ B := by
  propose (directProbeSec := 0) (structural := false)

example (A M B : Prop) (h₁ : A ↔ M) (h₂ : M ↔ B) : A ↔ B := by
  propose (directProbeSec := 0) via_iff M
