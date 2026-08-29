import ViaLean

example (A B C : Prop) (h₁ : A → B) (h₂ : B → C) (a : A) : C := by
  propose (directProbeSec := 0) via_cut B

example (A B C : Prop) (h₁ : A → B) (h₂ : B → C) (a : A) : C := by
  propose (directProbeSec := 0) (structural := false)
