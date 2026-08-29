import ViaLean

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  propose (directProbeSec := 0) (structural := true)

example (p : Prop) : p → p := by
  propose (directProbeSec := 0) (structural := true)

example (p q : Prop) (h : p ↔ q) : p ↔ q := by
  propose (directProbeSec := 0) (structural := true)
