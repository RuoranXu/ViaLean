import ViaLean

example (a b : Nat) (h : a = b) : a = b := by
  propose

example (A : Prop) (h : A) : A := by
  propose (directProbeSec := 0)

example (n : Nat) : ∃ x : Nat, x = n := by
  propose (directProbeSec := 0)
