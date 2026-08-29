import ViaLean

example (n : Nat) : ∃ x : Nat, x = n := by
  propose (directProbeSec := 0) via_witness n
