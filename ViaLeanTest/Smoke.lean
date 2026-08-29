import ViaLean

example : Nat := by
  propose (timeoutSec := 5)

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  propose (timeoutSec := 5)

example (p : Prop) (hp : p) : p := by
  propose? (directProbeSec := 0)
  exact hp

example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  propose (timeoutSec := 5)

example (α : Type) (x : α) : ∃ y : α, y = x := by
  propose (timeoutSec := 5)
