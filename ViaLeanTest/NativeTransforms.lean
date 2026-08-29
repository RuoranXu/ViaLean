import ViaLean

open ViaLean

example (P Q : Prop) (hp : P) (hnp : ¬ P) : Q := by
  propose
    (timeoutSec := 5)
    (structural := false)
    (cuts := false)
    (library := false)

example {α β : Type} (f : α → β) (a b : α) (h : a = b) : f a = f b := by
  propose
    (timeoutSec := 5)
    (structural := false)
    (cuts := false)
    (library := false)

example (n : Nat) : Nat.succ (n + 0) = Nat.succ n := by
  propose
    (timeoutSec := 5)
    (structural := false)
    (cuts := false)
    (library := false)

example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  propose
    (timeoutSec := 5)
    (structural := false)
    (cuts := false)
    (library := false)

example (α : Type) (p : α → Prop) (R : Prop)
    (h : ∃ x, p x) (use : ∀ x, p x → R) : R := by
  propose
    (timeoutSec := 5)
    (structural := false)
    (cuts := false)
    (library := false)