import Mathlib.Order.Defs.PartialOrder

/-! A minimal standard-library import probe for measuring compiler resources. -/
example : (1 : Nat) ≤ 1 := Nat.le_refl 1
