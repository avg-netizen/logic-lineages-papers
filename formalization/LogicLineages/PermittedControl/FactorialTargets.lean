module
public import LogicLineages.PermittedControl.FactorialDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets

/-- The complete factorial branch of lem:control, plus the source proof's
factorial bound and exact integer interpretation. No tail-only growth shortcut. -/
def FactorialControlLaws : Prop :=
  (∀ (n : Nat), (factorialControl n : Int) =
    (Nat.factorial (G n) : Int) + 2 * (potential n : Int) - 2) ∧
  Primrec factorialControl ∧
  (∀ (n : Nat), 2 ∣ factorialControl n) ∧
  (∀ (n : Nat), G n ≤ factorialControl n) ∧
  (∀ (n : Nat), factorialControl n ≤ 2 * Nat.factorial (G n)) ∧
  (∀ (n : Nat), 2 ^ (2 ^ factorialControl n) ≤ factorialControl (n + 1)) ∧
  (∀ (n : Nat), factorialControl n < G (n + 1)) ∧
  (∀ (n : Nat), 101 ≤ n → factorialControl n ≤ OrdinalComparison.fastControl 6 n) ∧
  (∀ (m n : Nat), 0 < m → max m 0 ≤ n →
    Int.ModEq (m : Int) (potential (factorialControl n) : Int) ((potential n : Int) - 1))

/-- Unbounded iteration identity with the source threshold B_f=0. -/
def FactorialControlOrbit : Prop :=
  ∀ (m t i : Nat), 0 < m → max m 0 ≤ t →
    Int.ModEq (m : Int) (potential (factorialControl^[i] t) : Int)
      ((potential t : Int) - (i : Int))

end LogicLineages.PermittedControl.Targets
