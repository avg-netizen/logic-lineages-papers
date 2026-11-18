module
public import LogicLineages.PermittedControl.Definitions
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets

/-- Remaining numerical estimates for the literal near-standard control.
The explicit eventual bound is stronger than an unspecified finite-level bound;
primitive recursiveness and the distinct factorial control are not included. -/
def NearControlGrowth : Prop :=
  (∀ (n : Nat), initialLcm n ≤ Nat.factorial n ∧ 2 * Nat.factorial n ≤ G n) ∧
  (∀ (b n : Nat), nearControl b n < 2 * G n) ∧
  (∀ (b n : Nat), 2 ^ (2 ^ nearControl b n) ≤ nearControl b (n + 1)) ∧
  (∀ (b n : Nat), nearControl b n < G (n + 1)) ∧
  (∀ (b n : Nat), 101 ≤ n → nearControl b n ≤ OrdinalComparison.fastControl 6 n)

end LogicLineages.PermittedControl.Targets
