module
public import LogicLineages.OrdinalComparison.ControlDefinitions
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Data.Nat.Basic

@[expose] public section

/-! Independent numerical statement, kept free of the ordinal library so it
can be checked on its own. The full source lemma additionally asserts a
computability property; this target is its exact numerical portion. -/

namespace LogicLineages.OrdinalComparison.Targets

def NumericalControlGrowth : Prop :=
  StrictMono Phi ∧ ∀ n : Nat,
    n < Phi n ∧ 2 ^ (n + 100) ≤ Phi n ∧ 2 ^ (2 ^ Phi n) ≤ Phi (n + 1)

end LogicLineages.OrdinalComparison.Targets
