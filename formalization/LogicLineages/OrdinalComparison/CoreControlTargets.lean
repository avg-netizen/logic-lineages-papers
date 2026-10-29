module
public import LogicLineages.OrdinalComparison.ControlDefinitions

@[expose] public section

/-!
# The numerical target with order terminology fully expanded

This is the same numerical source property as `NumericalControlGrowth`:
the first conjunct writes strict monotonicity directly. It does not need
the general Mathlib order hierarchy merely to state a natural-number fact.
No proof implementation is imported.
-/

namespace LogicLineages.OrdinalComparison.Targets

def CoreNumericalGrowth : Prop :=
  (∀ n m : Nat, n < m → Phi n < Phi m) ∧
  ∀ n : Nat, n < Phi n ∧ 2 ^ (n + 100) ≤ Phi n ∧
    2 ^ (2 ^ Phi n) ≤ Phi (n + 1)

end LogicLineages.OrdinalComparison.Targets
