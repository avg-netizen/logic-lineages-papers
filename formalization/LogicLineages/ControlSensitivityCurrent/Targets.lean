module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.Targets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.PerturbedControl

/-- Current paper19 `lem:perturbed-control`, all displayed and prose clauses.
The exact old `control` is reused, not redefined. Universal primitive-recursive
Boolean H strengthens the fixed bounded simulation H used by this lemma;
no halting or comparison-hardness assertion is part of this target. -/
def FullPerturbedControl : Prop :=
  ∀ (H : Nat × Nat → Bool), Primrec H → ∀ b : Nat,
    Primrec (control b H) ∧
    (∀ n : Nat, n ≤ b → control b H n = Phi n) ∧
    (∀ n : Nat, 0 ≤ control b H n - Phi n ∧ control b H n - Phi n ≤ 1) ∧
    (∀ n : Nat, Phi n ≤ control b H n ∧ control b H n < Phi (n + 1)) ∧
    (∀ n : Nat, 2 ^ (2 ^ control b H n) ≤ control b H (n + 1)) ∧
    (∀ v a : Nat, 1 ≤ a → control b H v + 2 * a ≤ control b H (v + a)) ∧
    (∀ n : Nat, 101 ≤ n → control b H n ≤ fastControl 6 n) ∧
    RatioLimit b H
end LogicLineages.ControlSensitivityCurrent.Targets
