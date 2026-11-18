module
public import LogicLineages.PermittedControl.EvaluatorDefinitions
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

/-- Printed cor:finite-coefficient with every natural coefficient and tail.
Computability is unnecessary for this mathematical identity. -/
def FiniteCoefficient : Prop :=
  ∀ (f : Nat → Nat), StrictMono f → (∀ n, G n ≤ f n) → ∀ (k n : Nat),
    collapseWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) = f^[k] (2 * k + n) + k

/-- Literal event count, excluding the finite predecessor chain, and endpoint. -/
def FiniteCoefficientTerminal : Prop :=
  ∀ (f : Nat → Nat), StrictMono f → (∀ n, G n ≤ f n) → ∀ (k n : Nat),
    (terminalWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))).2 = k ∧
    (terminalWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))).1 = f^[k] (2 * k + n)

/-- Explicit source controls, without a supplied admissibility premise. -/
def SelectedFiniteCoefficient : Prop :=
  ∀ (f : Nat → Nat), (f = factorialControl ∨ ∃ b : Nat, f = nearControl b) → ∀ (k n : Nat),
    collapseWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) = f^[k] (2 * k + n) + k ∧
    (terminalWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))).2 = k ∧
    (terminalWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))).1 = f^[k] (2 * k + n)

end LogicLineages.PermittedControl.Targets
