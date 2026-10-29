module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section

/-! Paper 05, `foundations.tex`, `cor:finite-head`, lines 265–277.

The norm and sufficient-budget maximum formulas are separately stated suppliers
for the full collapse identity; the final identity does not assume them as
premises. All arithmetic on Ordinal is ordinary, with finite coefficients on
the right of omega. Every natural k,n is included, in particular k=0.
These are exact symbolic statements, not evaluation of huge control values,
and assert no separate encoded-effectiveness certificate.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualFiniteHeadNorm : Prop :=
  ∀ k n : Nat,
    actualOrdinalNorm (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) = 2 * k + n

def ActualFiniteHeadMaximum : Prop :=
  ∀ k b : Nat, 2 * (k + 1) ≤ b →
    actualMaximumPredecessor (Ordinal.omega0 * ((k + 1 : Nat) : Ordinal)) b =
      Ordinal.omega0 * (k : Ordinal) + ((b - 2 * k : Nat) : Ordinal)

def ActualFiniteHeadCollapse : Prop :=
  ∀ k n : Nat,
    actualCollapse (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) =
      (Phi^[k]) (2 * k + n) + k

end LogicLineages.OrdinalComparison.Targets
