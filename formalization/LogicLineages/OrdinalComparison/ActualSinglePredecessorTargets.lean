module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section

/-! Paper 05, `foundations.tex`, `thm:single-predecessor`, lines 210–232.

The complete source recurrence for the actual unary collapse, actual-CNF norm,
and independently defined actual finite maximum. The finite tail uses ordinary
ordinal addition, not natural addition; every natural n, including zero, is
quantified. This target imports no recurrence proof or assumed recurrence and
asserts no optimized-algorithm or encoded-effectiveness result.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualSinglePredecessorRecurrence : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a → ∀ n : Nat,
    actualCollapse (a + (n : Ordinal)) =
      actualCollapse (actualMaximumPredecessor a (Phi (actualOrdinalNorm a + n))) + 1

end LogicLineages.OrdinalComparison.Targets
