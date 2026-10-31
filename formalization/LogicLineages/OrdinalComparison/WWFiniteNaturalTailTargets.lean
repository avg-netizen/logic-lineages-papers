module
public import LogicLineages.OrdinalComparison.NaturalArithmeticDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Semantic calibration for the fixed-head finite-tail comparison in the
repaired source weak scalar lemma. The source scalar collapse uses natural
sum; finite right tails agree with ordinary ordinal addition. -/
def ActualNaturalSumFiniteRight : Prop :=
  ∀ (a : Ordinal.{0}) (k : Nat), ordinalNaturalSum a (k : Ordinal) = a + (k : Ordinal)

def ActualCollapseNaturalFiniteTailMonotone : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ r s : Nat, r ≤ s →
    actualCollapse (ordinalNaturalSum a (r : Ordinal)) ≤
      actualCollapse (ordinalNaturalSum a (s : Ordinal))

end LogicLineages.OrdinalComparison.Targets
