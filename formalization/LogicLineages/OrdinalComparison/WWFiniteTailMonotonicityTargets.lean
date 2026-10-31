module
public import LogicLineages.OrdinalComparison.ActualCollapseBoundsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Exact cited supplier for source-syntax.tex wwsc:thm:weak: ordinary finite
right-tail growth of the actual unary collapse below epsilon zero. This is
not global ordinal monotonicity and imposes no assumption on a selector. -/
def ActualCollapseFiniteTailIncrement : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ k : Nat,
    actualCollapse a + k ≤ actualCollapse (a + (k : Ordinal))

def ActualCollapseFiniteTailMonotone : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ r s : Nat, r ≤ s →
    actualCollapse (a + (r : Ordinal)) ≤ actualCollapse (a + (s : Ordinal))

end LogicLineages.OrdinalComparison.Targets
