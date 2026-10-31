module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-- Original Proposition 2.3's nonfinite collapse lower bound. A finite
predecessor at the actual Phi norm budget supplies the estimate; no global
monotonicity of collapse is asserted. -/
def ActualInfiniteCollapseControlLower : Prop :=
  ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero →
    Phi (actualOrdinalNorm a) + 1 ≤ actualCollapse a

end LogicLineages.OrdinalComparison.Source.Targets
