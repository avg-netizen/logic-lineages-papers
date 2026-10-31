module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-- The actual natural product used as a collapse head is nonfinite for every
positive original ordinal operand. This supplies the nonfinite hypothesis
for the genuine Phi lower bound; it is not inferred from norm positivity. -/
def ActualOmegaNaturalProductInfinite : Prop :=
  ∀ a : Ordinal.{0}, 0 < a → a < epsilonZero →
    Ordinal.omega0 ≤ ordinalNaturalProduct Ordinal.omega0 a

end LogicLineages.OrdinalComparison.Source.Targets
