module
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses ForwardTranslation

def PositiveHeightZeroLinearBound : Prop :=
  ∀ c : ClosedPositive, positiveHeadHeight c = 0 →
    c.evaluate.1.repr < Ordinal.omega0 ^ (2 : Ordinal)

def PositiveHeightOnePolynomialBound : Prop :=
  ∀ c : ClosedPositive, positiveHeadHeight c ≤ 1 →
    c.evaluate.1.repr < Ordinal.omega0 ^ Ordinal.omega0
end LogicLineages.OrdinalComparison.Source.Targets
