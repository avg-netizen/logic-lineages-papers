module
public import LogicLineages.OrdinalComparison.WWSourcePolynomialArithmeticTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets
/-- Multiplication here is the original natural product; the output is a
positive limit, not merely an ordinal above omega. -/
def SourcePolynomialIndexLimit : Prop :=
  ∀ a : Ordinal.{0}, 0 < a → a < Ordinal.omega0 ^ Ordinal.omega0 →
    Order.IsSuccLimit (ordinalNaturalProduct Ordinal.omega0 a) ∧
      ordinalNaturalProduct Ordinal.omega0 a < Ordinal.omega0 ^ Ordinal.omega0
end LogicLineages.OrdinalComparison.Targets
