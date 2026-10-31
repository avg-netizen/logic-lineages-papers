module
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.OrdinalComparison.OrdinalRepresentationSound
@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets
/-- Actual natural arithmetic, not ordinary addition/multiplication. -/
def SourceNaturalSumPowerClosure : Prop :=
  ∀ (a b k : Ordinal.{0}), a < epsilonZero → b < epsilonZero →
    a < Ordinal.omega0 ^ k → b < Ordinal.omega0 ^ k →
      ordinalNaturalSum a b < Ordinal.omega0 ^ k

def SourceNaturalProductPolynomialClosure : Prop :=
  ∀ (a b : Ordinal.{0}), a < Ordinal.omega0 ^ Ordinal.omega0 →
    b < Ordinal.omega0 ^ Ordinal.omega0 →
      ordinalNaturalProduct a b < Ordinal.omega0 ^ Ordinal.omega0

def SourceBaseTwoLinearPolynomial : Prop :=
  ∀ a : Ordinal.{0}, a < Ordinal.omega0 ^ (2 : Ordinal.{0}) →
    (2 : Ordinal.{0}) ^ a < Ordinal.omega0 ^ Ordinal.omega0
end LogicLineages.OrdinalComparison.Targets
