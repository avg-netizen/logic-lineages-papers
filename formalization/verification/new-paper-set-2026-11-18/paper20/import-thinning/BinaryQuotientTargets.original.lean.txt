module
public import LogicLineages.OrdinalComparison.PolynomialDigitDefinitions
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! External continuation, 30 October 2026. Exact F2 algebraic suppliers for
paper10, paper.tex399–417 (lem:matrix). The actual polynomial/series selectors
and formal quotient are unchanged. No finite-matrix or all-word observer
completion is claimed by these transport targets alone. -/

namespace LogicLineages.OrdinalComparison.Targets

/-- Squaring an F2 polynomial doubles exponents, without changing coefficients. -/
def ActualBinaryPolynomialSquareCoefficient : Prop :=
  ∀ A : Polynomial (ZMod 2), ∀ n : Nat,
    (A ^ 2).coeff n = if 2 ∣ n then A.coeff (n / 2) else 0

/-- Literal coefficient selection commutes with a polynomial factor in z². -/
def ActualBinarySeriesSquareFactor : Prop :=
  ∀ b : Bool, ∀ F : PowerSeries (ZMod 2), ∀ A : Polynomial (ZMod 2),
    actualBinarySeriesDigit b (F * ((A ^ 2 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2))) =
      actualBinarySeriesDigit b F * (A : PowerSeries (ZMod 2))

/-- The genuine source quotient update over F2, for every unit-at-zero
polynomial denominator and every polynomial numerator. -/
def ActualBinaryQuotientTransport : Prop :=
  ∀ A U : Polynomial (ZMod 2), A.coeff 0 = 1 → ∀ b : Bool,
    actualBinarySeriesDigit b (actualPolynomialSeriesQuotient A U) =
      actualPolynomialSeriesQuotient A (actualBinaryPolynomialDigit b (U * A))

end LogicLineages.OrdinalComparison.Targets
