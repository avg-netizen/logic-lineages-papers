module
public import LogicLineages.CartierObserverCurrent.FractionSeriesDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FractionSeries.Targets

/-- Both actual rational digits use the genuine same-denominator formula. -/
def RationalDigitFraction : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ P Q : Polynomial K, Q ≠ 0 → ∀ b : Bool,
      Basic.actualRationalSquareRootDigit b (rationalFraction P Q) =
        rationalFraction (Basic.actualPolynomialSquareRootDigit b (P * Q)) Q

/-- Genuine regular-at-origin fraction expansion does not depend on its presentation. -/
def RepresentationIndependent : Prop :=
  ∀ (K : Type u) [Field K], ∀ P Q P' Q' : Polynomial K,
    Q.coeff 0 ≠ 0 → Q'.coeff 0 ≠ 0 →
    rationalFraction P Q = rationalFraction P' Q' →
      seriesFraction P Q = seriesFraction P' Q'

/-- Actual rational C and actual series C act on the same represented fraction.
Includes every coefficient of the resulting genuine series expansion. -/
def CartierCompatibility : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ P Q : Polynomial K, Q.coeff 0 ≠ 0 →
      Basic.actualDifferentialCartier (rationalFraction P Q) =
        rationalFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q ∧
      Series.differentialCartier (seriesFraction P Q) =
        seriesFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q ∧
      ∀ n : Nat,
        PowerSeries.coeff n
          (seriesFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q) =
          (frobeniusEquiv K 2).symm
            (PowerSeries.coeff (2 * n + 1) (seriesFraction P Q))
end LogicLineages.CartierObserverCurrent.FractionSeries.Targets
