module
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public import LogicLineages.OrdinalComparison.SeriesObservabilityTargets

@[expose] public section

/-! Full source comparators for paper10 lem:matrix (paper.tex399–417) and
lem:observable (437–451). A_d retains all source factors, D_d is its proved
triangular degree, and transition matrices use the guarded source coefficients.
The arbitrary-field uniqueness clause is stronger than the source cutoff
assumption deg(A)=D. The source matrix clause uses d>0 (source195–204); the
separate zero-dimension gate certifies that the excluded case has no pair of
distinct proper numerators. No partition-generating-function claim is made. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualSourceZeroProperNumerator : Prop :=
  ∀ U : Polynomial (ZMod 2),
    U.degree < (actualBinarySourceDimension 0 : WithBot Nat) → U = 0

def ActualSourceBinaryMatrix : Prop :=
  ∀ d : Nat, ∀ U : Polynomial (ZMod 2),
    U.degree < (actualBinarySourceDimension d : WithBot Nat) → ∀ b : Bool,
      actualBinarySeriesDigit b (actualPolynomialSeriesQuotient (actualBinarySourceDenominator d) U) =
        actualPolynomialSeriesQuotient (actualBinarySourceDenominator d)
          (actualBinaryPolynomialDigit b (U * actualBinarySourceDenominator d)) ∧
      (actualBinaryPolynomialDigit b (U * actualBinarySourceDenominator d)).degree <
        (actualBinarySourceDimension d : WithBot Nat) ∧
      actualBinaryCoefficientVector (actualBinarySourceDimension d)
          (actualBinaryPolynomialDigit b (U * actualBinarySourceDenominator d)) =
        Matrix.mulVec (actualBinaryTransitionMatrix (actualBinarySourceDimension d)
          (actualBinarySourceDenominator d) b)
          (actualBinaryCoefficientVector (actualBinarySourceDimension d) U)

def ActualSourceBinaryObservability : Prop :=
  ActualPolynomialNumeratorObservability.{u} ∧
  ∀ d : Nat, ∀ hd : 0 < d, ∀ U V : Polynomial (ZMod 2),
    U.degree < (actualBinarySourceDimension d : WithBot Nat) →
    V.degree < (actualBinarySourceDimension d : WithBot Nat) → U ≠ V →
      ∃ w : List Bool, w.length ≤ Nat.clog 2 (actualBinarySourceDimension d) ∧
        actualBinaryMatrixWord (actualBinarySourceDimension d) (actualBinarySourceDenominator d) w
          (actualBinaryCoefficientVector (actualBinarySourceDimension d) U)
          ⟨0, actualBinarySourceDimensionPositive d hd⟩ ≠
        actualBinaryMatrixWord (actualBinarySourceDimension d) (actualBinarySourceDenominator d) w
          (actualBinaryCoefficientVector (actualBinarySourceDimension d) V)
          ⟨0, actualBinarySourceDimensionPositive d hd⟩

end LogicLineages.OrdinalComparison.Targets
