module
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalDefinitions
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesDefinitions
public import LogicLineages.OrdinalComparison.SeriesObservabilityDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine differential selected-coefficient identity, source eq:selection.
The numerator exponent and selected count index are nonnegative by explicit
source hypotheses; no truncated negative index stands for a source exponent. -/
def ActualBinaryRationalOriginSeries : Prop :=
  ∀ d : Nat, ∀ U : Polynomial (ZMod 2),
    actualTranslatedRationalEmbedding (0 : ZMod 2) (actualBinaryRationalDifferential d U) =
      HahnSeries.ofPowerSeries Int (ZMod 2)
        (actualPolynomialSeriesQuotient (actualBinarySourceDenominator d) U)

def ActualDifferentialSelectedCoefficient : Prop :=
  ∀ d e ℓ : Nat, 1 ≤ e → e ≤ 2 ^ ℓ →
    (actualTranslatedRationalEmbedding (0 : ZMod 2)
      ((actualDifferentialCartier (K := ZMod 2))^[ℓ]
        (actualBinaryRationalDifferential d (Polynomial.X ^ (e - 1))))).coeff 0 =
      (restrictedPartitionCount d (2 ^ ℓ - e) : ZMod 2)

def ActualDifferentialSelectedParity : Prop :=
  ∀ d e ℓ : Nat, 1 ≤ e → e ≤ 2 ^ ℓ →
    ((actualTranslatedRationalEmbedding (0 : ZMod 2)
      ((actualDifferentialCartier (K := ZMod 2))^[ℓ]
        (actualBinaryRationalDifferential d (Polynomial.X ^ (e - 1))))).coeff 0).val =
      restrictedPartitionCount d (2 ^ ℓ - e) % 2

end LogicLineages.OrdinalComparison.Targets
