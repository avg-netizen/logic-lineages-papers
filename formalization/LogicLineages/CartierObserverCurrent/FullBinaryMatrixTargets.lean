module
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullBinaryMatrix.Targets
open LogicLineages.OrdinalComparison

/-- Full current20 lem:matrix, retaining actual quotient selection, proper
numerator preservation and genuine matrix action with guarded negative indices. -/
def CompleteStateUpdate : Prop := ∀ d : Nat,
  let A := actualBinarySourceDenominator d
  let D := d * (d + 1) / 2
  A.degree = (D : WithBot Nat) ∧
  ∀ U : Polynomial (ZMod 2), U.degree < (D : WithBot Nat) → ∀ b : Bool,
    actualBinarySeriesDigit b (actualPolynomialSeriesQuotient A U) =
      actualPolynomialSeriesQuotient A (actualBinaryPolynomialDigit b (U * A)) ∧
    (actualBinaryPolynomialDigit b (U * A)).degree < (D : WithBot Nat) ∧
    actualBinaryCoefficientVector D (actualBinaryPolynomialDigit b (U * A)) =
      Matrix.mulVec (actualBinaryTransitionMatrix D A b) (actualBinaryCoefficientVector D U) ∧
    ∀ i j : Fin D, actualBinaryTransitionMatrix D A b i j =
      if j.val ≤ Nat.bit b i.val then A.coeff (Nat.bit b i.val - j.val) else 0
end LogicLineages.CartierObserverCurrent.FullBinaryMatrix.Targets
