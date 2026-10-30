module
public import LogicLineages.OrdinalComparison.BinaryCartierExtensionTargets
public import LogicLineages.OrdinalComparison.CartierRationalProof

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualBinaryRationalExtensionInjective : Targets.ActualBinaryRationalExtensionInjective.{u} := by
  intro K _ _
  exact (actualBinaryRationalExtension K).injective

theorem actualBinaryRationalExtensionPolynomial : Targets.ActualBinaryRationalExtensionPolynomial.{u} := by
  intro K _ _ U
  unfold actualBinaryRationalExtension
  exact IsFractionRing.lift_algebraMap _ U

theorem actualBinaryRationalExtensionCartier : Targets.ActualBinaryRationalExtensionCartier.{u} := by
  intro K _ _ _ _ f
  let E := actualBinaryRationalExtension K
  have hX : E RatFunc.X = RatFunc.X := by
    have h := actualBinaryRationalExtensionPolynomial K Polynomial.X
    simpa only [RatFunc.algebraMap_X, Polynomial.map_X] using h
  have hf := actualRationalSquareRootDecomposition (ZMod 2) f
  have he : E f = (E (actualRationalSquareRootDigit false f)) ^ 2 +
      RatFunc.X * (E (actualRationalSquareRootDigit true f)) ^ 2 := by
    calc
      E f = E ((actualRationalSquareRootDigit false f) ^ 2 +
          RatFunc.X * (actualRationalSquareRootDigit true f) ^ 2) := congrArg E hf
      _ = _ := by simp only [map_add, map_mul, map_pow, hX]
  change E (actualRationalSquareRootDigit true f) = actualDifferentialCartier (E f)
  rw [he, actualDifferentialCartierCharacterization]

theorem actualBinaryRationalExtensionLinked : Targets.ActualBinaryRationalExtensionLinked := by
  intro u
  unfold actualBinaryRationalDifferential actualLinkedDifferential
  rw [map_div₀, actualBinaryRationalExtensionPolynomial, actualBinaryRationalExtensionPolynomial]
  simp only [Polynomial.map_pow, Polynomial.map_X, Algebra.algebraMap_self, Polynomial.map_id]

end LogicLineages.OrdinalComparison
