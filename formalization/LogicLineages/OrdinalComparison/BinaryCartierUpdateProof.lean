module
public import LogicLineages.OrdinalComparison.BinaryCartierUpdateTargets
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public import LogicLineages.OrdinalComparison.CartierRationalProof
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualBinaryRationalCartierUpdate : Targets.ActualBinaryRationalCartierUpdate := by
  intro d U
  have hf : frobeniusEquiv (ZMod 2) 2 = RingEquiv.refl (ZMod 2) := by
    ext x
    change x ^ 2 = x
    fin_cases x <;> decide
  have hdigit (b : Bool) (P : Polynomial (ZMod 2)) :
      actualPolynomialSquareRootDigit b P = actualBinaryPolynomialDigit b P := by
    simp [actualPolynomialSquareRootDigit, hf]
  let A := actualBinarySourceDenominator d
  let E := algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2))
  have ha : A ≠ 0 := by
    intro h
    have hc := actualBinarySourceDenominatorConstant d
    change A.coeff 0 = 1 at hc
    simpa [h] using hc
  have hden : E A ≠ 0 := RatFunc.algebraMap_ne_zero ha
  have h := congrArg E (actualPolynomialSquareRootDecomposition (ZMod 2) (U * A))
  simp only [map_mul, map_add, map_pow] at h
  have he : E U / E A =
      (E (actualPolynomialSquareRootDigit false (U * A)) / E A) ^ 2 +
      RatFunc.X * (E (actualPolynomialSquareRootDigit true (U * A)) / E A) ^ 2 := by
    calc
      E U / E A = (E U * E A) / (E A) ^ 2 := by field_simp
      _ = _ := by rw [h]; dsimp [E]; field_simp
  simp only [actualBinaryRationalDifferential, Algebra.algebraMap_self, Polynomial.map_id]
  change actualDifferentialCartier (E U / E A) = E (actualBinaryPolynomialDigit true (U * A)) / E A
  rw [he, actualDifferentialCartierCharacterization, hdigit]

end LogicLineages.OrdinalComparison
