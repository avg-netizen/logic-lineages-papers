module
public import LogicLineages.OrdinalComparison.CartierLaurentTargets
public import LogicLineages.OrdinalComparison.TranslatedRationalProof
public import LogicLineages.OrdinalComparison.CartierRationalProof
public import LogicLineages.OrdinalComparison.HahnSquareProof

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualDifferentialCartierLaurentCoefficient :
    Targets.ActualDifferentialCartierLaurentCoefficient.{u} := by
  intro K _ _ _ z f n
  let H := actualTranslatedRationalEmbedding z
  let a := actualRationalSquareRootDigit false f
  let b := actualRationalSquareRootDigit true f
  have hx : H RatFunc.X = HahnSeries.single (1 : Int) 1 + HahnSeries.single (0 : Int) z := by
    rw [← RatFunc.algebraMap_X, actualTranslatedRationalPolynomial,
      actualTranslatedPolynomialVariable]
  have hf := congrArg H (actualRationalSquareRootDecomposition K f)
  simp only [map_add, map_mul, map_pow] at hf
  change H f = (H a) ^ 2 + H RatFunc.X * (H b) ^ 2 at hf
  rw [hx, add_mul] at hf
  have hc := congrArg (fun F : HahnSeries Int K => F.coeff (2 * n + 1)) hf
  simp only [HahnSeries.coeff_add] at hc
  rw [actualHahnSquareOddCoefficient K (H a) n, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_single_zero_mul] at hc
  have hi : 2 * n + 1 - 1 = 2 * n := by omega
  rw [hi, actualHahnSquareEvenCoefficient K (H b) n,
    actualHahnSquareOddCoefficient K (H b) n] at hc
  simp only [one_mul, mul_zero, add_zero, zero_add] at hc
  change (H b).coeff n = (frobeniusEquiv K 2).symm ((H f).coeff (2 * n + 1))
  rw [hc]
  exact ((frobeniusEquiv K 2).symm_apply_apply ((H b).coeff n)).symm

theorem actualDifferentialCartierResidue : Targets.ActualDifferentialCartierResidue.{u} := by
  intro K _ _ _ z f
  simpa using actualDifferentialCartierLaurentCoefficient K z f (-1)

theorem actualDifferentialCartierSimpleSupport : Targets.ActualDifferentialCartierSimpleSupport.{u} := by
  intro K _ _ _ z f hf n hn
  rw [actualDifferentialCartierLaurentCoefficient, hf (2 * n + 1) (by omega), map_zero]

end LogicLineages.OrdinalComparison
