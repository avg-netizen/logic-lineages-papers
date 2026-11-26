module
public import LogicLineages.CartierObserverCurrent.PeriodLaurentBridgeTargets
public import LogicLineages.OrdinalComparison.TranslatedRationalProof
public import LogicLineages.OrdinalComparison.HahnSquareProof
public import LogicLineages.CartierObserverCurrent.BasicRationalProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodLaurentBridge
open LogicLineages.OrdinalComparison

theorem cartierIdentity : Targets.CartierIdentity.{u} := by
  intro K _ _ _ f
  rfl

theorem laurentCoefficient : Targets.LaurentCoefficient.{u} := by
  intro K _ _ _ z f n
  let H := actualTranslatedRationalEmbedding z
  let a := Basic.actualRationalSquareRootDigit false f
  let b := Basic.actualRationalSquareRootDigit true f
  have hx : H Basic.rationalX = HahnSeries.single (1 : Int) 1 + HahnSeries.single (0 : Int) z := by
    rw [Basic.rationalX, actualTranslatedRationalPolynomial, actualTranslatedPolynomialVariable]
  have hf := congrArg H (Basic.actualRationalSquareRootDecomposition K f)
  simp only [map_add, map_mul, map_pow] at hf
  change H f = (H a) ^ 2 + H Basic.rationalX * (H b) ^ 2 at hf
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

theorem iteratedResidue : Targets.IteratedResidue.{u} := by
  intro K _ _ _ z f j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', cartierIdentity, laurentCoefficient]
    norm_num only at *
    rw [ih]
    rw [show j + 1 = 1 + j by omega, iterateFrobeniusEquiv_symm_add_apply,
      iterateFrobeniusEquiv_one]

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodLaurentBridge
end LogicLineages.CartierObserverCurrent.PeriodLaurentBridge
