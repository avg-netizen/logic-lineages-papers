module
public import LogicLineages.CartierObserverCurrent.RegularSelectorsTargets
public import LogicLineages.CartierObserverCurrent.FractionSeriesProof
public import LogicLineages.CartierObserverCurrent.MixedProperProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RegularSelectors

theorem regularPreservation : Targets.RegularPreservation := by
  intro f hf i
  obtain ⟨Q, hQ⟩ := MixedProper.stepDenominatorDivides (ZMod 2) i f
  intro h
  apply hf
  rw [hQ, Polynomial.eval_mul, h, zero_mul]

private theorem series_digit (P Q : Polynomial (ZMod 2)) (hQ : Q.coeff 0 ≠ 0) (i : Bool) :
    Series.squareRootDigit i (FractionSeries.seriesFraction P Q) =
      FractionSeries.seriesFraction (Basic.actualPolynomialSquareRootDigit i (P * Q)) Q := by
  have hc : (Q : PowerSeries (ZMod 2)) * (Q : PowerSeries (ZMod 2))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa only [Polynomial.constantCoeff_coe] using hQ)
  have hp := congrArg (fun R : Polynomial (ZMod 2) => (R : PowerSeries (ZMod 2)))
    (Basic.actualPolynomialSquareRootDecomposition (ZMod 2) (P * Q))
  simp only [Polynomial.coe_mul, Polynomial.coe_add,
    Polynomial.coe_pow, Polynomial.coe_X] at hp
  have he : FractionSeries.seriesFraction P Q =
      (FractionSeries.seriesFraction (Basic.actualPolynomialSquareRootDigit false (P * Q)) Q) ^ 2 +
      PowerSeries.X *
        (FractionSeries.seriesFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q) ^ 2 := by
    unfold FractionSeries.seriesFraction
    calc
      (P : PowerSeries (ZMod 2)) * (Q : PowerSeries (ZMod 2))⁻¹ =
          ((P : PowerSeries (ZMod 2)) * Q) * ((Q : PowerSeries (ZMod 2))⁻¹) ^ 2 := by
        calc
          _ = (P : PowerSeries (ZMod 2)) * ((Q : PowerSeries (ZMod 2)) * (Q : PowerSeries (ZMod 2))⁻¹) *
              (Q : PowerSeries (ZMod 2))⁻¹ := by rw [hc, mul_one]
          _ = _ := by ring
      _ = _ := by rw [hp]; ring
  have hu := Series.squareUniqueness (ZMod 2) _ _ _ _
    ((Series.squareDecomposition (ZMod 2) (FractionSeries.seriesFraction P Q)).symm.trans he)
  cases i
  · exact hu.1
  · exact hu.2

private theorem sqrt_f2 (x : ZMod 2) : (frobeniusEquiv (ZMod 2) 2).symm x = x := by
  apply (frobeniusEquiv (ZMod 2) 2).injective
  rw [(frobeniusEquiv (ZMod 2) 2).apply_symm_apply]
  change x = x ^ 2
  fin_cases x <;> decide

theorem actualCoefficientSelector : Targets.ActualCoefficientSelector := by
  intro f hf i n
  have hf0 : f.denom.coeff 0 ≠ 0 := by simpa only [regular, Polynomial.coeff_zero_eq_eval_zero] using hf
  have hs0 : (MixedProper.step i f).denom.coeff 0 ≠ 0 := by
    simpa only [regular, Polynomial.coeff_zero_eq_eval_zero] using regularPreservation f hf i
  have hr : MixedProper.step i f = FractionSeries.rationalFraction
      (Basic.actualPolynomialSquareRootDigit i (f.num * f.denom)) f.denom := by
    rw [MixedProper.stepDigitIdentity]
    have h := FractionSeries.rationalDigitFraction (ZMod 2) f.num f.denom f.denom_ne_zero i
    simpa only [FractionSeries.rationalFraction, RatFunc.num_div_denom] using h
  have he : expansion (MixedProper.step i f) = FractionSeries.seriesFraction
      (Basic.actualPolynomialSquareRootDigit i (f.num * f.denom)) f.denom := by
    apply FractionSeries.representationIndependent (ZMod 2) _ _ _ _ hs0 hf0
    simpa only [FractionSeries.rationalFraction, RatFunc.num_div_denom] using hr
  rw [he, ← series_digit f.num f.denom hf0 i]
  simp only [Series.squareRootDigit, PowerSeries.coeff_mk, sqrt_f2]
  rfl

#audit_namespace LogicLineages.CartierObserverCurrent.RegularSelectors
end LogicLineages.CartierObserverCurrent.RegularSelectors
