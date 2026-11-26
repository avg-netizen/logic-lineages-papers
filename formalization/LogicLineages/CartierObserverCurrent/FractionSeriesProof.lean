module
public import LogicLineages.CartierObserverCurrent.FractionSeriesTargets
public import LogicLineages.CartierObserverCurrent.BasicRationalProof
public import LogicLineages.CartierObserverCurrent.SeriesProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FractionSeries

theorem rationalDigitFraction : Targets.RationalDigitFraction.{u} := by
  intro K _ _ _ P Q hQ b
  let E := algebraMap (Polynomial K) (RatFunc K)
  have hden : E Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  have hp := congrArg E (Basic.actualPolynomialSquareRootDecomposition K (P * Q))
  simp only [map_mul, map_add, map_pow] at hp
  have he : rationalFraction P Q =
      (rationalFraction (Basic.actualPolynomialSquareRootDigit false (P * Q)) Q) ^ 2 +
      Basic.rationalX *
        (rationalFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q) ^ 2 := by
    change E P / E Q = _
    calc
      E P / E Q = (E P * E Q) / (E Q) ^ 2 := by field_simp
      _ = _ := by rw [hp]; unfold rationalFraction; dsimp [E]; field_simp
  have hu := Basic.actualRationalSquareRootUniqueness K _ _ _ _
    ((Basic.actualRationalSquareRootDecomposition K (rationalFraction P Q)).symm.trans he)
  cases b
  · exact hu.1
  · exact hu.2

theorem representationIndependent : Targets.RepresentationIndependent.{u} := by
  intro K _ P Q P' Q' hQ hQ' h
  have qne : Q ≠ 0 := by intro h; subst Q; simpa using hQ
  have qne' : Q' ≠ 0 := by intro h; subst Q'; simpa using hQ'
  unfold rationalFraction at h
  rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero qne)
    (RatFunc.algebraMap_ne_zero qne')] at h
  have hp : P * Q' = P' * Q := RatFunc.algebraMap_injective K (by simpa only [map_mul] using h)
  have hs := congrArg (fun R : Polynomial K => (R : PowerSeries K)) hp
  simp only [Polynomial.coe_mul] at hs
  have hc : (Q : PowerSeries K) * (Q : PowerSeries K)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa only [Polynomial.constantCoeff_coe] using hQ)
  have hc' : (Q' : PowerSeries K) * (Q' : PowerSeries K)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa only [Polynomial.constantCoeff_coe] using hQ')
  unfold seriesFraction
  calc
    (P : PowerSeries K) * (Q : PowerSeries K)⁻¹ =
        ((P : PowerSeries K) * Q') * (Q : PowerSeries K)⁻¹ * (Q' : PowerSeries K)⁻¹ := by
      calc
        _ = ((P : PowerSeries K) * (Q : PowerSeries K)⁻¹) *
            ((Q' : PowerSeries K) * (Q' : PowerSeries K)⁻¹) := by rw [hc', mul_one]
        _ = _ := by ring
    _ = ((P' : PowerSeries K) * Q) * (Q : PowerSeries K)⁻¹ * (Q' : PowerSeries K)⁻¹ := by rw [hs]
    _ = (P' : PowerSeries K) * (Q' : PowerSeries K)⁻¹ := by
      calc
        _ = (P' : PowerSeries K) * ((Q : PowerSeries K) * (Q : PowerSeries K)⁻¹) *
            (Q' : PowerSeries K)⁻¹ := by ring
        _ = _ := by rw [hc, mul_one]

theorem seriesCartierFraction (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    (P Q : Polynomial K) (hQ : Q.coeff 0 ≠ 0) :
    Series.differentialCartier (seriesFraction P Q) =
      seriesFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q := by
  have hc : (Q : PowerSeries K) * (Q : PowerSeries K)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa only [Polynomial.constantCoeff_coe] using hQ)
  have hp := congrArg (fun R : Polynomial K => (R : PowerSeries K))
    (Basic.actualPolynomialSquareRootDecomposition K (P * Q))
  simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X] at hp
  have he : seriesFraction P Q =
      (seriesFraction (Basic.actualPolynomialSquareRootDigit false (P * Q)) Q) ^ 2 +
      PowerSeries.X *
        (seriesFraction (Basic.actualPolynomialSquareRootDigit true (P * Q)) Q) ^ 2 := by
    unfold seriesFraction
    calc
      (P : PowerSeries K) * (Q : PowerSeries K)⁻¹ =
          ((P : PowerSeries K) * Q) * ((Q : PowerSeries K)⁻¹) ^ 2 := by
        calc
          _ = (P : PowerSeries K) * ((Q : PowerSeries K) * (Q : PowerSeries K)⁻¹) *
              (Q : PowerSeries K)⁻¹ := by rw [hc, mul_one]
          _ = _ := by ring
      _ = _ := by rw [hp]; ring
  rw [he, Series.cartierCharacterization]

theorem cartierCompatibility : Targets.CartierCompatibility.{u} := by
  intro K _ _ _ P Q hQ
  have qne : Q ≠ 0 := by intro h; subst Q; simpa using hQ
  have hs := seriesCartierFraction K P Q hQ
  refine ⟨rationalDigitFraction K P Q qne true, hs, ?_⟩
  intro n
  rw [← hs]
  exact Series.cartierCoefficient K (seriesFraction P Q) n

#audit_namespace LogicLineages.CartierObserverCurrent.FractionSeries
end LogicLineages.CartierObserverCurrent.FractionSeries
