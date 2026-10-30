module
public import LogicLineages.OrdinalComparison.SeriesObservabilityTargets

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualSeriesQuotientIdentity : Targets.ActualSeriesQuotientIdentity.{u} := by
  intro K _ A U hA
  have hc : PowerSeries.constantCoeff (A : PowerSeries K) = 1 := by
    simpa only [Polynomial.constantCoeff_coe] using hA
  have hinv := PowerSeries.mul_inv_cancel (A : PowerSeries K) (by rw [hc]; exact one_ne_zero)
  change (A : PowerSeries K) * ((U : PowerSeries K) * (A : PowerSeries K)⁻¹) = (U : PowerSeries K)
  rw [mul_left_comm, hinv, mul_one]

theorem actualInitialSeriesCoefficientReconstruction :
    Targets.ActualInitialSeriesCoefficientReconstruction.{u} := by
  intro K _ A U V hA D hcoeff n hn
  have hU := actualSeriesQuotientIdentity K A U hA
  have hV := actualSeriesQuotientIdentity K A V hA
  have hsum : PowerSeries.coeff n ((A : PowerSeries K) * actualPolynomialSeriesQuotient A U) =
      PowerSeries.coeff n ((A : PowerSeries K) * actualPolynomialSeriesQuotient A V) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hindex : i + j = n := Finset.mem_antidiagonal.mp hij
    rw [hcoeff j (by omega)]
  rw [hU, hV, Polynomial.coeff_coe, Polynomial.coeff_coe] at hsum
  exact hsum

theorem actualPolynomialNumeratorObservability : Targets.ActualPolynomialNumeratorObservability.{u} := by
  intro K _ A U V hA D hU hV hcoeff
  have hlow := actualInitialSeriesCoefficientReconstruction K A U V hA D hcoeff
  apply Polynomial.ext
  intro n
  by_cases hn : n < D
  · exact hlow n hn
  · have hDn : (D : WithBot Nat) ≤ (n : WithBot Nat) := WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hn)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (hU.trans_le hDn),
      Polynomial.coeff_eq_zero_of_degree_lt (hV.trans_le hDn)]

end LogicLineages.OrdinalComparison
