module
public import LogicLineages.OrdinalComparison.BinaryPolynomialWordTargets
public import LogicLineages.OrdinalComparison.BinaryQuotientProof
public import LogicLineages.OrdinalComparison.SeriesContinuationProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualBinaryPolynomialWordQuotient : Targets.ActualBinaryPolynomialWordQuotient := by
  intro A U hA w
  induction w generalizing U with
  | nil => rfl
  | cons b w ih =>
    simp only [actualBinarySeriesWord, actualBinaryPolynomialWord]
    rw [actualBinaryQuotientTransport A U hA b]
    exact ih _

theorem actualBinaryPolynomialWordDegree : Targets.ActualBinaryPolynomialWordDegree.{u} := by
  intro K _ A U D hA hU w
  induction w generalizing U with
  | nil => exact hU
  | cons b w ih =>
    exact ih _ (actualBinaryPolynomialStepDegree K A U D hA hU b)

private theorem quotient_constant {K : Type*} [Field K] (A U : Polynomial K)
    (hA : A.coeff 0 = 1) :
    PowerSeries.coeff 0 (actualPolynomialSeriesQuotient A U) = U.coeff 0 := by
  have h := congrArg (PowerSeries.coeff 0) (actualSeriesQuotientIdentity K A U hA)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    Polynomial.constantCoeff_coe, hA, one_mul] using h

theorem actualBinaryPolynomialWordObservation : Targets.ActualBinaryPolynomialWordObservation := by
  intro A U hA w
  rw [← actualBinarySeriesWordSelection (ZMod 2) w (actualPolynomialSeriesQuotient A U),
    actualBinaryPolynomialWordQuotient A U hA w, quotient_constant A _ hA]

theorem actualBinaryPolynomialBoundedContinuation :
    Targets.ActualBinaryPolynomialBoundedContinuation := by
  intro A U V hA D _hdegree hU hV hne
  obtain ⟨w, hlen, hdiff⟩ := actualSeriesBoundedContinuation (ZMod 2) A U V hA D hU hV hne
  refine ⟨w, hlen, ?_⟩
  rw [actualBinaryPolynomialWordQuotient A U hA w,
    actualBinaryPolynomialWordQuotient A V hA w,
    quotient_constant A _ hA, quotient_constant A _ hA] at hdiff
  exact hdiff

end LogicLineages.OrdinalComparison
