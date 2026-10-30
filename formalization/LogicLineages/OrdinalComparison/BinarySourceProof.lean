module
public import LogicLineages.OrdinalComparison.BinarySourceTargets
public import LogicLineages.OrdinalComparison.BinaryMatrixProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualSourceZeroProperNumerator : Targets.ActualSourceZeroProperNumerator := by
  intro U hU
  apply Polynomial.ext
  intro n
  have hn : U.degree < (n : WithBot Nat) := hU.trans_le
    (WithBot.coe_le_coe.mpr (Nat.zero_le n))
  rw [Polynomial.coeff_eq_zero_of_degree_lt hn, Polynomial.coeff_zero]

theorem actualSourceBinaryMatrix : Targets.ActualSourceBinaryMatrix := by
  intro d U hU b
  refine ⟨actualBinaryQuotientTransport _ U (actualBinarySourceDenominatorConstant d) b, ?_, ?_⟩
  · exact actualBinaryPolynomialStepDegree (ZMod 2) _ U _
      (le_of_eq (actualBinarySourceDenominatorDegree d)) hU b
  · exact actualBinaryMatrixStep (ZMod 2) _ _ U hU b

theorem actualSourceBinaryObservability : Targets.ActualSourceBinaryObservability.{u} := by
  refine ⟨actualPolynomialNumeratorObservability, ?_⟩
  intro d hd U V hU hV hne
  exact actualBinaryMatrixBoundedContinuation _ (actualBinarySourceDimensionPositive d hd)
    _ U V (actualBinarySourceDenominatorConstant d)
    (le_of_eq (actualBinarySourceDenominatorDegree d)) hU hV hne

end LogicLineages.OrdinalComparison
