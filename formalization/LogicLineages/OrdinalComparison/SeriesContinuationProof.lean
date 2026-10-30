module
public import LogicLineages.OrdinalComparison.SeriesContinuationTargets
public import LogicLineages.OrdinalComparison.SeriesObservabilityProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualBinarySeriesWordSelection : Targets.ActualBinarySeriesWordSelection.{u} := by
  intro K _ w
  induction w with
  | nil => intro F; rfl
  | cons b w ih =>
    intro F
    change PowerSeries.coeff 0 (actualBinarySeriesWord w (actualBinarySeriesDigit b F)) = _
    rw [ih]
    simp only [actualBinarySeriesDigit, PowerSeries.coeff_mk, actualBinaryWordValue]

private theorem binary_word_value_bits (k : Nat) : actualBinaryWordValue (Nat.bits k) = k := by
  induction k using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    change Nat.bit b (actualBinaryWordValue (Nat.bits n)) = Nat.bit b n
    rw [ih]

theorem actualBinaryDigitsValueAndBound : Targets.ActualBinaryDigitsValueAndBound := by
  intro D k hk
  refine ⟨?_, binary_word_value_bits k⟩
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (hk.trans_le (Nat.le_pow_clog (by decide) D))

theorem actualSeriesBoundedContinuation : Targets.ActualSeriesBoundedContinuation.{u} := by
  classical
  intro K _ A U V hA D hU hV hne
  have hdiff : ∃ k : Nat, k < D ∧
      PowerSeries.coeff k (actualPolynomialSeriesQuotient A U) ≠
        PowerSeries.coeff k (actualPolynomialSeriesQuotient A V) := by
    by_contra hnone
    apply hne
    apply actualPolynomialNumeratorObservability K A U V hA D hU hV
    intro k hk
    by_contra hneq
    exact hnone ⟨k, hk, hneq⟩
  obtain ⟨k, hk, hcoeff⟩ := hdiff
  have hbits := actualBinaryDigitsValueAndBound D k hk
  refine ⟨Nat.bits k, hbits.1, ?_⟩
  rw [actualBinarySeriesWordSelection, actualBinarySeriesWordSelection, hbits.2]
  exact hcoeff

end LogicLineages.OrdinalComparison
