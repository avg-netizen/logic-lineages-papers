module
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailTargets
public import LogicLineages.OrdinalComparison.WWFiniteTailMonotonicityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem finite_coeff (k : Nat) :
    Ordinal.CNF.coeff Ordinal.omega0 (k : Ordinal.{0}) = Finsupp.single 0 (k : Ordinal) := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, Ordinal.CNF.coeff_zero_right, Finsupp.single_zero]
  · have hne : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast hk
    simpa only [Ordinal.opow_zero, one_mul, add_zero, Ordinal.CNF.coeff_zero_right] using
      Ordinal.CNF.coeff_opow_mul_add (e := 0) (y := 0) Ordinal.one_lt_omega0 hne
        (Ordinal.natCast_lt_omega0 k) (by simp)

theorem actualNaturalSumFiniteRight : Targets.ActualNaturalSumFiniteRight := by
  intro a k
  unfold ordinalNaturalSum
  rw [finite_coeff, Ordinal.CNF.eval_add]
  · rw [Ordinal.CNF.eval_coeff, Ordinal.CNF.eval_single]
    simp only [Ordinal.opow_zero, one_mul]
  · intro e he d hd
    have hd0 : d = 0 := by
      by_contra h
      simpa [Finsupp.mem_support_iff, Finsupp.single_apply, h] using hd
    subst d
    exact zero_le

theorem actualCollapseNaturalFiniteTailMonotone :
    Targets.ActualCollapseNaturalFiniteTailMonotone := by
  intro a ha r s hrs
  rw [actualNaturalSumFiniteRight, actualNaturalSumFiniteRight]
  exact actualCollapseFiniteTailMonotone a ha r s hrs

end LogicLineages.OrdinalComparison
