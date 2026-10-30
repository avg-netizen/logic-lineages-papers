module
public import LogicLineages.OrdinalComparison.BinaryDenominatorTargets
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualBinarySourceDenominatorConstant : Targets.ActualBinarySourceDenominatorConstant := by
  intro d
  simp [actualBinarySourceDenominator, Polynomial.coeff_zero_prod]

private theorem triangular_sum (d : Nat) :
    (∑ i : Fin d, (i.val + 1)) = actualBinarySourceDimension d := by
  rw [← Finset.sum_range (fun n : Nat => n + 1)]
  change (∑ i ∈ Finset.range d, (i + 1)) = d * (d + 1) / 2
  calc
    (∑ i ∈ Finset.range d, (i + 1)) = ∑ i ∈ Finset.range (d + 1), i := by
      rw [Finset.sum_range_succ']
      simp
    _ = d * (d + 1) / 2 := by
      rw [Finset.sum_range_id]
      simp [Nat.mul_comm]

theorem actualBinarySourceDenominatorDegree : Targets.ActualBinarySourceDenominatorDegree := by
  intro d
  unfold actualBinarySourceDenominator
  rw [Polynomial.degree_prod]
  have hf : ∀ i : Fin d, (1 + Polynomial.X ^ (i.val + 1) : Polynomial (ZMod 2)).degree =
      ((i.val + 1 : Nat) : WithBot Nat) := by
    intro i
    rw [add_comm, ← Polynomial.C_1]
    exact Polynomial.degree_X_pow_add_C (Nat.succ_pos _) 1
  simp_rw [hf]
  rw [← Nat.cast_sum, triangular_sum]

theorem actualBinarySourceDimensionPositive : Targets.ActualBinarySourceDimensionPositive := by
  intro d hd
  unfold actualBinarySourceDimension
  apply Nat.div_pos
  · nlinarith
  · decide

end LogicLineages.OrdinalComparison
