module
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof
public import LogicLineages.OrdinalComparison.NumericalFixedBudgetProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualConstantBudgetMonomialCount : Targets.ActualConstantBudgetMonomialCount := by
  intro d k
  induction k with
  | zero =>
    intro b hd _
    simp only [Nat.cast_zero, mul_zero, Finset.range_zero, Finset.sum_empty]
    have hz := (actualFiniteMonomialFacts d 0).1
    simp only [Nat.cast_zero, mul_zero] at hz
    exact (actualControlledCountRecursion (fun _ => b) 0 hz).1 Ordinal.omega0_pos
  | succ k ih =>
    intro b hd hb
    have hb' : (d + 1) * k + (d + 1) ≤ b := by simpa only [Nat.mul_succ] using hb
    have hpow := finiteOmegaPowerBelowEpsilonZero d
    have hdpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
    have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ (d : Ordinal)) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hdpos)
    have hblock := actualNumericalFixedBudgetPartitionCount d ((d + 1) * k) b 0 hd (by omega) (by
      have hn := (actualFiniteMonomialFacts d 1).2.1
      simp only [Nat.cast_one, mul_one, Nat.mul_one] at hn
      simpa only [Nat.cast_zero, add_zero, hn] using hb')
    simp only [Nat.cast_zero, add_zero] at hblock
    by_cases hk : k = 0
    · subst k
      simpa only [Nat.zero_add, Nat.cast_one, mul_one, Nat.mul_zero, Nat.sub_zero,
        Finset.sum_range_one] using hblock
    · let p := Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal)
      have hp := actualFiniteMonomialFacts d k
      have hplim : Order.IsSuccLimit p :=
        Ordinal.isSuccLimit_mul_left hlim (by exact_mod_cast Nat.pos_of_ne_zero hk)
      have hbound : Ordinal.omega0 ^ (d : Ordinal) < Ordinal.omega0 ^ ((d : Ordinal) + 1) :=
        (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (Order.lt_add_one_iff.mpr le_rfl)
      have hsplit := actualConstantBudgetPrefixCountDecomposition b p (Ordinal.omega0 ^ (d : Ordinal))
        hp.1 hpow hplim (d : Ordinal) hdpos hp.2.2 hbound (by rw [hp.2.1]; omega)
      rw [hp.2.1, hblock, ih b hd (by omega)] at hsplit
      rw [Finset.sum_range_succ]
      have heq : Ordinal.omega0 ^ (d : Ordinal) * ((k + 1 : Nat) : Ordinal) =
          p + Ordinal.omega0 ^ (d : Ordinal) := by
        simp only [p, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [heq, hsplit, Nat.add_comm]

end LogicLineages.OrdinalComparison
