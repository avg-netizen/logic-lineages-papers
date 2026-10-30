module
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof
public import LogicLineages.OrdinalComparison.ConstantBudgetCountProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem actual_limit_part_limit_add_nat (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualNumericalFixedBudgetPartitionCount : Targets.ActualNumericalFixedBudgetPartitionCount := by
  intro d c S n hd _ _
  let lam := Ordinal.omega0 ^ (d : Ordinal)
  have hdpos : (d : Ordinal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < d)
  have hlam : Order.IsSuccLimit lam :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hdpos
  have heps := (actualFiniteTailClosureNorm lam (finiteOmegaPowerBelowEpsilonZero d) n).1
  have hinfinite : Ordinal.omega0 ≤ lam + (n : Ordinal) :=
    (Ordinal.omega0_le_of_isSuccLimit hlam).trans le_self_add
  change actualControlledCount (fun _ => S - c) (lam + (n : Ordinal)) = _
  rw [actualConstantBudgetCountCardinality (S - c) (lam + (n : Ordinal)) heps hinfinite,
    actual_limit_part_limit_add_nat lam hlam n]
  exact actualPolynomialNormPartitionCardinality d (S - c) hd

end LogicLineages.OrdinalComparison
