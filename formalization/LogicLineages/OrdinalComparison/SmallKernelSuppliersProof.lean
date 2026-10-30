module
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersTargets
public import LogicLineages.OrdinalComparison.ActualLimitPredecessor
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof
public import LogicLineages.OrdinalComparison.ControlledCountProof
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem small_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero, Nat.zero_add] using
    actualFiniteHeadNorm 0 n

private theorem small_nat_below (n : Nat) : (n : Ordinal) < epsilonZero := by
  simpa only [Nat.cast_zero, Ordinal.opow_zero, one_mul] using (actualFiniteMonomialFacts 0 n).1

private theorem small_omega_below : Ordinal.omega0 < epsilonZero := by
  simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1

theorem actualOmegaMaximum : Targets.ActualOmegaMaximum := by
  intro b
  have hm := actualMaximumPredecessor_correct Ordinal.omega0 Ordinal.omega0_pos small_omega_below b
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hm.1.1
  have hs := actualLimitMaximumPredecessorSaturation Ordinal.omega0 small_omega_below
    Ordinal.isSuccLimit_omega0 b
  rw [hn, small_nat_norm] at hs
  simpa only [hs] using hn

theorem actualOmegaSquaredMaximum : Targets.ActualOmegaSquaredMaximum := by
  intro b hb
  have hmax : actualMaximumPredecessor (2 : Ordinal) (b - 1) = 1 := by
    symm
    apply actualMaximumPredecessor_unique (2 : Ordinal) (by norm_num) (small_nat_below 2) (b - 1)
    constructor
    · constructor
      · norm_num
      · have hn := small_nat_norm 1
        simp only [Nat.cast_one] at hn
        rw [hn]
        omega
    · intro x hx
      exact Order.lt_add_one_iff.mp (show x < (1 : Ordinal) + 1 by simpa using hx.1)
  have hr := actualLowerPowerGreedyRecurrence (2 : Ordinal) (by norm_num) (small_nat_below 2) b (by omega)
  dsimp only at hr
  rw [hmax] at hr
  have hn := small_nat_norm 1
  simp only [Nat.cast_one] at hn
  rw [hn] at hr
  norm_num only at hr
  have hx := actualOmegaMaximum (b % 2)
  simpa only [actualLowerPowerMaximum, Ordinal.opow_one, hx] using hr

private theorem small_limitPart_tail (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualExpansiveControlLinearCount : Targets.ActualExpansiveControlLinearCount := by
  intro g hg k
  induction k with
  | zero =>
    intro n
    simp only [Nat.cast_zero, mul_zero, zero_add]
    exact (actualControlledCountRecursion g (n : Ordinal) (small_nat_below n)).1
      (Ordinal.natCast_lt_omega0 n)
  | succ k ih =>
    intro n
    have hbase : Ordinal.omega0 * ((k + 1 : Nat) : Ordinal) < epsilonZero := by
      simpa only [Nat.cast_one, Ordinal.opow_one] using (actualFiniteMonomialFacts 1 (k + 1)).1
    have heps := (actualFiniteTailClosureNorm _ hbase n).1
    have hlim : Order.IsSuccLimit (Ordinal.omega0 * ((k + 1 : Nat) : Ordinal)) :=
      Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast Nat.succ_pos k)
    have hn : Ordinal.omega0 ≤ Ordinal.omega0 * ((k + 1 : Nat) : Ordinal) + (n : Ordinal) :=
      (Ordinal.omega0_le_of_isSuccLimit hlim).trans le_self_add
    have hb : 2 * (k + 1) ≤ g (2 * (k + 1) + n) := by have := hg (2 * (k + 1) + n); omega
    rw [(actualControlledCountRecursion g _ heps).2 hn]
    unfold actualControlledStep
    rw [small_limitPart_tail _ hlim, actualFiniteHeadNorm, actualFiniteHeadMaximum k _ hb, ih]

end LogicLineages.OrdinalComparison
