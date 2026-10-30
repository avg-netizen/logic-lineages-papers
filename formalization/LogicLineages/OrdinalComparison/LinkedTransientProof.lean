module
public import LogicLineages.OrdinalComparison.LinkedTransientTargets
public import LogicLineages.OrdinalComparison.LinkedResidueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualBinaryPoleBudgetQuadratic : Targets.ActualBinaryPoleBudgetQuadratic := by
  intro d
  unfold actualBinaryPoleBudget
  calc
    (∑ i : Fin d, 2 ^ padicValNat 2 (i.val + 1)) ≤ ∑ _i : Fin d, d := by
      apply Finset.sum_le_sum
      intro i _
      exact (Nat.le_of_dvd (Nat.succ_pos i.val) pow_padicValNat_dvd).trans
        (Nat.succ_le_of_lt i.isLt)
    _ = d ^ 2 := by simp [pow_two]

private theorem square_le_two_pow (n : Nat) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hpoly : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc
      (n + 1) ^ 2 ≤ 2 * n ^ 2 := hpoly
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

theorem actualLinkedPoleTransient : Targets.ActualLinkedPoleTransient := by
  intro u hu
  have huB : u < actualLinkedBudget u := self_lt_Phi u
  have hb4 : 4 ≤ actualLinkedBudget u := by omega
  have hdB : actualLinkedCutoff u ≤ actualLinkedBudget u := by
    unfold actualLinkedCutoff
    omega
  have hμ : actualBinaryPoleBudget (actualLinkedCutoff u) ≤ 2 ^ actualLinkedBudget u :=
    (actualBinaryPoleBudgetQuadratic _).trans
      ((Nat.pow_le_pow_left hdB 2).trans (square_le_two_pow _ hb4))
  have ha : actualBinaryPoleTransient (actualLinkedCutoff u) ≤ actualLinkedBudget u :=
    Nat.clog_le_of_le_pow hμ
  have hC : Phi (u + 1) = 2 ^ actualLinkedBinaryExponent (u + 1) :=
    (actualLinkedBudgetExponent (u + 1)).1
  have hgap := Phi_succ_gap u
  rw [hC] at hgap
  have hinner := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hgap
  have hell : actualLinkedBudget u + 1 ≤ actualLinkedBinaryExponent (u + 1) :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := Phi u + 1))).trans hinner
  exact ⟨ha, hell, hC⟩

end LogicLineages.OrdinalComparison
