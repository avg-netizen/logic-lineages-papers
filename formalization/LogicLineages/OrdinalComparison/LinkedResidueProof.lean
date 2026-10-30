module
public import LogicLineages.OrdinalComparison.LinkedResidueTargets
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem control_power_of_two (j n : Nat) : ∃ k : Nat, fastControl j n = 2 ^ k := by
  induction j generalizing n with
  | zero => exact ⟨n, rfl⟩
  | succ j ih =>
    change ∃ k : Nat, (fastControl j)^[n + 1] n = 2 ^ k
    rw [Function.iterate_succ_apply']
    exact ih _

theorem actualLinkedBudgetExponent : Targets.ActualLinkedBudgetExponent := by
  intro u
  obtain ⟨k, hk⟩ := control_power_of_two 5 (u + 100)
  have hb : actualLinkedBudget u = 2 ^ k := hk
  have hlog : actualLinkedBinaryExponent u = k := by
    unfold actualLinkedBinaryExponent
    rw [hb, Nat.log_pow (by decide)]
  rw [hlog]
  refine ⟨hb, ?_⟩
  have ht : 2 ^ (2 ^ (u + 100)) ≤ actualLinkedBudget u :=
    two_tower_le_fastControl (by decide : 1 ≤ 5) (by omega : 1 ≤ u + 100)
  rw [hb] at ht
  exact (Nat.pow_le_pow_iff_right (by decide)).mp ht

private theorem linked_quadratic_bound (u : Nat) (hu : 4 ≤ u) :
    u ^ 2 + 100 < 2 ^ (u + 100) := by
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u hu ih =>
    have hs : (u + 1) ^ 2 + 100 ≤ 2 * (u ^ 2 + 100) := by
      have hmul := Nat.mul_le_mul_left u hu
      nlinarith
    have h := hs.trans_lt (Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 2))
    simpa only [show u + 1 + 100 = u + 100 + 1 by omega, pow_succ, Nat.mul_comm] using h

theorem actualLinkedResidueArithmetic : Targets.ActualLinkedResidueArithmetic := by
  intro u hu
  let B := actualLinkedBudget u
  let K := actualLinkedBinaryExponent u
  let r := actualLinkedHalfExponent u
  let q := actualLinkedModulus u
  let m := actualLinkedTail u
  let D := actualLinkedDegree u
  let e := actualLinkedOffset u
  let d := actualLinkedCutoff u
  change 96 ≤ r ∧ D < r ∧ 2 * e < D ∧ 0 < D - 2 * e ∧ D - 2 * e < q ∧
    q = B / 2 + 1 ∧ u ≤ B ∧ q ≤ d ∧ d < 2 * q ∧ m < q ∧ d - q = q - 1 - m
  have hexp := actualLinkedBudgetExponent u
  have hbig : u ^ 2 + 100 < K := (linked_quadratic_bound u hu).trans_le hexp.2
  have hrbig : u ^ 2 + 100 ≤ r := by dsimp only [r, actualLinkedHalfExponent]; change u ^ 2 + 100 ≤ K - 1; omega
  have hrK : r + 1 = K := by dsimp only [r, actualLinkedHalfExponent]; change K - 1 + 1 = K; omega
  have hB : B = 2 ^ r * 2 := by
    change actualLinkedBudget u = _
    rw [hexp.1]
    change 2 ^ K = _
    rw [← hrK, pow_succ]
  have hq : q = 2 ^ r + 1 := rfl
  have hlinear : B + 2 = 2 * q := by rw [hB, hq]; ring
  have hqb : q = B / 2 + 1 := by rw [hB, hq, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  have hm : m + 2 = u := by dsimp [m, actualLinkedTail]; omega
  have he : e + 4 = u := by dsimp [e, actualLinkedOffset]; omega
  have hD : 2 * D = m * (m + 1) := by
    change 2 * (m * (m + 1) / 2) = m * (m + 1)
    exact Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one m)
  have hDle : D ≤ u ^ 2 := by nlinarith
  have hDelta : 2 * e < D := by nlinarith
  have hulower : u ≤ u ^ 2 := by nlinarith
  have hpowr : r < 2 ^ r := Nat.lt_two_pow_self
  have hqbig : u + 2 < q := by omega
  have hd : d = B - u + 3 := rfl
  refine ⟨by omega, by omega, hDelta, by omega, by omega, hqb, by omega,
    by omega, by omega, by omega, by omega⟩

end LogicLineages.OrdinalComparison
