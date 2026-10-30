module
public import LogicLineages.OrdinalComparison.OmegaBlockSupplierTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem factorial_bounded_power (B d : Nat) (hd : d ≤ B) : d.factorial ≤ B ^ d := by
  induction d with
  | zero => simp only [Nat.factorial_zero, Nat.pow_zero]; exact le_rfl
  | succ d ih =>
    rw [Nat.factorial_succ, Nat.pow_succ, Nat.mul_comm (B ^ d) B]
    exact Nat.mul_le_mul hd (ih (by omega))

private theorem double_square_le_two_pow (B : Nat) (hB : 8 ≤ B) : 2 * B ^ 2 ≤ 2 ^ B := by
  induction B, hB using Nat.le_induction with
  | base => decide
  | succ B hB ih =>
    have hthree : B * 3 ≤ B * B := Nat.mul_le_mul_left B (by omega : 3 ≤ B)
    have hsquare : (B + 1) ^ 2 ≤ 2 * B ^ 2 := by
      simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    have hnext := (Nat.mul_le_mul_left 2 hsquare).trans (Nat.mul_le_mul_left 2 ih)
    exact hnext.trans_eq (by rw [Nat.pow_succ, Nat.mul_comm])

theorem restrictedPartitionDoubleExponentBound : Targets.RestrictedPartitionDoubleExponentBound := by
  intro B d m hB hd hdB hm hmB
  have hBpos : 0 < B := by omega
  have hfac : d.factorial ≤ B ^ B :=
    (factorial_bounded_power B d hdB).trans (Nat.pow_le_pow_right hBpos hdB)
  have hmpow : m ^ (d - 1) ≤ B ^ B :=
    (Nat.pow_le_pow_left hmB _).trans (Nat.pow_le_pow_right hBpos (by omega : d - 1 ≤ B))
  have hperiod : restrictedPartitionPeriod d m ≤ B ^ (2 * B) := by
    unfold restrictedPartitionPeriod
    have h := Nat.mul_le_mul hfac hmpow
    simpa only [← Nat.pow_add, show B + B = 2 * B by omega] using h
  have hbase : B ≤ 2 ^ B := (Nat.lt_two_pow_self : B < 2 ^ B).le
  have hpower : B ^ (2 * B) ≤ 2 ^ (B * (2 * B)) := by
    simpa only [Nat.pow_mul] using Nat.pow_le_pow_left hbase (2 * B)
  have hexp : B * (2 * B) ≤ 2 ^ B := by
    have h := double_square_le_two_pow B (by omega)
    simpa only [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact hperiod.trans (hpower.trans (Nat.pow_le_pow_right (by decide) hexp))

end LogicLineages.OrdinalComparison
