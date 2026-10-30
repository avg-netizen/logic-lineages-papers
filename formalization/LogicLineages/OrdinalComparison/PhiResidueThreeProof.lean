module
public import LogicLineages.OrdinalComparison.ThetaEntryTargets
public import LogicLineages.OrdinalComparison.ControlResidueProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem double_power_mod_three (n : Nat) (hn : 1 ≤ n) :
    Nat.ModEq 3 (2 ^ (2 ^ n)) 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hbase : Nat.ModEq 3 (2 ^ 2) 1 := by decide
  have h := hbase.pow (2 ^ k)
  have hpow : (2 ^ 2) ^ (2 ^ k) = 2 ^ (2 ^ (k + 1)) := by
    rw [← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
  rw [hpow, Nat.one_pow] at h
  exact h

private theorem first_control_mod_three (n : Nat) (hn : 1 ≤ n) :
    Nat.ModEq 3 (fastControl 1 n) 1 := by
  let z := ((fastControl 0)^[n - 1]) n
  have hz : 1 ≤ z := hn.trans
    (iterate_self_le (fun x => (self_lt_fastControl 0 x).le) (n - 1) n)
  have heq : fastControl 1 n = 2 ^ (2 ^ z) := by
    change ((fastControl 0)^[n + 1]) n = _
    rw [show n + 1 = 2 + (n - 1) by omega, Function.iterate_add_apply]
    rfl
  rw [heq]
  exact double_power_mod_three z hz

private theorem higher_control_mod_three (j : Nat) :
    ∀ n : Nat, 1 ≤ n → Nat.ModEq 3 (fastControl (j + 1) n) 1 := by
  induction j with
  | zero => intro n hn; exact first_control_mod_three n hn
  | succ j ih =>
    intro n hn
    let z := ((fastControl (j + 1))^[n]) n
    have hz : 1 ≤ z := hn.trans
      (iterate_self_le (fun x => (self_lt_fastControl (j + 1) x).le) n n)
    have heq : fastControl (j + 1 + 1) n = fastControl (j + 1) z := by
      change ((fastControl (j + 1))^[n + 1]) n = _
      exact Function.iterate_succ_apply' _ _ _
    rw [heq]
    exact ih z hz

theorem actualPhiResidueThree : Targets.ActualPhiResidueThree := by
  intro v
  exact higher_control_mod_three 4 (v + 100) (by omega)

end LogicLineages.OrdinalComparison
