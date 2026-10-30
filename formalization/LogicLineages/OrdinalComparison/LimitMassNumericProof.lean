module
public import LogicLineages.OrdinalComparison.LimitMassNumericTargets
public import Mathlib.Order.Iterate

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualPhiSquareGap : Targets.ActualPhiSquareGap := by
  intro n
  by_cases hn : n=0
  · subst n
    simpa using self_lt_Phi 0
  have hp : 0 < n := Nat.pos_of_ne_zero hn
  have ht : n < 2^n := Nat.lt_two_pow_self
  have hsq := (Nat.mul_lt_mul_of_pos_left ht hp).trans_le (Nat.mul_le_mul_right (2^n) ht.le)
  rw [← Nat.pow_add] at hsq
  have he : n+n ≤ 2^(n+1) := by rw [Nat.pow_succ]; omega
  have hbase := hsq.trans_le (Nat.pow_le_pow_right (by decide) he)
  have hshift : 2^(n+1) ≤ 2^(n+100) := Nat.pow_le_pow_right (by decide) (by omega)
  have htower : 2^(2^(n+100)) ≤ Phi n :=
    two_tower_le_fastControl (j := 5) (n := n+100) (by decide) (by omega)
  exact hbase.trans_le ((Nat.pow_le_pow_right (by decide) hshift).trans htower)

private theorem limitmass_iterate_growth (t d : Nat) : t+d ≤ (Phi^[d]) t := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    have hh := self_lt_Phi ((Phi^[d]) t)
    omega

theorem actualLimitMassNumericalGap : Targets.ActualLimitMassNumericalGap := by
  intro R t D q p ht hD hq hp
  dsimp only
  let Z := (Phi^[D]) t
  have hgrow := limitmass_iterate_growth t D
  have hDZ : D < Z := by omega
  have hTZ : t ≤ Z := by omega
  have hV : Phi Z ≤ (Phi^[q]) (Phi (Phi t)) := by
    have hi := iterate_index_mono (fun n => (self_lt_Phi n).le) t (show D+1 ≤ q+2 by omega)
    have hr : (Phi^[q+2]) t=(Phi^[q]) (Phi (Phi t)) := by
      rw [Function.iterate_add_apply]
      rfl
    change (Phi^[D+1]) t ≤ (Phi^[q+2]) t at hi
    rw [Function.iterate_succ_apply', hr] at hi
    exact hi
  have hprod : (R+3)*Z ≤ Z*Z := Nat.mul_le_mul_right Z (by omega)
  have hsum : p+Z+D < (R+3)*Z := by
    change p ≤ (R+1)*Z at hp
    simp only [Nat.add_mul, Nat.one_mul] at hp ⊢
    omega
  have hh := (hsum.trans_le hprod).trans (actualPhiSquareGap Z) |>.trans_le hV
  change Z+D < (Phi^[q]) (Phi (Phi t))-p
  omega

end LogicLineages.OrdinalComparison
