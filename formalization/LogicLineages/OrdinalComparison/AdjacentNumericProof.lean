module
public import LogicLineages.OrdinalComparison.AdjacentNumericTargets
public import Mathlib.Order.Iterate

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem adjacent_iterate_growth (t d : Nat) : t+d ≤ (Phi^[d]) t := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    have hh := self_lt_Phi ((Phi^[d]) t)
    omega

theorem actualAdjacentNumericalGap : Targets.ActualAdjacentNumericalGap := by
  intro R t D q p ht hD hq hp
  dsimp only
  let Z := (Phi^[D]) t
  let d := D-1
  let s := (Phi^[d]) t
  have hDeq : D=d+1 := by dsimp only [d]; omega
  have hdq : d ≤ q := by omega
  have hZ : Z=Phi s := by
    change (Phi^[D]) t=Phi ((Phi^[d]) t)
    rw [hDeq, Function.iterate_succ_apply']
  have hgrow := adjacent_iterate_growth t D
  have hDZ : D < Z := by omega
  have hTZ : t ≤ Z := by omega
  have hgap : Phi (s+1) ≤ (Phi^[d]) (Phi (t+1)) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    apply Phi_strictMono.monotone
    exact Nat.succ_le_of_lt ((Phi_strictMono.iterate d) (Nat.lt_succ_self t))
  have hidx := iterate_index_mono (fun n => (self_lt_Phi n).le) (Phi (t+1)) hdq
  have hV : 2^(2^(Z+1)) ≤ (Phi^[q]) (Phi (t+1)) := by
    rw [hZ]
    exact (Phi_succ_gap s).trans (hgap.trans hidx)
  have hpos : 0 < Z := by omega
  have htwo : Z < 2^Z := Nat.lt_two_pow_self
  have hsq : Z*Z < 2^Z*2^Z :=
    (Nat.mul_lt_mul_of_pos_left htwo hpos).trans_le (Nat.mul_le_mul_right _ htwo.le)
  rw [← Nat.pow_add] at hsq
  have hexp : Z+Z ≤ 2^(Z+1) := by rw [Nat.pow_succ]; omega
  have hupper := hsq.trans_le (Nat.pow_le_pow_right (by decide) hexp)
  have hprod : (R+3)*Z ≤ Z*Z := Nat.mul_le_mul_right Z (by omega)
  have hsum : p+Z+D < (R+3)*Z := by
    change p ≤ (R+1)*Z at hp
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add] at hp ⊢
    omega
  have hh := hsum.trans_le hprod |>.trans hupper |>.trans_le hV
  change Z+D < (Phi^[q]) (Phi (t+1))-p
  omega

end LogicLineages.OrdinalComparison
