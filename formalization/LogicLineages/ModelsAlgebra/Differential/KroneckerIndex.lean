module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndexTargets
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.KroneckerIndex

private theorem index_succ (B : ℕ) {n : ℕ} (d : Fin (n + 1) → ℕ) :
    index B d = d 0 + B * index B (fun i : Fin n => d i.succ) := by
  simp only [index, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ac_rfl

theorem index_injective : Targets.kroneckerIndexInjective := by
  intro n B hB
  induction n with
  | zero =>
    intro d e _ _ _
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro d e hd he heq
    have hsum : d 0 + B * index B (fun i : Fin n => d i.succ) =
        e 0 + B * index B (fun i : Fin n => e i.succ) := by
      simpa only [index_succ] using heq
    have hzero : d 0 = e 0 := by
      have hm := congrArg (fun k : ℕ => k % B) hsum
      simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
        Nat.add_zero, Nat.mod_eq_of_lt (hd 0), Nat.mod_eq_of_lt (he 0)] using hm
    have htail : index B (fun i : Fin n => d i.succ) =
        index B (fun i : Fin n => e i.succ) := by
      rw [hzero] at hsum
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel hsum)
    have ht := ih (fun i : Fin n => d i.succ) (fun i : Fin n => e i.succ)
      (fun i => hd i.succ) (fun i => he i.succ) htail
    funext i
    exact Fin.cases hzero (fun j => congrFun ht j) i

theorem index_bound : Targets.kroneckerIndexBound := by
  intro n B hB
  induction n with
  | zero =>
    intro d _
    simp [index]
  | succ n ih =>
    intro d hd
    have ht := ih (fun i : Fin n => d i.succ) (fun i => hd i.succ)
    rw [index_succ]
    calc
      d 0 + B * index B (fun i : Fin n => d i.succ) <
          B + B * index B (fun i : Fin n => d i.succ) := Nat.add_lt_add_right (hd 0) _
      _ = B * (index B (fun i : Fin n => d i.succ) + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ B * B ^ n := Nat.mul_le_mul_left B (Nat.succ_le_of_lt ht)
      _ = B ^ (n + 1) := (pow_succ' B n).symm

theorem digits_bound : Targets.kroneckerDigitsBound := by
  intro n B k hB i
  exact Nat.mod_lt _ (by omega)

private theorem digits_succ (B n k : ℕ) (i : Fin n) :
    digits B (n + 1) k i.succ = digits B n (k / B) i := by
  simp only [digits, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]

theorem index_digits : Targets.kroneckerIndexDigits := by
  intro n B k hB hk
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    simp [index]
  | succ n ih =>
    have ht : (fun i : Fin n => digits B (n + 1) k i.succ) = digits B n (k / B) :=
      funext (digits_succ B n k)
    have hquot : k / B < B ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      simpa only [pow_succ] using hk
    rw [index_succ, ht, ih (k / B) hquot]
    simp only [digits, Fin.val_zero, pow_zero, Nat.div_one]
    exact Nat.mod_add_div k B

theorem digits_index : Targets.kroneckerDigitsIndex := by
  intro n B hB d hd
  apply index_injective n B hB _ d (digits_bound n B _ hB) hd
  exact index_digits n B (index B d) hB (index_bound n B hB d hd)

end LogicLineages.ModelsAlgebra.Differential.KroneckerIndex
