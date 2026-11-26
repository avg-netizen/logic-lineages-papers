module
public import LogicLineages.PermittedControl.SelectedLeadingSignCutoffTargets
import Mathlib.Data.Nat.Log

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedLeadingSignCutoff

theorem cutoffEffective : CutoffEffective := by
  have sum : Primrec (fun p : Nat × Nat => p.1 + p.2 + 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd) (Primrec.const 2)
  exact (Primrec.nat_mul.comp (Primrec.const 4) sum).to₂

private theorem squareBelowPower (n : Nat) (large : 4 ≤ n) : n*n ≤ 2^n := by
  induction n,large using Nat.le_induction with
  | base => decide
  | succ n large ih =>
    have linear : 2*n+1 ≤ n*n :=
      (show 2*n+1 ≤ 3*n by omega).trans
        (Nat.mul_le_mul_right n (show 3 ≤ n by omega))
    rw [Nat.pow_succ]
    calc
      (n+1)*(n+1) = n*n+(2*n+1) := by
        simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
        omega
      _ ≤ 2*(n*n) := by omega
      _ ≤ 2*2^n := Nat.mul_le_mul_left 2 ih
      _ = 2^n*2 := Nat.mul_comm _ _

theorem absoluteErrorBelowHalf : AbsoluteErrorBelowHalf := by
  intro K K₀ C tail
  let n := Nat.log2 C
  have large : cutoff K K₀ ≤ n := tail
  unfold cutoff at large
  have quadratic : n*n ≤ 2^n := squareBelowPower n (by omega)
  have coefficient : 2*K + 1 ≤ n := by omega
  have expanded := Nat.mul_le_mul_right n coefficient
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at expanded
  have error : 2*(K*n+K₀) < n*n := by omega
  have positive : C ≠ 0 := by
    intro zero
    have invalid : cutoff K K₀ ≤ 0 := by simpa [zero] using tail
    unfold cutoff at invalid
    omega
  have logarithm : 2^n ≤ C := by
    change 2 ^ Nat.log2 C ≤ C
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 positive
  exact error.trans_le (quadratic.trans logarithm)

end LogicLineages.PermittedControl.SelectedLeadingSignCutoff
