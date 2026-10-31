module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlTargets
public import LogicLineages.OrdinalComparison.ElementaryControl
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl.Proof

theorem error_bound (b : Nat) (H : Nat×Nat → Bool) (n : Nat) : error b H n ≤ 1 := by
  unfold error
  split_ifs <;> omega

theorem bounds (b : Nat) (H : Nat×Nat → Bool) (n : Nat) :
    Phi n ≤ control b H n ∧ control b H n ≤ Phi n+1 := by
  have h := error_bound b H n
  unfold control
  omega

theorem prefix_exact (b : Nat) (H : Nat×Nat → Bool) (n : Nat) (hn : n≤b) :
    control b H n=Phi n := by
  simp [control, error, hn]

theorem perturbation (b : Nat) (H : Nat×Nat → Bool) (n : Nat) :
    0≤control b H n-Phi n ∧ control b H n-Phi n≤1 := by
  have h := bounds b H n
  omega

theorem between (b : Nat) (H : Nat×Nat → Bool) (n : Nat) :
    Phi n≤control b H n ∧ control b H n<Phi (n+1) := by
  have h := bounds b H n
  have hg := Phi_linear_gap n
  omega

theorem growth (b : Nat) (H : Nat×Nat → Bool) (n : Nat) :
    4*control b H n<control b H (n+1) := by
  have h := bounds b H n
  have h' := bounds b H (n+1)
  have hg := Phi_linear_gap n
  omega

theorem margin_all (b : Nat) (H : Nat×Nat → Bool) (v a : Nat) :
    control b H v+2*a≤control b H (v+a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hg := growth b H (v+a)
    have hb := (bounds b H (v+a)).1
    have hp := four_le_Phi (v+a)
    have he : v+(a+1)=v+a+1 := by omega
    rw [he]
    omega

theorem twice_le_pow (n : Nat) : 2*n≤2^n := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.pow_succ]
      have hn : 1≤n+1 := by omega
      omega

theorem upper_level (b : Nat) (H : Nat×Nat → Bool) (n : Nat) (hn : 101≤n) :
    control b H n≤fastControl 6 n := by
  have hs : n+101≤fastControl 5 n := by
    have hp := twice_le_pow n
    have hf := two_pow_le_fastControl 5 n
    omega
  have hm := (fastControl_strictMono 5).monotone hs
  have hi := (iterate_index_mono (fun x => (self_lt_fastControl 5 x).le) n)
    (show 2≤n+1 by omega)
  have ht : fastControl 5 (fastControl 5 n)≤fastControl 6 n := by
    change fastControl 5 (fastControl 5 n) ≤ (fastControl 5)^[n+1] n
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hi
  have he : Phi (n+1)=fastControl 5 (n+101) := by
    unfold Phi
    congr 1
  have hb := (between b H n).2
  rw [he] at hb
  exact hb.le.trans (hm.trans ht)
end LogicLineages.OrdinalComparison.PerturbedControl.Proof
