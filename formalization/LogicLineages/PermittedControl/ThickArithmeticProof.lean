module
public import LogicLineages.PermittedControl.ThickBlockFactsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem rounded_charge_rigidity (N c d R M : Nat) (hcd : c < d) (hd : d ≤ R) (hM : R < M)
    (hmod : Int.ModEq (M : Int) (((N+c+1)/2 : Nat) : Int) (((N+d+1)/2 : Nat) : Int)) :
    d=c+1 ∧ (N+c)%2=1 := by
  have hn : Nat.ModEq M ((N+c+1)/2) ((N+d+1)/2) := Int.natCast_modEq_iff.mp hmod
  have hb : |(((N+d+1)/2 : Nat) : Int)-(((N+c+1)/2 : Nat) : Int)| < (M : Int) := by
    rw [abs_of_nonneg (by omega)]
    omega
  have heq := hn.eq_of_abs_lt hb
  omega

 theorem thick_lcm_bounds (R : Nat) : 0 < initialLcm (R+1) ∧ R < initialLcm (R+1) := by
  have hp := initialLcm_pos (R+1)
  have hd := dvd_initialLcm (m := R+1) (n := R+1) (by omega) le_rfl
  exact ⟨hp, lt_of_lt_of_le (by omega) (Nat.le_of_dvd hp hd)⟩

 theorem equal_entry_rounded_mod (M p i c d N : Nat)
    (h1 : Int.ModEq (M : Int) (i : Int) ((p : Int)-(((N+c+1)/2 : Nat) : Int)))
    (h2 : Int.ModEq (M : Int) (i : Int) ((p : Int)-(((N+d+1)/2 : Nat) : Int))) :
    Int.ModEq (M : Int) (((N+c+1)/2 : Nat) : Int) (((N+d+1)/2 : Nat) : Int) := by
  have h := (h1.symm.trans h2).sub_left (p : Int)
  simpa only [sub_sub_cancel] using h

 theorem selected_even_next_residue (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (M E : Nat) (hM : 0 < M) (ht : max M B ≤ E) (heven : 2 ∣ E) :
    Int.ModEq (2*(M : Int)) (f E : Int) ((E : Int)-2) := by
  have h := bare_iterate_residue f B hf M E 1 hM ht (by omega)
  have he : E=2*potential E := by
    have hm := Nat.mod_eq_zero_of_dvd heven
    unfold potential
    omega
  simpa only [Function.iterate_one, Int.natCast_one, mul_one, ← Int.natCast_mul, ← he] using h

 theorem moving_local_residue (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (M E c n w : Nat) (hM : 0 < M) (ht : max M B ≤ E) (heven : 2 ∣ E)
    (hodd : (n+c)%2=1)
    (hentry : Int.ModEq (2*(M : Int)) (E : Int) (2*(((n+c+1)/2 : Nat) : Int)))
    (Pnorm : Nat) (hn : n=Pnorm+(1+w)) (hpaid : c+Pnorm ≤ f E) :
    Int.ModEq (2*(M : Int)) ((f E-c-Pnorm : Nat) : Int) (w : Int) := by
  have hceil : 2*((n+c+1)/2)=n+c+1 := by omega
  have hentry' : Int.ModEq (2*(M : Int)) (E : Int) ((n : Int)+(c : Int)+1) := by
    convert hentry using 1 <;> omega
  have hnext := (selected_even_next_residue f B hf M E hM ht heven).trans (hentry'.sub_right 2)
  have h := hnext.sub_right ((c : Int)+(Pnorm : Int))
  convert h using 1 <;> omega

end LogicLineages.PermittedControl
