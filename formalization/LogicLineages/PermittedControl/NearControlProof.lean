module
public import LogicLineages.PermittedControl.Targets
public import LogicLineages.OrdinalComparison.Control
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.PermittedControl

 theorem initialLcm_pos (n : Nat) : 0 < initialLcm n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.lcm_pos_iff.mpr ⟨ih, Nat.succ_pos n⟩

 theorem dvd_initialLcm {m n : Nat} (hm : 0 < m) (hmn : m ≤ n) :
    m ∣ initialLcm n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : m ≤ n
    · exact (ih h).trans (Nat.dvd_lcm_left _ _)
    · have heq : m = n + 1 := by omega
      subst m
      exact Nat.dvd_lcm_right _ _

 theorem G_even (n : Nat) : 2 ∣ G n := by
  have hf : ∀ j x, 0 < x → 2 ∣ OrdinalComparison.fastControl j x := by
    intro j
    induction j with
    | zero =>
      intro x hx
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
      exact ⟨2 ^ k, by simp [OrdinalComparison.fastControl, pow_succ, Nat.mul_comm]⟩
    | succ j ih =>
      intro x hx
      change 2 ∣ ((OrdinalComparison.fastControl j)^[x + 1]) x
      rw [Function.iterate_succ_apply']
      apply ih
      exact hx.trans_le (OrdinalComparison.iterate_self_le
        (fun y => (OrdinalComparison.self_lt_fastControl j y).le) x x)
  exact hf 5 (n + 100) (by omega)

 theorem correction_cast (n : Nat) :
    (correction n : Int) =
      (2 * (potential n : Int) - 2 - (G n : Int)) % (2 * (initialLcm n : Int)) := by
  unfold correction
  apply Int.toNat_of_nonneg
  apply Int.emod_nonneg
  have := initialLcm_pos n
  omega

 theorem correction_lt (n : Nat) : correction n < 2 * initialLcm n := by
  have hp : 0 < (2 * (initialLcm n : Int)) := by
    have := initialLcm_pos n
    omega
  have h := Int.emod_lt_of_pos (2 * (potential n : Int) - 2 - (G n : Int)) hp
  rw [← correction_cast] at h
  omega

 theorem nearControl_prefix (b n : Nat) (hn : n ≤ b) : nearControl b n = G n := by
  simp [nearControl, hn]

 theorem nearControl_ge (b n : Nat) : G n ≤ nearControl b n := by
  unfold nearControl
  split <;> omega

 theorem nearControl_distance (b n : Nat) (hn : b < n) :
    nearControl b n - G n < 2 * initialLcm n := by
  simp only [nearControl, if_neg (by omega : ¬n ≤ b), Nat.add_sub_cancel_left]
  exact correction_lt n

 theorem nearControl_congruence (b n : Nat) (hn : b < n) :
    Int.ModEq (2 * (initialLcm n : Int)) (nearControl b n : Int)
      (2 * (potential n : Int) - 2) := by
  have h := (Int.mod_modEq (2 * (potential n : Int) - 2 - (G n : Int))
    (2 * (initialLcm n : Int))).add_left (G n : Int)
  rw [← correction_cast] at h
  have heq : (nearControl b n : Int) = (G n : Int) + (correction n : Int) := by
    simp [nearControl, if_neg (by omega : ¬n ≤ b)]
  rw [heq]
  convert h using 1 <;> omega

 theorem nearControl_even (b n : Nat) : 2 ∣ nearControl b n := by
  by_cases hn : n ≤ b
  · rw [nearControl_prefix b n hn]
    exact G_even n
  · have h := (nearControl_congruence b n (by omega)).of_dvd
      (show (2 : Int) ∣ 2 * (initialLcm n : Int) from dvd_mul_right _ _)
    have hr : Int.ModEq 2 (2 * (potential n : Int) - 2) 0 := by
      apply Int.modEq_zero_iff_dvd.mpr
      exact ⟨(potential n : Int) - 1, by omega⟩
    have hz := Int.modEq_zero_iff_dvd.mp (h.trans hr)
    exact Int.natCast_dvd_natCast.mp hz

 theorem nearControl_potential (b m n : Nat) (hm : 0 < m)
    (hn : max m (b + 1) ≤ n) :
    Int.ModEq (m : Int) (potential (nearControl b n) : Int)
      ((potential n : Int) - 1) := by
  have hl : (m : Int) ∣ (initialLcm n : Int) :=
    Int.natCast_dvd_natCast.mpr (dvd_initialLcm hm (by omega))
  have h := (nearControl_congruence b n (by omega)).of_dvd
    (mul_dvd_mul_left (2 : Int) hl)
  have he : (nearControl b n : Int) = 2 * (potential (nearControl b n) : Int) := by
    have hd := Nat.mod_eq_zero_of_dvd (nearControl_even b n)
    unfold potential
    omega
  rw [he] at h
  have h' : Int.ModEq (2 * (m : Int))
      (2 * (potential (nearControl b n) : Int)) (2 * ((potential n : Int) - 1)) := by
    convert h using 1 <;> omega
  exact h'.mul_left_cancel' (by decide : (2 : Int) ≠ 0)

 theorem nearControlModular : Targets.NearControlModular :=
  ⟨nearControl_prefix, nearControl_ge, nearControl_distance,
    nearControl_even, nearControl_potential⟩

 theorem nearControlOrbit : Targets.NearControlOrbit := by
  intro b m t i hm ht
  induction i with
  | zero => simp [Int.ModEq]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hti : t ≤ ((nearControl b)^[i]) t :=
      OrdinalComparison.iterate_self_le
        (fun x => (OrdinalComparison.self_lt_Phi x).le.trans (nearControl_ge b x)) i t
    have hs := nearControl_potential b m (((nearControl b)^[i]) t) hm (ht.trans hti)
    have h := hs.trans (ih.sub_right 1)
    convert h using 1 <;> simp only [Int.natCast_add, Int.natCast_one] <;> omega

end LogicLineages.PermittedControl
