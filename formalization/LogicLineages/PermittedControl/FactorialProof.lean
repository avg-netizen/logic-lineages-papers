module
public import LogicLineages.PermittedControl.FactorialTargets
public import LogicLineages.PermittedControl.NearGrowthProof
public import LogicLineages.PermittedControl.EffectivityProof

@[expose] public section
namespace LogicLineages.PermittedControl

 theorem G_large (n : Nat) : 2 * n + 4 ≤ G n := by
  have h := twice_self_le_two_pow (n := n + 100) (by omega)
  have h' := OrdinalComparison.two_pow_le_fastControl 5 (n + 100)
  change 2 ^ (n + 100) ≤ G n at h'
  omega

 theorem twice_le_factorial {a : Nat} (ha : 3 ≤ a) : 2 * a ≤ Nat.factorial a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have h : 2 ≤ Nat.factorial k := by
    simpa using Nat.factorial_le (show 2 ≤ k by omega)
  simpa [Nat.factorial_succ, Nat.mul_comm] using Nat.mul_le_mul_left (k + 1) h

 theorem factorialControl_cast (n : Nat) : (factorialControl n : Int) =
    (Nat.factorial (G n) : Int) + 2 * (potential n : Int) - 2 := by
  have hg := G_large n
  have hf := twice_le_factorial (a := G n) (by omega)
  unfold factorialControl
  rw [Int.natCast_sub (by omega : 2 ≤ Nat.factorial (G n) + 2 * potential n)]
  simp

 theorem factorial_primrec : Primrec Nat.factorial := by
  have hs : Primrec₂ (fun n v : Nat => (n + 1) * v) :=
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  apply (Primrec.nat_rec₁ 1 hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, Nat.factorial_succ, ih]

 theorem factorialControl_primrec : Primrec factorialControl :=
  Primrec.nat_sub.comp
    (Primrec.nat_add.comp (factorial_primrec.comp OrdinalComparison.Phi_primrec)
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))) (Primrec.const 2)

 theorem factorialControl_ge (n : Nat) : G n ≤ factorialControl n := by
  have hg := G_large n
  have hf := twice_le_factorial (a := G n) (by omega)
  unfold factorialControl
  omega

 theorem factorialControl_le_twice_factorial (n : Nat) :
    factorialControl n ≤ 2 * Nat.factorial (G n) := by
  have hg := G_large n
  have hf := Nat.self_le_factorial (G n)
  have hp : 2 * potential n ≤ n := by unfold potential; omega
  unfold factorialControl
  omega

 theorem factorialControl_congruence (m n : Nat) (hm : 0 < m) (hn : m ≤ n) :
    Int.ModEq (2 * (m : Int)) (factorialControl n : Int)
      (2 * (potential n : Int) - 2) := by
  have hg := G_large n
  have hd : 2 * m ∣ Nat.factorial (G n) := Nat.dvd_factorial (by omega) (by omega)
  have hdi : (2 * (m : Int)) ∣ (Nat.factorial (G n) : Int) := by
    exact_mod_cast hd
  have h := (Int.modEq_zero_iff_dvd.mpr hdi).add_right (2 * (potential n : Int) - 2)
  rw [factorialControl_cast]
  convert h using 1 <;> omega

 theorem factorialControl_even (n : Nat) : 2 ∣ factorialControl n := by
  have hg := G_large n
  have hd : 2 ∣ Nat.factorial (G n) := Nat.dvd_factorial (by decide) (by omega)
  have hdi : (2 : Int) ∣ (Nat.factorial (G n) : Int) := Int.natCast_dvd_natCast.mpr hd
  have he : (2 : Int) ∣ 2 * (potential n : Int) - 2 := ⟨(potential n : Int) - 1, by omega⟩
  have h := Int.dvd_add hdi he
  have heq : (Nat.factorial (G n) : Int) + (2 * (potential n : Int) - 2) = (factorialControl n : Int) := by
    rw [factorialControl_cast]
    omega
  rw [heq] at h
  exact Int.natCast_dvd_natCast.mp h

 theorem factorialControl_potential (m n : Nat) (hm : 0 < m) (hn : max m 0 ≤ n) :
    Int.ModEq (m : Int) (potential (factorialControl n) : Int) ((potential n : Int) - 1) := by
  have h := factorialControl_congruence m n hm (by omega)
  have he : (factorialControl n : Int) = 2 * (potential (factorialControl n) : Int) := by
    have hd := Nat.mod_eq_zero_of_dvd (factorialControl_even n)
    unfold potential
    omega
  rw [he] at h
  have h' : Int.ModEq (2 * (m : Int)) (2 * (potential (factorialControl n) : Int))
      (2 * ((potential n : Int) - 1)) := by convert h using 1 <;> omega
  exact h'.mul_left_cancel' (by decide : (2 : Int) ≠ 0)

 theorem four_tower_le_fastControl {j x : Nat} (hj : 1 ≤ j) (hx : 3 ≤ x) :
    2 ^ (2 ^ (2 ^ (2 ^ x))) ≤ OrdinalComparison.fastControl j x := by
  have h := (OrdinalComparison.iterate_index_mono
    (fun z => (OrdinalComparison.self_lt_fastControl 0 z).le) x)
    (show 4 ≤ x + 1 by omega)
  have hfirst : 2 ^ (2 ^ (2 ^ (2 ^ x))) ≤ OrdinalComparison.fastControl 1 x := by
    simpa [OrdinalComparison.fastControl, Function.iterate_succ_apply'] using h
  exact hfirst.trans ((OrdinalComparison.fastControl_level_mono x) hj)

 theorem factorialControl_tower_bound (n : Nat) : factorialControl n ≤ 2 ^ (2 ^ (G n + 1)) :=
  (factorialControl_le_twice_factorial n).trans (two_factorial_le_double_pow (G n))

 theorem factorialControl_separation (n : Nat) :
    2 ^ (2 ^ factorialControl n) ≤ factorialControl (n + 1) := by
  have hg := G_large n
  have ht := four_tower_le_fastControl (j := 4) (x := G n + 1) (by decide) (by omega)
  have hnext : OrdinalComparison.fastControl 4 (G n + 1) ≤ G (n + 1) := by
    simpa only [G, OrdinalComparison.Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using OrdinalComparison.fastControl_step_growth 4 (n + 100)
  exact (Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_right (by decide) (factorialControl_tower_bound n))).trans
    (ht.trans (hnext.trans (factorialControl_ge (n + 1))))

 theorem factorialControl_lt_nextG (n : Nat) : factorialControl n < G (n + 1) := by
  have hg := G_large n
  have ht := four_tower_le_fastControl (j := 4) (x := G n + 1) (by decide) (by omega)
  have hnext : OrdinalComparison.fastControl 4 (G n + 1) ≤ G (n + 1) := by
    simpa only [G, OrdinalComparison.Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using OrdinalComparison.fastControl_step_growth 4 (n + 100)
  exact (factorialControl_tower_bound n).trans_lt
    ((Nat.lt_two_pow_self (n := 2 ^ (2 ^ (G n + 1)))).trans_le
      ((Nat.lt_two_pow_self (n := 2 ^ (2 ^ (2 ^ (G n + 1))))).le.trans (ht.trans hnext)))

 theorem factorialControl_eventual (n : Nat) (hn : 101 ≤ n) :
    factorialControl n ≤ OrdinalComparison.fastControl 6 n := by
  have hs : n + 101 ≤ OrdinalComparison.fastControl 5 n := by
    have h := twice_self_le_two_pow (n := n) (by omega)
    have h' := OrdinalComparison.two_pow_le_fastControl 5 n
    omega
  have hseed := (OrdinalComparison.fastControl_strictMono 5).monotone hs
  have hi := (OrdinalComparison.iterate_index_mono
    (fun z => (OrdinalComparison.self_lt_fastControl 5 z).le) n) (show 2 ≤ n + 1 by omega)
  have hit : OrdinalComparison.fastControl 5 (OrdinalComparison.fastControl 5 n) ≤
      OrdinalComparison.fastControl 6 n := by
    change OrdinalComparison.fastControl 5 (OrdinalComparison.fastControl 5 n) ≤
      ((OrdinalComparison.fastControl 5)^[n + 1]) n
    simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] using hi
  have hG : G (n + 1) ≤ OrdinalComparison.fastControl 5 (OrdinalComparison.fastControl 5 n) := by
    simpa only [G, OrdinalComparison.Phi, Nat.add_assoc] using hseed
  exact (factorialControl_lt_nextG n).le.trans (hG.trans hit)

 theorem factorialControlLaws : Targets.FactorialControlLaws :=
  ⟨factorialControl_cast, factorialControl_primrec, factorialControl_even, factorialControl_ge,
    factorialControl_le_twice_factorial, factorialControl_separation, factorialControl_lt_nextG,
    factorialControl_eventual, factorialControl_potential⟩

 theorem factorialControlOrbit : Targets.FactorialControlOrbit := by
  intro m t i hm ht
  induction i with
  | zero => simp [Int.ModEq]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hti : t ≤ (factorialControl^[i]) t := OrdinalComparison.iterate_self_le
      (fun x => (OrdinalComparison.self_lt_Phi x).le.trans (factorialControl_ge x)) i t
    have hs := factorialControl_potential m ((factorialControl^[i]) t) hm (ht.trans hti)
    have h := hs.trans (ih.sub_right 1)
    convert h using 1 <;> simp only [Int.natCast_add, Int.natCast_one] <;> omega

end LogicLineages.PermittedControl
