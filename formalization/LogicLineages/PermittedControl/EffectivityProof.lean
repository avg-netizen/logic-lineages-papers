module
public import LogicLineages.PermittedControl.EffectivityTargets
public import LogicLineages.PermittedControl.NearControlProof
public import LogicLineages.OrdinalComparison.ControlComputability
public import Mathlib.Data.Nat.Find

@[expose] public section
namespace LogicLineages.PermittedControl

 theorem gcd_search (a b : Nat) :
    Nat.findGreatest (fun d => a % d = 0 ∧ b % d = 0) (a + b) = Nat.gcd a b := by
  by_cases hz : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a; subst b; rfl
  · have hbound : Nat.gcd a b ≤ a + b := by
      by_cases ha : a = 0
      · simp [ha]
      · exact (Nat.gcd_le_left b (by omega)).trans (Nat.le_add_right _ _)
    have hgood : a % Nat.gcd a b = 0 ∧ b % Nat.gcd a b = 0 :=
      ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left _ _),
       Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right _ _)⟩
    apply Nat.le_antisymm
    · have hs := Nat.findGreatest_spec (P := fun d => a % d = 0 ∧ b % d = 0) hbound hgood
      have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hs.1) (Nat.dvd_of_mod_eq_zero hs.2)
      exact Nat.le_of_dvd (Nat.gcd_pos_iff.mpr (by omega)) hd
    · exact Nat.le_findGreatest hbound hgood

 theorem gcd_primrec : Primrec₂ Nat.gcd := by
  have hp : PrimrecRel (fun (p : Nat × Nat) (d : Nat) => p.1 % d = 0 ∧ p.2 % d = 0) :=
    PrimrecPred.and
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.const 0))
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const 0))
  exact (Primrec.nat_findGreatest Primrec.nat_add hp).of_eq (fun p => gcd_search p.1 p.2)

 theorem lcm_primrec : Primrec₂ Nat.lcm :=
  (Primrec.nat_div.comp Primrec.nat_mul gcd_primrec).of_eq (fun p => (Nat.lcm_eq_mul_div p.1 p.2).symm)

 theorem initialLcm_primrec : Primrec initialLcm := by
  have hs : Primrec₂ (fun n v : Nat => Nat.lcm v (n + 1)) :=
    (lcm_primrec.comp Primrec.snd (Primrec.succ.comp Primrec.fst)).to₂
  apply (Primrec.nat_rec₁ 1 hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, initialLcm, ih]

/-- Natural-code implementation used only after proving equality to the
original integer remainder. The extra positive modulus prevents underflow. -/
def correctionCode (n : Nat) : Nat :=
  (2 * potential n + 2 * initialLcm n - ((G n + 2) % (2 * initialLcm n))) %
    (2 * initialLcm n)

 theorem correctionCode_eq (n : Nat) : correctionCode n = correction n := by
  let M := 2 * initialLcm n
  have hM : 0 < M := by dsimp [M]; have := initialLcm_pos n; omega
  have hrem : (G n + 2) % M < M := Nat.mod_lt _ hM
  have hsub : (G n + 2) % M ≤ 2 * potential n + M := by omega
  have hc : (correctionCode n : Int) =
      (2 * (potential n : Int) + (M : Int) - ((G n + 2 : Nat) : Int) % (M : Int)) % (M : Int) := by
    unfold correctionCode
    change (((2 * potential n + M - ((G n + 2) % M)) % M : Nat) : Int) = _
    rw [Int.natCast_emod, Int.natCast_sub hsub]
    simp only [Int.natCast_add, Int.natCast_mul, Nat.cast_ofNat, Int.natCast_emod]
  have hB := Int.mod_modEq ((G n + 2 : Nat) : Int) (M : Int)
  have hA : Int.ModEq (M : Int) (2 * (potential n : Int) + (M : Int))
      (2 * (potential n : Int)) := Int.add_modEq_right
  have h := hA.sub hB
  apply Int.ofNat_inj.mp
  rw [hc, correction_cast]
  change Int.ModEq (M : Int) _ _ at h
  have heq : 2 * (potential n : Int) - ((G n + 2 : Nat) : Int) =
      2 * (potential n : Int) - 2 - (G n : Int) := by omega
  rw [heq] at h
  exact h

 theorem correctionCode_primrec : Primrec correctionCode := by
  have hp : Primrec potential := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hM : Primrec (fun n => 2 * initialLcm n) :=
    Primrec.nat_mul.comp (Primrec.const 2) initialLcm_primrec
  have hA : Primrec (fun n => 2 * potential n) :=
    Primrec.nat_mul.comp (Primrec.const 2) hp
  have hB : Primrec (fun n => (G n + 2) % (2 * initialLcm n)) :=
    Primrec.nat_mod.comp (Primrec.nat_add.comp OrdinalComparison.Phi_primrec (Primrec.const 2)) hM
  exact Primrec.nat_mod.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp hA hM) hB) hM

 theorem correction_primrec : Primrec correction :=
  correctionCode_primrec.of_eq correctionCode_eq

 theorem nearControl_primrec : Primrec₂ nearControl :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (OrdinalComparison.Phi_primrec.comp Primrec.snd)
    (Primrec.nat_add.comp (OrdinalComparison.Phi_primrec.comp Primrec.snd)
      (correction_primrec.comp Primrec.snd))

 theorem nearControlPrimitiveRecursive : Targets.NearControlPrimitiveRecursive :=
  ⟨initialLcm_primrec, correction_primrec, nearControl_primrec⟩

end LogicLineages.PermittedControl
