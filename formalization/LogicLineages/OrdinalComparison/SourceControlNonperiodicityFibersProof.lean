module
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityTargets
public import LogicLineages.OrdinalComparison.SourcePerturbedControlValuationProof
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof

theorem fiber_base_primitive :
    Primrec (fun z : Nat × Nat × Nat => fiberBase z.1 z.2.1 z.2.2) := by
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact Primrec.nat_mul.comp
    (hpow.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (Primrec.nat_max.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd)))))

/-- The added spacing changes only the odd factor. -/
theorem fiber_point_factor (N b p e k : Nat) :
    fiberPoint N b p e k = 2^e * (2*(max N b+1+k*p)+1) := by
  unfold fiberPoint fiberBase
  rw [pow_succ]
  ring

theorem fiber_point_above (N b p e k : Nat) :
    max N b < fiberPoint N b p e k := by
  have hp : 1 ≤ 2^e := Nat.one_le_pow e 2 (by omega)
  have hm := Nat.mul_le_mul_right (2*(max N b+1+k*p)+1) hp
  rw [fiber_point_factor]
  simp only [one_mul] at hm
  omega

/-- Maximal divisibility determines the exponent without an oracle. -/
theorem valuation_of_exact_power (n e : Nat) (hn : 0 < n)
    (hd : 2^e ∣ n) (hnext : ¬ 2^(e+1) ∣ n) :
    PerturbedControl.valuationTwo n = e := by
  obtain ⟨hv, hvnext⟩ := PerturbedControl.Proof.valuation_exact n hn
  apply Nat.le_antisymm
  · by_contra h
    have he : e+1 ≤ PerturbedControl.valuationTwo n := by omega
    exact hnext ((Nat.pow_dvd_pow 2 he).trans hv)
  · by_contra h
    have he : PerturbedControl.valuationTwo n+1 ≤ e := by omega
    exact hvnext ((Nat.pow_dvd_pow 2 he).trans hd)

theorem fiber_point_valuation (N b p e k : Nat) :
    PerturbedControl.valuationTwo (fiberPoint N b p e k) = e := by
  apply valuation_of_exact_power
  · have h := fiber_point_above N b p e k
    omega
  · rw [fiber_point_factor]
    exact dvd_mul_right _ _
  · rw [fiber_point_factor, pow_succ]
    intro hd
    have hp : 0 < 2^e := pow_pos (by omega) _
    have hodd : 2 ∣ 2*(max N b+1+k*p)+1 :=
      (Nat.mul_dvd_mul_iff_left hp).1 hd
    have hm := Nat.mod_eq_zero_of_dvd hodd
    omega

theorem fiber_point_residue (N b p e k : Nat) :
    fiberPoint N b p e k % p = fiberBase N b e % p := by
  unfold fiberPoint
  have hd : p ∣ k*p*2^(e+1) := by
    exact dvd_mul_of_dvd_left (dvd_mul_left p k) _
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod]

theorem fiber_point_ge_index (N b p e k : Nat) (hp : 0 < p) :
    k ≤ fiberPoint N b p e k := by
  have hkp := Nat.mul_le_mul_left k (show 1 ≤ p by omega)
  have hpow : 1 ≤ 2^(e+1) := Nat.one_le_pow (e+1) 2 (by omega)
  have hmul := Nat.mul_le_mul_left (k*p) hpow
  simp only [mul_one] at hkp hmul
  unfold fiberPoint
  omega

theorem exactValuationFibers : Targets.ExactValuationFibers := by
  refine ⟨fiber_base_primitive, ?_⟩
  intro N b p e k hp
  exact ⟨fiber_point_above N b p e k, fiber_point_valuation N b p e k,
    fiber_point_residue N b p e k, fiber_point_ge_index N b p e k hp⟩

end LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof
