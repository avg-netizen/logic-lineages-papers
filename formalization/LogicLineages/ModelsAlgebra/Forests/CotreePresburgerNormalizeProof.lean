module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalizeTargets
public import Mathlib.Algebra.GroupWithZero.Divisibility
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize.Proof
open CotreePresburgerLinear CotreePresburgerLinear.Proof CotreePresburgerUnit

 theorem weight_positive {n : Nat} (a : Atom (n + 1)) : 0 < weight a := by
  unfold weight
  split_ifs with h
  · omega
  · exact Int.natAbs_pos.mpr h

theorem coefficientModulusPositive : Targets.CoefficientModulusPositive := by
  intro n p
  apply CotreePresburgerUnit.Proof.list_prod_positive
  intro a ha
  rcases List.mem_map.mp ha with ⟨b,_,rfl⟩
  exact weight_positive b

theorem leading_dvd {n : Nat} (p : QF (n + 1)) (a : Atom (n + 1))
    (ha : a ∈ p.atoms) (hz : leading a ≠ 0) : (leading a).natAbs ∣ coefficientModulus p := by
  have h : weight a ∣ coefficientModulus p := List.dvd_prod (List.mem_map.mpr ⟨a,ha,rfl⟩)
  simpa only [weight, if_neg hz] using h

theorem factor_positive (M : Nat) (a : Int) (hM : 0 < M) (ha : a ≠ 0)
    (hd : a.natAbs ∣ M) : 0 < M / a.natAbs :=
  Nat.div_pos (Nat.le_of_dvd hM hd) (Int.natAbs_pos.mpr ha)

theorem factor_mul (M : Nat) (a : Int) (hd : a.natAbs ∣ M) :
    ((M / a.natAbs : Nat) : Int) * (a.natAbs : Int) = (M : Int) := by
  rw [← Int.natCast_mul, Nat.div_mul_cancel hd]

theorem sign_scaled (M : Nat) (a : Int) (ha : a ≠ 0) (hd : a.natAbs ∣ M) :
    (nonzeroSign a).value * (M : Int) = ((M / a.natAbs : Nat) : Int) * a := by
  by_cases hp : 0 < a
  · have habs := Int.natAbs_of_nonneg (le_of_lt hp)
    simp only [nonzeroSign, if_pos hp, Sign.value, one_mul]
    calc
      _ = ((M / a.natAbs : Nat) : Int) * (a.natAbs : Int) := (factor_mul M a hd).symm
      _ = _ := by rw [habs]
  · have ha' := Int.eq_neg_natAbs_of_nonpos (le_of_not_gt hp)
    simp only [nonzeroSign, if_neg hp, Sign.value, neg_one_mul]
    calc
      _ = -(((M / a.natAbs : Nat) : Int) * (a.natAbs : Int)) := by rw [factor_mul M a hd]
      _ = ((M / a.natAbs : Nat) : Int) * (-(a.natAbs : Int)) := (mul_neg _ _).symm
      _ = _ := congrArg (fun z => ((M / a.natAbs : Nat) : Int) * z) ha'.symm

theorem scaled_eval {n : Nat} (M : Nat) (t : Affine (n + 1))
    (ha : Affine.lastCoeff t ≠ 0) (hd : (Affine.lastCoeff t).natAbs ∣ M)
    (v : Fin n → Int) (x : Int) :
    (nonzeroSign (Affine.lastCoeff t)).value * ((M : Int) * x) +
      (Affine.scale ((M / (Affine.lastCoeff t).natAbs : Nat) : Int) (Affine.dropLast t)).eval v =
    ((M / (Affine.lastCoeff t).natAbs : Nat) : Int) * t.eval (Fin.snoc v x) := by
  rw [eval_scale, lastVariableSplitExact, mul_add,
    ← mul_assoc (nonzeroSign (Affine.lastCoeff t)).value (M : Int) x,
    sign_scaled M (Affine.lastCoeff t) ha hd]
  simp only [mul_assoc, add_comm]

theorem adjust_atom_exact {n : Nat} (M : Nat) (hM : 0 < M) (a : Atom (n + 1))
    (hd : leading a ≠ 0 → (leading a).natAbs ∣ M) (v : Fin n → Int) (x : Int) :
    UnitAtom.eval v ((M : Int) * x) (adjustAtom M a) = Atom.eval (Fin.snoc v x) a := by
  cases a with
  | nonneg t =>
    by_cases hz : Affine.lastCoeff t = 0
    · have hs := lastVariableSplitExact n t v x
      simp only [hz, zero_mul, add_zero] at hs
      simp [adjustAtom, hz, UnitAtom.eval, Atom.eval, Sign.value, hs]
    · have hd' : (Affine.lastCoeff t).natAbs ∣ M := hd hz
      have hk : 0 < ((M / (Affine.lastCoeff t).natAbs : Nat) : Int) := by
        exact_mod_cast factor_positive M _ hM hz hd'
      simp only [adjustAtom, if_neg hz, UnitAtom.eval, Atom.eval]
      rw [scaled_eval M t hz hd']
      apply decide_eq_decide.mpr
      rw [mul_comm]
      exact Int.mul_nonneg_iff_of_pos_right hk
  | dvd m t =>
    by_cases hz : Affine.lastCoeff t = 0
    · have hs := lastVariableSplitExact n t v x
      simp only [hz, zero_mul, add_zero] at hs
      simp [adjustAtom, hz, UnitAtom.eval, Atom.eval, Sign.value, hs]
    · have hd' : (Affine.lastCoeff t).natAbs ∣ M := hd hz
      let k := M / (Affine.lastCoeff t).natAbs
      have hk : 0 < k := factor_positive M _ hM hz hd'
      have hkI : (k : Int) ≠ 0 := by omega
      have hm : (m + 1) * k - 1 + 1 = (m + 1) * k :=
        Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos m) hk)
      simp only [adjustAtom, if_neg hz, UnitAtom.eval, Atom.eval]
      change decide (((((m + 1) * k - 1 + 1 : Nat) : Int) ∣
        (nonzeroSign (Affine.lastCoeff t)).value * ((M : Int) * x) +
        (Affine.scale (k : Int) (Affine.dropLast t)).eval v)) =
        decide ((((m + 1 : Nat) : Int) ∣ t.eval (Fin.snoc v x)))
      rw [hm, Int.natCast_mul, scaled_eval M t hz hd']
      apply decide_eq_decide.mpr
      rw [mul_comm ((m + 1 : Nat) : Int) (k : Int)]
      exact mul_dvd_mul_iff_left hkI

theorem adjustmentExact : Targets.AdjustmentExact := by
  intro n p v x
  simp only [adjust, evalUnit, evalQF, CotreePresburgerUnit.Proof.eval_map]
  apply CotreePresburgerUnit.Proof.eval_congr
  intro a ha
  exact adjust_atom_exact (coefficientModulus p) (coefficientModulusPositive n p) a
    (leading_dvd p a ha) v x

theorem normalize_iff {n : Nat} (p : QF (n + 1)) (v : Fin n → Int) (y : Int) :
    evalUnit (normalize p) v y = true ↔ (coefficientModulus p : Int) ∣ y ∧
      evalUnit (adjust (coefficientModulus p) p) v y = true := by
  have hm : coefficientModulus p - 1 + 1 = coefficientModulus p :=
    Nat.sub_add_cancel (by have := coefficientModulusPositive n p; omega)
  simp [normalize, evalUnit, Boolean.eval, UnitAtom.eval, Sign.value, hm]

theorem normalizationExact : Targets.NormalizationExact := by
  intro n p v
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨coefficientModulus p * x, (normalize_iff p v _).mpr ⟨?_,?_⟩⟩
    · exact Int.natCast_dvd_natCast.mpr (dvd_mul_right _ _)
    · simpa only [Int.natCast_mul] using (adjustmentExact n p v (x : Int)).trans hx
  · rintro ⟨y,hy⟩
    rcases (normalize_iff p v _).mp hy with ⟨hd,hbody⟩
    rcases Int.natCast_dvd_natCast.mp hd with ⟨x,rfl⟩
    rw [Int.natCast_mul, adjustmentExact] at hbody
    exact ⟨x,hbody⟩

theorem eliminationExact : Targets.EliminationExact := by
  intro n p v
  rw [eliminate, CotreePresburgerUnit.StatementChecks.unitEliminationExact]
  exact (normalizationExact n p v).symm

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize.Proof
