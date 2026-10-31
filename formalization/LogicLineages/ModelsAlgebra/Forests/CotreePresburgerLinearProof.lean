module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinearTargets
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear.Proof
open FirstOrder Language

@[simp] theorem eval_const {n : Nat} (z : Int) (v : Fin n → Int) :
    (Affine.const z).eval v = z := by simp [Affine.eval, Affine.const]

@[simp] theorem eval_var {n : Nat} (i : Fin n) (v : Fin n → Int) :
    (Affine.var i).eval v = v i := by simp [Affine.eval, Affine.var, ite_mul]

@[simp] theorem eval_add {n : Nat} (s t : Affine n) (v : Fin n → Int) :
    (Affine.add s t).eval v = s.eval v + t.eval v := by
  simp only [Affine.eval, Affine.add, add_mul, Finset.sum_add_distrib]
  omega

@[simp] theorem eval_scale {n : Nat} (z : Int) (t : Affine n) (v : Fin n → Int) :
    (Affine.scale z t).eval v = z * t.eval v := by
  simp [Affine.eval, Affine.scale, mul_add, Finset.mul_sum, mul_assoc]

theorem termTranslationExact : Targets.TermTranslationExact := by
  intro n t v
  induction t with
  | var i => simp [Affine.ofTerm]
  | func f ts ih =>
    cases f <;> simp [Affine.ofTerm, Term.realize, ih]

theorem lastVariableSplitExact : Targets.LastVariableSplitExact := by
  intro n t v x
  simp only [Affine.eval, Affine.dropLast, Affine.lastCoeff,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  omega

theorem substitutionExact : Targets.SubstitutionExact := by
  intro n t s v
  rw [Affine.substLast, eval_add, eval_scale, lastVariableSplitExact]

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear.Proof
