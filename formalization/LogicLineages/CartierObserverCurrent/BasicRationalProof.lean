module
public import LogicLineages.CartierObserverCurrent.BasicPolynomialProof
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic

theorem actualRationalSquareRootDecomposition : Targets.ActualRationalSquareRootDecomposition.{u} := by
  intro K _ _ _ f
  let E := algebraMap (Polynomial K) (RatFunc K)
  have hden : E f.denom ≠ 0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := congrArg E (actualPolynomialSquareRootDecomposition K (f.num * f.denom))
  simp only [map_mul, map_add, map_pow] at h
  change f = (E (actualPolynomialSquareRootDigit false (f.num * f.denom)) / E f.denom) ^ 2 +
    rationalX * (E (actualPolynomialSquareRootDigit true (f.num * f.denom)) / E f.denom) ^ 2
  calc
    f = E f.num / E f.denom := (RatFunc.num_div_denom f).symm
    _ = (E f.num * E f.denom) / (E f.denom) ^ 2 := by field_simp
    _ = _ := by rw [h]; dsimp [E]; field_simp

private theorem rational_square_relation {K : Type*} [Field K] [CharP K 2]
    (a b : RatFunc K) (h : a ^ 2 = rationalX * b ^ 2) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · simp only [hb, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    exact ⟨eq_zero_of_pow_eq_zero h, hb⟩
  · let r := a / b
    let E := algebraMap (Polynomial K) (RatFunc K)
    have hr : r ^ 2 = rationalX := by
      dsimp [r]
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hb)]
      exact h
    have hd : E r.denom ≠ 0 := RatFunc.algebraMap_ne_zero r.denom_ne_zero
    have hf : (E r.num / E r.denom) ^ 2 = rationalX := by
      rw [RatFunc.num_div_denom]
      exact hr
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hd)] at hf
    have hp : r.num ^ 2 = Polynomial.X * r.denom ^ 2 := by
      apply RatFunc.algebraMap_injective
      simpa only [map_mul, map_pow] using hf
    have hn := congrArg Polynomial.natDegree hp
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_mul
      (pow_ne_zero 2 r.denom_ne_zero), Polynomial.natDegree_pow] at hn
    omega

theorem actualRationalSquareRootUniqueness : Targets.ActualRationalSquareRootUniqueness.{u} := by
  intro K _ _ _ a b c d h
  have hz : (a + c) ^ 2 + rationalX * (b + d) ^ 2 = 0 := by
    calc
      _ = (a ^ 2 + rationalX * b ^ 2) + (c ^ 2 + rationalX * d ^ 2) := by
        rw [CharTwo.add_sq, CharTwo.add_sq]
        ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero]
  have hab := rational_square_relation (a + c) (b + d) (CharTwo.add_eq_zero.mp hz)
  exact ⟨CharTwo.add_eq_zero.mp hab.1, CharTwo.add_eq_zero.mp hab.2⟩

theorem actualDifferentialCartierCharacterization :
    Targets.ActualDifferentialCartierCharacterization.{u} := by
  intro K _ _ _ a b
  have h := actualRationalSquareRootDecomposition K (a ^ 2 + rationalX * b ^ 2)
  exact (actualRationalSquareRootUniqueness K _ _ _ _ h.symm).2

#audit_namespace LogicLineages.CartierObserverCurrent.Basic
end LogicLineages.CartierObserverCurrent.Basic
