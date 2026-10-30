module
public import LogicLineages.OrdinalComparison.CartierRationalTargets
public import LogicLineages.OrdinalComparison.CartierPolynomialProof
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualRationalSquareRootDecomposition : Targets.ActualRationalSquareRootDecomposition.{u} := by
  intro K _ _ _ f
  let E := algebraMap (Polynomial K) (RatFunc K)
  have hden : E f.denom ≠ 0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := congrArg E (actualPolynomialSquareRootDecomposition K (f.num * f.denom))
  simp only [map_mul, map_add, map_pow, RatFunc.algebraMap_X] at h
  change f = (E (actualPolynomialSquareRootDigit false (f.num * f.denom)) / E f.denom) ^ 2 +
    RatFunc.X * (E (actualPolynomialSquareRootDigit true (f.num * f.denom)) / E f.denom) ^ 2
  calc
    f = E f.num / E f.denom := (RatFunc.num_div_denom f).symm
    _ = (E f.num * E f.denom) / (E f.denom) ^ 2 := by field_simp
    _ = _ := by rw [h]; dsimp [E]; field_simp

private theorem rational_square_relation {K : Type*} [Field K] [CharP K 2]
    (a b : RatFunc K) (h : a ^ 2 = RatFunc.X * b ^ 2) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · simp only [hb, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    exact ⟨eq_zero_of_pow_eq_zero h, hb⟩
  · have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_pow (by decide : 2 ≠ 0)] at h
      exact (mul_ne_zero RatFunc.X_ne_zero (pow_ne_zero _ hb)) h.symm
    have hd := congrArg RatFunc.intDegree h
    simp only [pow_two, RatFunc.intDegree_mul ha ha,
      RatFunc.intDegree_mul RatFunc.X_ne_zero (mul_ne_zero hb hb),
      RatFunc.intDegree_mul hb hb, RatFunc.intDegree_X] at hd
    omega

theorem actualRationalSquareRootUniqueness : Targets.ActualRationalSquareRootUniqueness.{u} := by
  intro K _ _ _ a b c d h
  have hz : (a + c) ^ 2 + RatFunc.X * (b + d) ^ 2 = 0 := by
    calc
      _ = (a ^ 2 + RatFunc.X * b ^ 2) + (c ^ 2 + RatFunc.X * d ^ 2) := by
        rw [CharTwo.add_sq, CharTwo.add_sq]
        ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero]
  have hab := rational_square_relation (a + c) (b + d) (CharTwo.add_eq_zero.mp hz)
  exact ⟨CharTwo.add_eq_zero.mp hab.1, CharTwo.add_eq_zero.mp hab.2⟩

theorem actualDifferentialCartierCharacterization :
    Targets.ActualDifferentialCartierCharacterization.{u} := by
  intro K _ _ _ a b
  have h := actualRationalSquareRootDecomposition K (a ^ 2 + RatFunc.X * b ^ 2)
  exact (actualRationalSquareRootUniqueness K _ _ _ _ h.symm).2

end LogicLineages.OrdinalComparison
