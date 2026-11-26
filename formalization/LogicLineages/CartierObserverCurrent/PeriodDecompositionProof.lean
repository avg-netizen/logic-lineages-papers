module
public import LogicLineages.CartierObserverCurrent.PeriodDecompositionTargets
public import LogicLineages.CartierObserverCurrent.BasicPolynomialProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodDecomposition
open Basic

theorem actualDecomposition : Targets.ActualRationalSquareRootDecomposition.{u} := by
  intro K _ _ _ f
  let E := algebraMap (Polynomial K) (RatFunc K)
  have hden : E f.denom ≠ 0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := congrArg E (Basic.actualPolynomialSquareRootDecomposition K (f.num * f.denom))
  simp only [map_mul, map_add, map_pow] at h
  change f = (E (actualPolynomialSquareRootDigit false (f.num * f.denom)) / E f.denom) ^ 2 +
    rationalX * (E (actualPolynomialSquareRootDigit true (f.num * f.denom)) / E f.denom) ^ 2
  rw [div_pow, div_pow, ← mul_div_assoc, ← add_div, ← h, pow_two,
    mul_div_mul_right _ _ hden]
  exact f.num_div_denom.symm

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodDecomposition
end LogicLineages.CartierObserverCurrent.PeriodDecomposition
