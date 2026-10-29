module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.FieldTheory.Minpoly.Field

@[expose] public section

/-!
# The algebraic-constants lemma by the minimal degree

This implements exactly the same algebraic-constants statement as
`Constants.lean`. The derivative of the minimal polynomial is nonzero
in characteristic zero and has smaller degree, so it cannot itself
vanish at the element. This proves the particular separability fact
needed here without taking a separability or derivative-nonvanishing
supplier as a premise. The original candidate is preserved separately.
-/

namespace LogicLineages.ModelsAlgebra.Differential.MinpolyDegree

open Polynomial

variable {K : Type*} {F : Type*}
variable [Field K] [CharZero K] [Field F] [Algebra K F]

theorem derivation_eq_zero_of_isAlgebraic (D : Derivation K F F)
    {x : F} (hx : IsAlgebraic K x) : D x = 0 := by
  have hdegree : (minpoly K x).natDegree ≠ 0 :=
    (minpoly.natDegree_pos hx.isIntegral).ne'
  have hderivative : derivative (minpoly K x) ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hdegree
  have hne : aeval x (derivative (minpoly K x)) ≠ (0 : F) := by
    intro hz
    exact (Polynomial.not_dvd_of_natDegree_lt hderivative
      (Polynomial.natDegree_derivative_lt hdegree)) (minpoly.dvd K x hz)
  have hprod : aeval x (derivative (minpoly K x)) * D x = (0 : F) := by
    simpa only [smul_eq_mul, minpoly.aeval, map_zero] using
      (D.map_aeval (minpoly K x) x).symm
  exact (mul_eq_zero.mp hprod).resolve_left hne

theorem transcendental_of_derivation_ne_zero (D : Derivation K F F)
    {x : F} (hx : D x ≠ 0) : Transcendental K x := by
  exact fun halg => hx (derivation_eq_zero_of_isAlgebraic D halg)

end LogicLineages.ModelsAlgebra.Differential.MinpolyDegree
