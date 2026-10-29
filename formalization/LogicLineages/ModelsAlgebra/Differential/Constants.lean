module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# Algebraic elements are constants in characteristic zero

This is the full statement of Lemma `lem:constants` in paper 15,
generalized from the rational base to an arbitrary characteristic-zero
field. A derivation over the base is part of the differential-extension
input; separability of the minimal polynomial is proved by Mathlib.
There is no supplied zero-derivative or separability hypothesis.
-/

namespace LogicLineages.ModelsAlgebra.Differential

open Polynomial

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A base-linear derivation vanishes at every element algebraic over
a characteristic-zero base field. -/
theorem derivation_eq_zero_of_isAlgebraic (D : Derivation K F F)
    {x : F} (hx : IsAlgebraic K x) : D x = 0 := by
  have hsep : (minpoly K x).Separable :=
    (minpoly.irreducible hx.isIntegral).separable
  have hne : aeval x (derivative (minpoly K x)) ≠ (0 : F) :=
    hsep.aeval_derivative_ne_zero (minpoly.aeval K x)
  have hprod : aeval x (derivative (minpoly K x)) * D x = (0 : F) := by
    simpa only [smul_eq_mul, minpoly.aeval, map_zero] using
      (D.map_aeval (minpoly K x) x).symm
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- The contrapositive used for nonconstant solutions of first-order
differential equations. -/
theorem transcendental_of_derivation_ne_zero (D : Derivation K F F)
    {x : F} (hx : D x ≠ 0) : Transcendental K x := by
  exact fun halg => hx (derivation_eq_zero_of_isAlgebraic D halg)

end LogicLineages.ModelsAlgebra.Differential
