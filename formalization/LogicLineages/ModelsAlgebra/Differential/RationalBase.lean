module

public import LogicLineages.ModelsAlgebra.Differential.Constants
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.LinearMap.Rat

@[expose] public section

/-!
# Rational linearity is derived, not assumed

An ordinary integer derivation of a characteristic-zero field has the
same additive map as a rational derivation. The rational linearity is
Mathlib's proved scalar compatibility for additive maps on rational
vector spaces, not an extra axiom of the differential field.
-/

namespace LogicLineages.ModelsAlgebra.Differential

variable {F : Type*} [Field F] [CharZero F]

def integerDerivationToRat (D : Derivation ℤ F F) : Derivation ℚ F F where
  toLinearMap := D.toLinearMap.toAddMonoidHom.toRatLinearMap
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

@[simp] theorem integerDerivationToRat_apply (D : Derivation ℤ F F) (x : F) :
    integerDerivationToRat D x = D x := rfl

/-- The actual algebraic-constants statement needs no supplied rational
linearity proof for its ordinary field derivation. -/
theorem integerDerivation_eq_zero_of_isAlgebraic (D : Derivation ℤ F F)
    {x : F} (hx : IsAlgebraic ℚ x) : D x = 0 := by
  exact derivation_eq_zero_of_isAlgebraic (integerDerivationToRat D) hx

end LogicLineages.ModelsAlgebra.Differential
