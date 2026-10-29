module

public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! The actual monic squarefree radical of a rational polynomial: normalize
the standard UFD product of its distinct normalized irreducible factors.
No root-vanishing criterion is built into this definition. -/

namespace LogicLineages.ModelsAlgebra.Differential

noncomputable def rationalRadical (r : Polynomial ℚ) : Polynomial ℚ :=
  normalize (UniqueFactorizationMonoid.radical r)

end LogicLineages.ModelsAlgebra.Differential
