module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-! The literal source polynomial in paper 15 prop:cyclotomic, rather than
a larger general cyclotomic-polynomial construction. -/
namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily

noncomputable def geometric (R : Type*) [Semiring R] (ℓ : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range ℓ, Polynomial.X ^ k

noncomputable def polynomial (ℓ : ℕ) : Polynomial ℚ := geometric ℚ ℓ

end LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
