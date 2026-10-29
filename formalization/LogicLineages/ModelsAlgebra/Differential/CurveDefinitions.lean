module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-! Literal bivariate rational-polynomial semantics for paper 15's curve
argument. The inner polynomial variable is Y and the outer variable is Z.
No ideal/kernel, irreducibility, or genericity assertion is a definition. -/

namespace LogicLineages.ModelsAlgebra.Differential

abbrev BivariatePolynomial := Polynomial (Polynomial ℚ)

variable {F : Type*} [Field F] [CharZero F]

noncomputable def pairEval (a b : F) : BivariatePolynomial →+* F :=
  Polynomial.eval₂RingHom (Polynomial.aeval a).toRingHom b

noncomputable def separant (p : BivariatePolynomial) : BivariatePolynomial :=
  Polynomial.derivative p

end LogicLineages.ModelsAlgebra.Differential
