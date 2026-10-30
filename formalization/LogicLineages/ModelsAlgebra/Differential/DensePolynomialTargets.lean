module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialDefinitions
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def densePolynomialCoverage : Prop :=
  ∀ p : Polynomial ℚ, ∃ c : DensePolynomial.Code, DensePolynomial.value c = p

def densePolynomialCoefficients : Prop :=
  ∀ (c : DensePolynomial.Code) (i : ℕ),
    (DensePolynomial.value c).coeff i = RationalCode.value (c.getD i RationalCode.zero)

def densePolynomialArithmeticCorrect : Prop :=
  (∀ a b, DensePolynomial.value (DensePolynomial.add a b) =
    DensePolynomial.value a + DensePolynomial.value b) ∧
  (∀ a, DensePolynomial.value (DensePolynomial.neg a) = -DensePolynomial.value a) ∧
  (∀ a b, DensePolynomial.value (DensePolynomial.scale a b) =
    Polynomial.C (RationalCode.value a) * DensePolynomial.value b) ∧
  (∀ a b, DensePolynomial.value (DensePolynomial.mul a b) =
    DensePolynomial.value a * DensePolynomial.value b) ∧
  (∀ a n, DensePolynomial.value (DensePolynomial.power a n) = (DensePolynomial.value a)^n) ∧
  (∀ a, DensePolynomial.value (DensePolynomial.derivative a) =
    (DensePolynomial.value a).derivative) ∧
  (∀ a, DensePolynomial.isZero a = true ↔ DensePolynomial.value a = 0)

def densePolynomialArithmeticPrimitiveRecursive : Prop :=
  Primrec₂ DensePolynomial.add ∧ Primrec DensePolynomial.neg ∧
  Primrec₂ DensePolynomial.scale ∧ Primrec₂ DensePolynomial.mul ∧
  Primrec₂ DensePolynomial.power ∧ Primrec DensePolynomial.derivative ∧
  Primrec DensePolynomial.isZero

end LogicLineages.ModelsAlgebra.Differential.Targets
