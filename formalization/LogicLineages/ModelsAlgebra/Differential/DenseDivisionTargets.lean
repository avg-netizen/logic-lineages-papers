module

public import LogicLineages.ModelsAlgebra.Differential.DenseDivisionDefinitions
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def denseDivisionDegreeCorrect : Prop :=
  ∀ a, DensePolynomial.isZero a = false →
    DenseDivision.degree a = (DensePolynomial.value a).natDegree ∧
    RationalCode.value (DenseDivision.leading a) = (DensePolynomial.value a).leadingCoeff

def denseDivisionRemainderCorrect : Prop :=
  ∀ a b, DensePolynomial.value (DenseDivision.remainder b a) =
    DensePolynomial.value a % DensePolynomial.value b

def denseDivisionTestCorrect : Prop :=
  ∀ a b, DenseDivision.divides b a = true ↔ DensePolynomial.value b ∣ DensePolynomial.value a

def denseDivisionPrimitiveRecursive : Prop :=
  Primrec DenseDivision.degree ∧ Primrec DenseDivision.leading ∧ Primrec₂ DenseDivision.shift ∧
  Primrec (fun t : DensePolynomial.Code × ℕ × DensePolynomial.Code =>
    DenseDivision.step t.1 t.2.1 t.2.2) ∧ Primrec₂ DenseDivision.remainder ∧
  Primrec₂ DenseDivision.divides

end LogicLineages.ModelsAlgebra.Differential.Targets
