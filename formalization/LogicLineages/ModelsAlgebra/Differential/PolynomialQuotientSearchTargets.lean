module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearchDefinitions
public import Mathlib.Algebra.Polynomial.Degree.Definitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

open PolynomialQuotientSearch

def polynomialQuotientAtIndexPrimitiveRecursive : Prop := Primrec₂ atIndex

def polynomialQuotientSearchCorrect : Prop :=
  ∀ (b a : DensePolynomial.Code) (w : Certificate), w ∈ search (b, a) →
    DensePolynomial.value a = DensePolynomial.value b * DensePolynomial.value w.1 +
      DensePolynomial.value w.2 ∧
    (DensePolynomial.value b ≠ 0 →
      DensePolynomial.value w.2 = 0 ∨
        (DensePolynomial.value w.2).natDegree < (DensePolynomial.value b).natDegree) ∧
    (DensePolynomial.isZero w.2 = true ↔ DensePolynomial.value b ∣ DensePolynomial.value a)

def polynomialQuotientSearchTotal : Prop := ∀ t : Input, (search t).Dom

def polynomialQuotientSearchPartialRecursive : Prop := Partrec search

def polynomialQuotientComputableRealization : Prop :=
  ∃ f : Input → Certificate, Computable f ∧
    (∀ t, f t ∈ search t) ∧
    ∀ b a,
      DensePolynomial.value a = DensePolynomial.value b * DensePolynomial.value (f (b, a)).1 +
        DensePolynomial.value (f (b, a)).2 ∧
      (DensePolynomial.value b ≠ 0 →
        DensePolynomial.value (f (b, a)).2 = 0 ∨
          (DensePolynomial.value (f (b, a)).2).natDegree < (DensePolynomial.value b).natDegree) ∧
      (DensePolynomial.isZero (f (b, a)).2 = true ↔
        DensePolynomial.value b ∣ DensePolynomial.value a)

end LogicLineages.ModelsAlgebra.Differential.Targets
