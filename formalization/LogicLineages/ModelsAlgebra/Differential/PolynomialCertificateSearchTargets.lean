module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchDefinitions
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

open DensePolynomial PolynomialCertificateSearch

def polynomialCodeDegreeCorrect : Prop :=
  ∀ a, PolynomialCertificateSearch.degree a = (DensePolynomial.value a).natDegree

def polynomialCertificateVerifierCorrect : Prop :=
  ∀ b a w, verify b a w = true ↔
    value a = value b * value w.1 + value w.2 ∧
    (value w.2 = 0 ∨ (value w.2).natDegree < (value b).natDegree)

def polynomialCertificateExists : Prop :=
  ∀ b a, value b ≠ 0 → ∃ w, verify b a w = true

def polynomialSearchAnswerCorrect : Prop :=
  ∀ (b a : DensePolynomial.Code) (answer : Bool),
    answer ∈ search (b, a) → (answer = true ↔ value b ∣ value a)

def polynomialSearchTotal : Prop := ∀ t : Input, (search t).Dom

def polynomialSearchFinitePrimitiveRecursive : Prop :=
  Primrec PolynomialCertificateSearch.degree ∧ Primrec₂ PolynomialCertificateSearch.equal ∧
  Primrec (fun t : Input × Certificate => verify t.1.1 t.1.2 t.2) ∧ Primrec₂ atIndex

def polynomialSearchPartialRecursive : Prop := Partrec search

end LogicLineages.ModelsAlgebra.Differential.Targets
