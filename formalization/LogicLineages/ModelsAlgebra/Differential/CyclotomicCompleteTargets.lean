module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicAlgorithmDefinitions
public import LogicLineages.ModelsAlgebra.Differential.CyclotomicFamilyTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def cyclotomicCoefficientCode : Prop := ∀ ℓ,
  DensePolynomial.value (CyclotomicAlgorithm.coefficients ℓ) = CyclotomicFamily.polynomial ℓ

def cyclotomicAlgorithmTotal : Prop := ∀ t : CyclotomicAlgorithm.Input,
  (CyclotomicAlgorithm.search t).Dom

def cyclotomicAlgorithmPartialRecursive : Prop := Partrec CyclotomicAlgorithm.search

def cyclotomicInputCoverage : Prop := ∀ ℓ
    (q : MvPolynomial (Fin (CyclotomicFamily.polynomial ℓ).natDegree) ℚ),
  ∃ B qc, 2 ≤ B ∧ BoxPolynomialCode.value (CyclotomicFamily.polynomial ℓ).natDegree B qc = q

def cyclotomicEffectiveFamily : Prop :=
  ∃ d : CyclotomicAlgorithm.Input → Bool, Computable d ∧
    (∀ t, d t ∈ CyclotomicAlgorithm.search t) ∧
    ∀ ℓ, ℓ.Prime → ∀ B, 2 ≤ B → ∀ qc : DensePolynomial.Code,
      BoxPolynomialCode.value (CyclotomicFamily.polynomial ℓ).natDegree B qc ≠ 0 →
      (d (ℓ, B, qc) = true ↔ ConstrainedLinear.{u} (CyclotomicFamily.polynomial ℓ)
        (BoxPolynomialCode.value (CyclotomicFamily.polynomial ℓ).natDegree B qc))

/-- Every clause of the original proposition, including genuine UNIFORM
decisions on all finite rational lower-order inputs, with full coverage. -/
def cyclotomicFullSource : Prop :=
  cyclotomicPrimeIrreducible ∧ cyclotomicPrimeSpectralPromise ∧ cyclotomicOrdersUnbounded ∧
    cyclotomicSemanticFamily.{u} ∧ cyclotomicInputCoverage ∧ cyclotomicEffectiveFamily.{u}

end LogicLineages.ModelsAlgebra.Differential.Targets
