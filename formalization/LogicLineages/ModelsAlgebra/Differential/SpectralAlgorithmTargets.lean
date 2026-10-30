module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def spectralAlgorithmInputCoverage : Prop := ∀ (f : Polynomial ℚ)
    (q : MvPolynomial (Fin f.natDegree) ℚ),
  ∃ (fc : DensePolynomial.Code) (B : ℕ) (qc : DensePolynomial.Code),
    2 ≤ B ∧ ∃ h : SpectralAlgorithm.equation (fc, B, qc) = f,
      h ▸ SpectralAlgorithm.lowerPolynomial (fc, B, qc) = q

def spectralAlgorithmOrder : Prop := ∀ t : SpectralAlgorithm.Input,
  SpectralAlgorithm.order t = (SpectralAlgorithm.equation t).natDegree

def spectralAlgorithmSearchCorrect : Prop := ∀ t answer,
  SpectralAlgorithm.SourcePromise t → answer ∈ SpectralAlgorithm.search t →
    (answer = true ↔ SpectralAlgorithm.InputConstrained.{u} t)

def spectralAlgorithmSearchTotal : Prop := ∀ t : SpectralAlgorithm.Input,
  (SpectralAlgorithm.search t).Dom

def spectralAlgorithmSearchPartialRecursive : Prop := Partrec SpectralAlgorithm.search

def spectralAlgorithmComputableRealization : Prop :=
  ∃ f : SpectralAlgorithm.Input → Bool, Computable f ∧
    (∀ t, f t ∈ SpectralAlgorithm.search t) ∧
    ∀ t, SpectralAlgorithm.SourcePromise t →
      (f t = true ↔ SpectralAlgorithm.InputConstrained.{u} t)

end LogicLineages.ModelsAlgebra.Differential.Targets
