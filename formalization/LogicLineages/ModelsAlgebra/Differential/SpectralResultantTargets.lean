module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def spectralGeneratingDegree : Prop :=
  ∀ n (f : Polynomial ℚ), (SpectralResultant.generating n f).natDegree ≤ n - 1

def spectralGeneratingRootCalibration : Prop :=
  ∀ (K : Type*) [Field K] [Algebra ℚ K] (n : ℕ) (f : Polynomial ℚ)
    (root : Fin n → K), f.natDegree = n →
    f.map (algebraMap ℚ K) = ∏ i : Fin n, (Polynomial.X - Polynomial.C (root i)) →
    ∀ i : Fin n,
      SpectralResultant.atRoot n f (root i) =
        SpectralProduct.linearForm n (SpectralProduct.rawPolynomial root i)

def spectralResultantCalibration : Prop :=
  ∀ (K : Type*) [Field K] [Algebra ℚ K] (n : ℕ) (f : Polynomial ℚ)
    (root : Fin n → K), f.Monic → f.natDegree = n →
    f.map (algebraMap ℚ K) = ∏ i : Fin n, (Polynomial.X - Polynomial.C (root i)) →
    MvPolynomial.map (algebraMap ℚ K) (SpectralResultant.obstruction n f) =
      SpectralProduct.obstruction root

def spectralResultantBox : Prop :=
  ∀ (K : Type*) [Field K] [Algebra ℚ K] (n : ℕ) (f : Polynomial ℚ)
    (root : Fin n → K), 0 < n → f.Monic → f.natDegree = n →
    f.map (algebraMap ℚ K) = ∏ i : Fin n, (Polynomial.X - Polynomial.C (root i)) →
    KroneckerPolynomial.Box (n + 1) (SpectralResultant.obstruction n f)

end LogicLineages.ModelsAlgebra.Differential.Targets
