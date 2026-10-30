module

public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraintDefinitions
public import LogicLineages.ModelsAlgebra.Differential.CyclotomicFamilyDefinitions
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

/-! Direct original prop:cyclotomic targets from paper 15. f is literally
1+T+...+T^(ell-1). Root independence, full actual splitting-field factorization,
and unbounded differential orders are conclusions, not supplier premises.
The semantic all-q family does NOT claim an effective decision algorithm;
that original effective consequence remains separately pending. The unfrozen
old generic-cyclotomic target/import snapshot is preserved in drafts after
two actual import RSS stops, without any resource-limit increase. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def cyclotomicGeometricCoefficients : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (ℓ : ℕ), 0 < ℓ →
    (∀ k : ℕ, (CyclotomicFamily.geometric R ℓ).coeff k = if k < ℓ then 1 else 0) ∧
    (CyclotomicFamily.geometric R ℓ).Monic ∧
    (CyclotomicFamily.geometric R ℓ).natDegree = ℓ - 1

def cyclotomicPrimeIrreducible : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → Irreducible (CyclotomicFamily.polynomial ℓ)

def cyclotomicPrimeSpectralPromise : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime →
    let f := CyclotomicFamily.polynomial ℓ
    f.Monic ∧ f.natDegree = ℓ - 1 ∧ 0 < f.natDegree ∧
    ∃ root : Fin f.natDegree → f.SplittingField,
      LinearIndependent ℚ root ∧
      f.map (algebraMap ℚ f.SplittingField) =
        ∏ i : Fin f.natDegree, ((Polynomial.X : Polynomial f.SplittingField) - Polynomial.C (root i))

def cyclotomicOrdersUnbounded : Prop :=
  ∀ N : ℕ, ∃ ℓ : ℕ, ℓ.Prime ∧ N < (CyclotomicFamily.polynomial ℓ).natDegree

def cyclotomicSemanticFamily : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime →
    let f := CyclotomicFamily.polynomial ℓ
    ∃ R : MvPolynomial (Fin f.natDegree) ℚ,
      R ≠ 0 ∧ ConstrainedLinear.{u} f R ∧
      ∀ q : MvPolynomial (Fin f.natDegree) ℚ, q ≠ 0 →
        (ConstrainedLinear.{u} f q ↔ R ∣ q)

end LogicLineages.ModelsAlgebra.Differential.Targets
