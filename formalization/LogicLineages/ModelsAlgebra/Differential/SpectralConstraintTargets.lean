module

public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraintDefinitions
public import LogicLineages.ModelsAlgebra.Differential.GenericJetsTargets

@[expose] public section

/-! Full original thm:spectral, with literal existence/all-extension
isomorphism semantics. R is the source's rational polynomial defined by its
exact raw L_i product; its existence is a proved separate construction.
Effectivity/resultant implementation remains a separate obligation. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def spectralConstraintCriterion : Prop :=
  ∀ (f : Polynomial ℚ) (root : Fin f.natDegree → f.SplittingField),
    f.Monic → 0 < f.natDegree → LinearIndependent ℚ root →
    f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i)) →
    ∀ R : MvPolynomial (Fin f.natDegree) ℚ,
      MvPolynomial.map (algebraMap ℚ f.SplittingField) R = SpectralProduct.obstruction root →
      ∀ q : MvPolynomial (Fin f.natDegree) ℚ, q ≠ 0 →
        (ConstrainedLinear.{u} f q ↔ R ∣ q)

/-- Complete source conjunction, including existence and the positive pair. -/
def spectralConstraintComplete : Prop :=
  ∀ (f : Polynomial ℚ) (root : Fin f.natDegree → f.SplittingField),
    f.Monic → 0 < f.natDegree → LinearIndependent ℚ root →
    f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i)) →
    ∃ R : MvPolynomial (Fin f.natDegree) ℚ,
      MvPolynomial.map (algebraMap ℚ f.SplittingField) R = SpectralProduct.obstruction root ∧
      R ≠ 0 ∧ ConstrainedLinear.{u} f R ∧
      ∀ q : MvPolynomial (Fin f.natDegree) ℚ, q ≠ 0 →
        (ConstrainedLinear.{u} f q ↔ R ∣ q)

end LogicLineages.ModelsAlgebra.Differential.Targets
