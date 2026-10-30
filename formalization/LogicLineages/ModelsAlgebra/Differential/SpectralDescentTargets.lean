module

public import LogicLineages.ModelsAlgebra.Differential.SpectralProductDefinitions
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

/-! Literal rational-coefficient descent in paper 15 immediately before
thm:spectral. The base is the actual splitting field of the rational source
polynomial. The roots enumerate its monic factorization and are distinct;
no Galois-invariance/descent correctness supplier is an input premise. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

def spectralObstructionRationalDescent : Prop :=
  ∀ (f : Polynomial ℚ) (n : ℕ) (root : Fin n → f.SplittingField),
    f.Monic → Function.Injective root →
    f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (root i)) →
    ∃ R : MvPolynomial (Fin n) ℚ,
      MvPolynomial.map (algebraMap ℚ f.SplittingField) R =
        SpectralProduct.obstruction root ∧ R ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
