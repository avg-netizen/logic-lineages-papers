module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJetDefinitions
public import LogicLineages.ModelsAlgebra.Differential.SpectralProductDefinitions
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

/-! Full two-conclusion comparator for paper 15 lem:genericjets. The source
roots enumerate the actual monic polynomial in its actual splitting field;
R is calibrated to the literal unnormalized L_i product, the source definition
of R_f. Existence of this rational R is proved in SpectralDescent, rather than
being an assumed mathematical supplier. No spectral-coordinate nonvanishing,
jet independence, field closure or isomorphism is an input premise. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def spectralGenericJets : Prop :=
  ∀ (f : Polynomial ℚ) (root : Fin f.natDegree → f.SplittingField),
    f.Monic → 0 < f.natDegree → LinearIndependent ℚ root →
    f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i)) →
    ∀ R : MvPolynomial (Fin f.natDegree) ℚ,
      MvPolynomial.map (algebraMap ℚ f.SplittingField) R = SpectralProduct.obstruction root →
      (∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F) (a : F),
        jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation f) = 0 →
        MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a f.natDegree) R ≠ 0 →
        AlgebraicIndependent ℚ (FiniteJet.family (integerDerivationToRat D) a f.natDegree)) ∧
      (∀ (F : Type u) (H : Type v) [Field F] [CharZero F] [Field H] [CharZero H]
        (D : Derivation ℤ F F) (E : Derivation ℤ H H) (a : F) (b : H),
        jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation f) = 0 →
        MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a f.natDegree) R ≠ 0 →
        jetEval (integerDerivationToRat E) b (LinearOperator.linearEquation f) = 0 →
        MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat E) b f.natDegree) R ≠ 0 →
        HasDesignatedRootIso D E a b)

end LogicLineages.ModelsAlgebra.Differential.Targets
