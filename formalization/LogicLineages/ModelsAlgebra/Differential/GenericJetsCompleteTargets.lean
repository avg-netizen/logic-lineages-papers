module

public import LogicLineages.ModelsAlgebra.Differential.GenericJetsTargets

@[expose] public section

/-! Full source lemma together with the actual construction of its rational
obstruction. R_f existence is a proved existential conclusion here, and both
original generic-jets conclusions are included. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def spectralGenericJetsComplete : Prop :=
  ∀ (f : Polynomial ℚ) (root : Fin f.natDegree → f.SplittingField),
    f.Monic → 0 < f.natDegree → LinearIndependent ℚ root →
    f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i)) →
    ∃ R : MvPolynomial (Fin f.natDegree) ℚ,
      MvPolynomial.map (algebraMap ℚ f.SplittingField) R = SpectralProduct.obstruction root ∧ R ≠ 0 ∧
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
