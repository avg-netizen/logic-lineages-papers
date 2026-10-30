module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJetDefinitions
public import LogicLineages.ModelsAlgebra.Differential.LinearOperatorDefinitions

@[expose] public section

/-! Literal source constrainedness for a rational monic linear differential
equation. Existence and universal designated-root differential isomorphism
are the original two semantic clauses; the predicate contains no divisibility,
spectral promise, coordinate condition or preferred model. -/
namespace LogicLineages.ModelsAlgebra.Differential

universe u

def ConstrainedLinear (f : Polynomial ℚ) (q : MvPolynomial (Fin f.natDegree) ℚ) : Prop :=
  (∃ (F : Type u) (fieldF : Field F),
    letI : Field F := fieldF
    ∃ charF : CharZero F,
      letI : CharZero F := charF
      ∃ (D : Derivation ℤ F F) (a : F),
        jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation f) = 0 ∧
        MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a f.natDegree) q ≠ 0) ∧
  (∀ (F H : Type u) [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H) (a : F) (b : H),
    jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation f) = 0 →
    MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a f.natDegree) q ≠ 0 →
    jetEval (integerDerivationToRat E) b (LinearOperator.linearEquation f) = 0 →
    MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat E) b f.natDegree) q ≠ 0 →
    HasDesignatedRootIso D E a b)

end LogicLineages.ModelsAlgebra.Differential
