module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJetDefinitions
public import LogicLineages.ModelsAlgebra.Differential.LinearOperatorDefinitions

@[expose] public section

/-! Direct source-calibrated monic-equation/recurrence bridge in paper 15
lem:genericjets. The full isomorphism conclusion below assumes only the
actual common monic equation and actual finite-jet algebraic independence;
there is no field-closure or isomorphism supplier premise. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def monicOperatorRecurrence : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℚ F F)
    (p : Polynomial ℚ) (a : F), p.Monic →
    (LinearOperator.applyOperator D p a = 0 ↔
      FiniteJet.Recurrence D a p.natDegree (fun k => -p.coeff k.val))

def independentMonicSolutionIsomorphism : Prop :=
  ∀ (F : Type u) (H : Type v) [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H)
    (p : Polynomial ℚ) (a : F) (b : H), p.Monic → 0 < p.natDegree →
    jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation p) = 0 →
    jetEval (integerDerivationToRat E) b (LinearOperator.linearEquation p) = 0 →
    AlgebraicIndependent ℚ (FiniteJet.family (integerDerivationToRat D) a p.natDegree) →
    AlgebraicIndependent ℚ (FiniteJet.family (integerDerivationToRat E) b p.natDegree) →
    HasDesignatedRootIso D E a b

end LogicLineages.ModelsAlgebra.Differential.Targets
