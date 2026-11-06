module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalOrientedBezout
open OrdinaryArithmetic (succTerm zeroTerm)
def ActualSignedConversion : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b x y z w : OTerm α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    (InternalLinearCombination.equation (succTerm a) (succTerm b) (succTerm zeroTerm) x y z w)).imp
    (arithmeticEmbedding.onFormula (InternalBezoutCRT.certificate (succTerm a) b
      (leftCoefficient b x z w) (rightCoefficient a x y w)))))
def ActualOrientedBezoutFromCoprimality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b : OTerm α),
  Nonempty (Derivation body [] ((InternalBezoutExistenceTargets.coprime (succTerm a) (succTerm b)).imp
    (arithmeticEmbedding.onFormula (oriented a b))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutTargets
