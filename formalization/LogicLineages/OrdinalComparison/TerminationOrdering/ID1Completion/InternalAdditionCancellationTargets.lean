module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus

def ActualAdditionCommutativity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.addTerm s t).equal (OrdinaryArithmetic.addTerm t s))))

def ActualAdditionLeftCancellation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (((OrdinaryArithmetic.addTerm u s).equal (OrdinaryArithmetic.addTerm u t)).imp (s.equal t))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationTargets
