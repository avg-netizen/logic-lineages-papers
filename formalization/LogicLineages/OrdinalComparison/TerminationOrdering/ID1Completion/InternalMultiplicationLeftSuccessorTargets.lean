module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
/-- The original embedded arithmetic equality, with no semantic reflection premise. -/
def ActualMultiplicationLeftSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.mulTerm (OrdinaryArithmetic.succTerm s) t).equal
      (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm s t) t))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorTargets
