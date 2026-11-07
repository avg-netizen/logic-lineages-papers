module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalQuotientComparison
def ActualOriginalComparison : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (comparison s t))
def ActualRightSuccessorOrder : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t)).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s (OrdinaryArithmetic.succTerm t)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonTargets
