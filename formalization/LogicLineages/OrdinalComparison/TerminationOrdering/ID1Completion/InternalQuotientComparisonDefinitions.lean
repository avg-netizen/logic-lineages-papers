module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparison
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
def comparison {α : Type} (s t : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t) ⊔
    (arithmeticEmbedding.onFormula (s.equal t) ⊔
      arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula t s))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparison
