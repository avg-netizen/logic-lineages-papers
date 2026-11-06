module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
/-- Literal embedded multiplication commutativity in the original PA calculus. -/
def ActualMultiplicationCommutativity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.mulTerm s t).equal (OrdinaryArithmetic.mulTerm t s))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityTargets
