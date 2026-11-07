module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGround
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof

/-- The existing scalar predicate with the original even tag, unchanged. -/
def literalGround {α : Type} (x : OrdinaryArithmetic.Term α) : language.Formula α :=
  (Positive.predicate (tagTerm false x)).formula

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGround
