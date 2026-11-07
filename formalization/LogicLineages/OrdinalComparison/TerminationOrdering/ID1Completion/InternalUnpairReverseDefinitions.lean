module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverse
open FirstOrder Language PositiveArithmeticOperators InternalCalculus

/-- Both ordinary weak bounds, written with the unchanged original strict-order formula. -/
def coordinateBounds {α : Type} (n x y : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula x (OrdinaryArithmetic.succTerm n)) ⊓
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula y (OrdinaryArithmetic.succTerm n))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverse
