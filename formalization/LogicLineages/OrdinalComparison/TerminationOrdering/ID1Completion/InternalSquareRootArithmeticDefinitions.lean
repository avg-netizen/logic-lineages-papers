module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmetic
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
abbrev square {α : Type} (s : OrdinaryArithmetic.Term α) : OrdinaryArithmetic.Term α :=
  OrdinaryArithmetic.mulTerm s s
/-- Literal arithmetic square interval. The weak lower bound is a strict
bound against the successor; no new object-language relation is introduced. -/
def interval {α : Type} (s n : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula (square s) (OrdinaryArithmetic.succTerm n)) ⊓
    arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula n (square (OrdinaryArithmetic.succTerm s)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmetic
