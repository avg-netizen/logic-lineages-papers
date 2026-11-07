module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
/-- Disjunction is the existing classical first-order connective. -/
theorem supInstantiate {α : Type} (p q : Formula (α ⊕ Fin 1)) (t : Term α) :
    instantiate (p ⊔ q) t = instantiate p t ⊔ instantiate q t := rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
