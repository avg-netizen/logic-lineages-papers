module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecTargets
open NumberedTypedRequests NumberedRequestPresentation

/-- Formal primitive recursion of the original one-step request expansion. -/
def ActualRequestExpansionPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (NumberedTypedRequests.expand arity : Request n → Option (List (Request n)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecTargets
