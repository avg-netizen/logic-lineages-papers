module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecTargets
open Source NumberedTypedRequests

/-- Primitive recursion of the literal local universe guard on every original request. -/
def ActualGuardPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : (List (Fin n) × List Ty) × Request n =>
    NumberedUniverseRequests.guard arity p.1.1 p.1.2 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecTargets
