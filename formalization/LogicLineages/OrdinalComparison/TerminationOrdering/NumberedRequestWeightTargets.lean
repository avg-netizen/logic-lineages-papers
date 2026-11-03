module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightTargets
open NumberedTypedRequests NumberedRequestWeight

def SuccessfulExpansionDecrease : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (request : Request n) (children : List (Request n)), expand arity request = some children → workWeight children < requestWeight request

def WorklistReplacementDecrease : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (request : Request n) (children rest : List (Request n)), expand arity request = some children → workWeight (children ++ rest) < workWeight (request :: rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightTargets
