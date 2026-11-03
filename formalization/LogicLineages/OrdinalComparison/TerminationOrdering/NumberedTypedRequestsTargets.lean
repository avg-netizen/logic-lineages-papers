module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedTypedRequests

def ActualTermExpansion : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) (code : Code (Fin n)),
  (decodeTerm arity Gamma tau code).isSome = expandedValid arity (.term Gamma tau code)

def ActualArgumentsExpansion : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty) (code : Code (Fin n)),
  (decodeArguments arity Gamma types code).isSome = expandedValid arity (.arguments Gamma types code)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsTargets
