module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsTargets
open Source NumberedAuxiliaryCoding NumberedTypedRequests

/-- Exact one-layer universe validation for every original typed term request. -/
def ActualTermExpansion : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (tau : Ty) (code : Code (Fin n)),
    NumberedUniverseRequests.valid arity symbols S (.term Gamma tau code) =
      NumberedUniverseRequests.expandedValid arity symbols S (.term Gamma tau code)

/-- Exact one-layer universe validation for every original typed argument request. -/
def ActualArgumentsExpansion : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma types : List Ty)
    (code : Code (Fin n)),
    NumberedUniverseRequests.valid arity symbols S (.arguments Gamma types code) =
      NumberedUniverseRequests.expandedValid arity symbols S (.arguments Gamma types code)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsTargets
