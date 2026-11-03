module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequests
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedFiniteUniverse
open NumberedNumericCarrier NumberedTypedRequests

/-- The original finite-universe conditions contributed by this request's root. -/
def guard {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty) :
    Request n → Bool
  | .term _ tau (.lam sigma _) => decide (tau ∈ S) && decide (sigma ∈ S)
  | .term _ tau (.ordinary head _) =>
    decide (tau ∈ S) && decide (HeadInWindow arity symbols S (decodeHead head))
  | .term _ tau (.numbered _ head _ _ _ _) =>
    decide (tau ∈ S) && decide (HeadInWindow arity symbols S (decodeHead head))
  | .term _ tau _ => decide (tau ∈ S)
  | .arguments _ _ _ => true

/-- Successful original typed decoding followed by the original universe test. -/
def valid {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty) :
    Request n → Bool
  | .term Gamma tau code =>
    (decodeTerm arity Gamma tau code).any (universeTest symbols S)
  | .arguments Gamma types code =>
    (decodeArguments arity Gamma types code).any (argumentsUniverseTest symbols S)

/-- The local universe guard and the original typed expander's ordered children. -/
def expandedValid {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (request : Request n) : Bool :=
  guard arity symbols S request &&
    (NumberedTypedRequests.expand arity request).any
      (fun children => children.all (valid arity symbols S))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequests
