module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluation
open NumberedTypedRequests

/-- A literal bounded traversal of the pending decoder requests. Each successful
expansion consumes one unit of fuel; exhausted nonempty work and failed local
checks return false. The empty worklist succeeds even at zero fuel. -/
def evaluate {n : Nat} (arity : Fin n → Nat) : Nat → List (Request n) → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, request :: rest =>
    match expand arity request with
    | none => false
    | some children => evaluate arity fuel (children ++ rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluation
