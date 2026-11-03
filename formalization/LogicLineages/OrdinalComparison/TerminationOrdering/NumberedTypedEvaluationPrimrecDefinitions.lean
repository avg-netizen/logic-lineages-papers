module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestPresentationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrec
open NumberedTypedRequests

abbrev State (n : Nat) := Option (List (Request n))

/-- One literal request expansion; failure and completed work are absorbing. -/
def step {n : Nat} (arity : Fin n → Nat) : State n → State n
  | none => none
  | some [] => some []
  | some (request :: rest) =>
    (expand arity request).map (fun children => children ++ rest)

/-- Exactly the supplied number of one-layer worklist transitions. -/
def run {n : Nat} (arity : Fin n → Nat) (fuel : Nat) (requests : List (Request n)) : State n :=
  (step arity)^[fuel] (some requests)

/-- Only completed successful work returns true; exhausted pending work fails. -/
def done {n : Nat} : State n → Bool
  | some [] => true
  | _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrec
