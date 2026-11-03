module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestPresentationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluation
open Source NumberedTypedRequests

/-- Bounded traversal of the original typed requests, with the original universe
conditions checked at each root before the unchanged typed expansion. -/
def evaluate {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty) :
    Nat → List (Request n) → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, request :: rest =>
    bif NumberedUniverseRequests.guard arity symbols S request then
      match expand arity request with
      | none => false
      | some children => evaluate arity symbols S fuel (children ++ rest)
    else false

abbrev State (n : Nat) := Option (List (Request n))

/-- One guarded actual request expansion; failure and completion are absorbing. -/
def step {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty) :
    State n → State n
  | none => none
  | some [] => some []
  | some (request :: rest) =>
    bif NumberedUniverseRequests.guard arity symbols S request then
      (expand arity request).map (fun children => children ++ rest)
    else none

/-- Exactly the supplied number of guarded worklist transitions. -/
def run {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (fuel : Nat) (requests : List (Request n)) : State n :=
  (step arity symbols S)^[fuel] (some requests)

/-- Success means completed work; failed or unfinished states return false. -/
def done {n : Nat} : State n → Bool
  | some [] => true
  | _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluation
