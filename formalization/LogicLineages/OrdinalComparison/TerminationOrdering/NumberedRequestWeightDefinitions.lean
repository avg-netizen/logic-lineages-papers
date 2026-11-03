module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeight
open NumberedAuxiliaryCoding NumberedTypedRequests

def codeWeight {n : Nat} : Code (Fin n) → Nat
  | .var _ | .bottom _ | .argumentsNil => 1
  | .lam _ body => 1 + codeWeight body
  | .app _ q a => 1 + codeWeight q + codeWeight a
  | .ordinary _ base => 1 + codeWeight base
  | .numbered _ _ _ base _ extras => 1 + codeWeight base + codeWeight extras
  | .argumentsCons _ q rest => 1 + codeWeight q + codeWeight rest

def requestWeight {n : Nat} : Request n → Nat
  | .term _ _ code | .arguments _ _ code => codeWeight code

def workWeight {n : Nat} (requests : List (Request n)) : Nat :=
  (requests.map requestWeight).sum

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeight
