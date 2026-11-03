module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidation
open Source NumberedNumericDecoding NumberedTypedRequests

/-- Check the original typed term and its finite-universe membership using fuel
read from the original numeric Code input. -/
def termValid (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (tau : Ty) (value : Nat) : Bool :=
  (decodeCode n value).any (fun code =>
    NumberedUniverseEvaluation.evaluate arity symbols S (value + 1) [.term Gamma tau code])

/-- Check the complete ordered argument list against the same finite window. -/
def argumentsValid (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma types : List Ty) (value : Nat) : Bool :=
  (decodeCode n value).any (fun code =>
    NumberedUniverseEvaluation.evaluate arity symbols S (value + 1) [.arguments Gamma types code])

/-- Use the unchanged packed type/Code pairing and actual numeric parsers. -/
def packedValid (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat) : Bool :=
  (decodeType (Nat.unpair value).1).any (fun tau =>
    termValid n arity symbols S Gamma tau (Nat.unpair value).2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidation
