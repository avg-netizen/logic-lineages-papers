module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidation
open Source NumberedNumericDecoding NumberedTypedRequests NumberedTypedEvaluation

/-- Validate the actual numeric Code using a bound read from its input number. -/
def termValid (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty)
    (value : Nat) : Bool :=
  match decodeCode n value with
  | none => false
  | some code => evaluate arity (value + 1) [.term Gamma tau code]

/-- Argument-list validation retains the exact ordered expected types. -/
def argumentsValid (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (value : Nat) : Bool :=
  match decodeCode n value with
  | none => false
  | some code => evaluate arity (value + 1) [.arguments Gamma types code]

/-- The packed input uses the accepted type/code pairing, with no dependent
typed decoder invoked by this Boolean validator. -/
def packedValid (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) : Bool :=
  match decodeType (Nat.unpair value).1 with
  | none => false
  | some tau => termValid n arity Gamma tau (Nat.unpair value).2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidation
