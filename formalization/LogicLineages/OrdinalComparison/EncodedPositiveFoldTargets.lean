module
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedPositiveFoldPartialRecursive : Prop :=
  Partrec encodedPositiveFoldProgram

def EncodedPositiveFoldTableTotal : Prop :=
  ∀ n : Nat, ∃ table : List Nat, table ∈ encodedPositiveFoldTable n ∧ table.length=n

def EncodedPositiveFoldCorrect : Prop :=
  ∀ E : FixedLimitPositiveExpr,
    encodedPositiveFoldProgram (positiveExprEncode E)=positiveClosedProgram E

def EncodedPositiveFoldTotal : Prop :=
  ∀ n : Nat, (encodedPositiveFoldProgram n).Dom

def EncodedPositiveFoldComputable : Prop :=
  Computable encodedPositiveFoldValue

def EncodedPositiveFoldSourceCorrect : Prop :=
  ∀ E : FixedLimitPositiveExpr,
    encodedPositiveFoldValue (positiveExprEncode E)=actualFixedLimitProfileEval E 0

end LogicLineages.OrdinalComparison.Targets
