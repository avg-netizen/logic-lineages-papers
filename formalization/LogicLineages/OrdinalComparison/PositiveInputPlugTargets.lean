module
public import LogicLineages.OrdinalComparison.PositiveInputPlugDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PositiveInputPlugSource : Prop :=
  ∀ (E : FixedLimitPositiveExpr) (x : Nat),
    (fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero (positiveInputPlug E x)) ∧
    actualFixedLimitProfileEval (positiveInputPlug E x) 0=actualFixedLimitProfileEval E x

def EncodedPositivePlugPrimitiveRecursive : Prop := Primrec₂ encodedPositivePlug

def EncodedPositivePlugCorrect : Prop :=
  ∀ (E : FixedLimitPositiveExpr) (x : Nat),
    encodedPositivePlug (positiveExprEncode E) x=positiveExprEncode (positiveInputPlug E x)

def EncodedPositiveEvaluationComputable : Prop := Computable₂ encodedPositiveEvaluation

def EncodedPositiveEvaluationCorrect : Prop :=
  ∀ (E : FixedLimitPositiveExpr) (x : Nat),
    encodedPositiveEvaluation (positiveExprEncode E) x=actualFixedLimitProfileEval E x

end LogicLineages.OrdinalComparison.Targets
