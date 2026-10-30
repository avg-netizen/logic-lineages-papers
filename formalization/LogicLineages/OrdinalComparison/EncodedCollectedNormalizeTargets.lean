module
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedCollectedOpenCorrect : Prop :=
  Primrec encodedCollectedOpen ∧
    ∀ A : CollectedPositiveNF, CollectedPositiveValid A →
      encodedCollectedOpen (collectedPositiveEncode A)=collectedPositiveSupport A

def EncodedCollectedNormalizeComputable : Prop := Computable encodedCollectedNormalize

def EncodedCollectedNormalizeCorrect : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    encodedCollectedNormalize (positiveExprEncode E)=
      collectedPositiveEncode (collectedPositiveNormalize E)

def EncodedCollectedNormalizeSource : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    ∃ A : CollectedPositiveNF, CollectedPositiveValid A ∧
      collectedPositiveEncode A=encodedCollectedNormalize (positiveExprEncode E) ∧
      ∀ x : Nat, actualCollectedPositiveEval A x=actualFixedLimitProfileEval E x

end LogicLineages.OrdinalComparison.Targets
