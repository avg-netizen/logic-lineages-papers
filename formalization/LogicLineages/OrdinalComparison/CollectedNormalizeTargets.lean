module
public import LogicLineages.OrdinalComparison.CollectedNormalizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedPositiveNormalizeValid : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    CollectedPositiveValid (collectedPositiveNormalize E)

def CollectedPositiveNormalizeSupport : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    collectedPositiveSupport (collectedPositiveNormalize E)=positiveExprHasInput E

def CollectedPositiveNormalizeValue : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E → ∀ x : Nat,
    actualCollectedPositiveEval (collectedPositiveNormalize E) x=actualFixedLimitProfileEval E x

end LogicLineages.OrdinalComparison.Targets
