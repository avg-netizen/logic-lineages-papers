module
public import LogicLineages.OrdinalComparison.PositiveNormalFlagDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PositiveNormalFlagComputable : Prop := Computable₂ encodedPositiveNormalFormsEqual

def PositiveNormalFlagCorrect : Prop :=
  ∀ E F : FixedLimitPositiveExpr,
    fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero F →
    (encodedPositiveNormalFormsEqual (positiveExprEncode E) (positiveExprEncode F)=true ↔
      collectedPositiveNormalize E=collectedPositiveNormalize F)

end LogicLineages.OrdinalComparison.Targets
