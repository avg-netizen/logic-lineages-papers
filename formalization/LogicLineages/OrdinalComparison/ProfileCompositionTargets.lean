module
public import LogicLineages.OrdinalComparison.ProfileCompositionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Exact source profile composition requested by section8's simultaneous
limit-cut certificate. All heads remain below the actual original limit. -/
def ActualProfileCompositionSource : Prop :=
  ∀ (L : Ordinal.{0}) (E F : FixedLimitPositiveExpr),
    fixedLimitProfileBelow L E → fixedLimitProfileBelow L F →
    fixedLimitProfileBelow L (fixedProfileCompose E F) ∧
      ∀ x : Nat, actualFixedLimitProfileEval (fixedProfileCompose E F) x=
        actualFixedLimitProfileEval E (actualFixedLimitProfileEval F x)

def ProfileCompositionInputSupport : Prop :=
  ∀ E F : FixedLimitPositiveExpr,
    positiveExprHasInput (fixedProfileCompose E F)=
      (positiveExprHasInput E && positiveExprHasInput F)

/-- Real uniform all-code computation of the composed SOURCE TREE, not an
extensional function oracle or an effective-composition assumption. -/
def ProfileCompositionProgram : Prop :=
  Primrec₂ encodedProfileCompose ∧ ∀ E F : FixedLimitPositiveExpr,
    encodedProfileCompose (positiveExprEncode E) (positiveExprEncode F)=
      positiveExprEncode (fixedProfileCompose E F)

end LogicLineages.OrdinalComparison.Targets
