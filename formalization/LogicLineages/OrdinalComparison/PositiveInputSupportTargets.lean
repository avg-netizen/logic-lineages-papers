module
public import LogicLineages.OrdinalComparison.PositiveInputSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Concrete program agreement, not an assumed head-evaluation oracle. -/
def PositiveClosedProgramCorrect : Prop :=
  ∀ E : FixedLimitPositiveExpr, actualFixedLimitProfileEval E 0 ∈ positiveClosedProgram E

def PositiveClosedProgramTotal : Prop := ∀ E : FixedLimitPositiveExpr, (positiveClosedProgram E).Dom

def PositiveInputAbsent : Prop :=
  ∀ E : FixedLimitPositiveExpr, positiveExprHasInput E=false → ∀ x : Nat,
    actualFixedLimitProfileEval E x=actualFixedLimitProfileEval E 0

/-- Stronger all-Nat form of the source's positive-valuation lower bound;
real nonzero-limit head validity is retained explicitly. -/
def PositiveInputPresentLower : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    positiveExprHasInput E=true → ∀ x : Nat, x ≤ actualFixedLimitProfileEval E x

end LogicLineages.OrdinalComparison.Targets
