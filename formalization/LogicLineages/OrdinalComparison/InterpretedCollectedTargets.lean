module
public import LogicLineages.OrdinalComparison.InterpretedCollectedDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def InterpretedCollectedAddition : Prop :=
  ∀ (H : NONote → Nat → Nat) (A B : CollectedPositiveNF) (x : Nat),
    interpretedCollectedEval H (collectedPositiveAdd A B) x=
      interpretedCollectedEval H A x+interpretedCollectedEval H B x

def InterpretedCollectedNormalization : Prop :=
  ∀ (H : NONote → Nat → Nat) (E : FixedLimitPositiveExpr),
    fixedLimitProfileBelow epsilonZero E → PositiveClosedHeadAgreement H E → ∀ x : Nat,
    interpretedCollectedEval H (collectedPositiveNormalize E) x=interpretedPositiveEval H E x

/-- Actual recursive head closure of the computed normal form, including
all nested argument forms; not merely its root/source textual head list. -/
def CollectedNormalizationHeadClosure : Prop :=
  ∀ (P : NONote → Prop) (E : FixedLimitPositiveExpr), positiveHeadsSatisfy P E →
    collectedHeadsSatisfy P (collectedPositiveNormalize E)

end LogicLineages.OrdinalComparison.Targets
