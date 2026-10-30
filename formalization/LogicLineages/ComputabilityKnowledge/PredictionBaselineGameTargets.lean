module

public import LogicLineages.ComputabilityKnowledge.PredictionBaselineGameDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBaselineGameTargets
open PredictionGame PredictionLearning PredictionBaselineGame

def PrimitiveRecursiveBudgetRule : Prop :=
  ∀ b : Nat → Nat, Primrec b → Primrec₂ (budgetRule b)

def BaselineProgramRealization : Prop :=
  ∀ b : Nat → Nat, Primrec b → Primrec (baselinePolicy b) ∧
    ∃ (p : Code) (hp : TotalBinary p), policy p hp = baselinePolicy b

def ActualBaselineLearning : Prop :=
  ∀ (b : Nat → Nat) (e : Code) (hp : TotalBinary e),
    UniformAvailable e hp b → Learns (baselinePolicy b) (policy e hp)

def OrdinaryBaselineLearning : Prop :=
  ∀ b : Nat → Nat, Primrec b →
    ∃ (p : Code) (hp : TotalBinary p), policy p hp = baselinePolicy b ∧
      ∀ (e : Code) (he : TotalBinary e), UniformAvailable e he b →
        Learns (policy p hp) (policy e he)

end LogicLineages.ComputabilityKnowledge.PredictionBaselineGameTargets
