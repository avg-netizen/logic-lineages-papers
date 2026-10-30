module

public import LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetTargets
open PredictionGame PredictionLearning PredictionRobust PredictionBaselineGame

def ComputableBudgetPrefix : Prop :=
  ∀ b : Nat → Nat, Computable b → Computable (budgetPrefix b)

def ComputableBudgetRule : Prop :=
  ∀ b : Nat → Nat, Computable b → Computable₂ (budgetRule b)

def ActualAnyPredictorBaselineCorrect : Prop :=
  ∀ (b : Nat → Nat) (p : Policy) (e : Code) (he : TotalBinary e), UniformAvailable e he b →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      let h := histories p (policy e he) n
      budgetRule b h.evasions h.predictions = evasion p (policy e he) n

end LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetTargets
