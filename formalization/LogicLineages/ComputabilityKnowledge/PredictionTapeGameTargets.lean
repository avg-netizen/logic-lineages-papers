module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeGameDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeGameTargets
open PredictionGame PredictionTapeObservation PredictionTapeGame

def ComputableBudgetRule : Prop :=
  ∀ b : Nat → Nat, Computable b → Computable₂ (budgetRule b)

def ActualAnyPredictorBaselineCorrect : Prop :=
  ∀ (b : Nat → Nat) (p : Policy) (e : Nat) (he : TotalBinary e),
    UniformAvailable e he b → ∃ N, ∀ n, N ≤ n →
      let h := histories p (policy e he) n
      budgetRule b h.evasions h.predictions = evasion p (policy e he) n

end LogicLineages.ComputabilityKnowledge.PredictionTapeGameTargets
