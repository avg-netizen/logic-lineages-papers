module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceRobustDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceRobustTargets
open PredictionTapeObservation PredictionTapeRuntimeClass
open PredictionRobust (historyPrefix budgetPrefix)

def SourceRobustBaseline : Prop :=
  ∀ (b : Nat → Nat), Computable b →
    ∀ (e : Nat) (he : TotalBinary e), EventualRuntime e b →
      ∀ y : Nat → Bool,
        let x := fun n => policy e he (historyPrefix y n)
        ∃ N, ∀ n, N ≤ n →
          PredictionTapeBaseline.baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) = x n

end LogicLineages.ComputabilityKnowledge.PredictionSourceRobustTargets
