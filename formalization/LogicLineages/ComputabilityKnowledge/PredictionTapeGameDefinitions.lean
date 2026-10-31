module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeGame
open PredictionTapeObservation PredictionSelfHistory

def budgetRule (b : Nat → Nat) : PairedRule :=
  fun xs ys => PredictionTapeBaseline.baseline (PredictionRobust.budgetPrefix b xs.length) xs ys

def UniformAvailable (e : Nat) (hp : TotalBinary e) (b : Nat → Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ ys : List Bool, ys.length = n →
    boundedMove e (b n) ys = some (policy e hp ys)

end LogicLineages.ComputabilityKnowledge.PredictionTapeGame
