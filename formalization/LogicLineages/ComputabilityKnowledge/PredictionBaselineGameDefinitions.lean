module

public import LogicLineages.ComputabilityKnowledge.PredictionRobustDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBaselineGame
open PredictionLearning PredictionRobust PredictionSelfHistory

def budgetRule (b : Nat → Nat) : PairedRule :=
  fun xs ys => baseline (budgetPrefix b xs.length) xs ys

def baselinePolicy (b : Nat → Nat) : PredictionGame.Policy := selfPolicy (budgetRule b)

/-- Actual evaln availability on all inputs of each sufficiently large length.
This is not the source's tape-runtime domination predicate. -/
def UniformAvailable (e : Code) (hp : TotalBinary e) (b : Nat → Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ ys : List Bool, ys.length = n →
    boundedMove e (b n) ys = some (policy e hp ys)

end LogicLineages.ComputabilityKnowledge.PredictionBaselineGame
