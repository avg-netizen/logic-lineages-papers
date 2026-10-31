module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionMeasureOrder

def MonotoneLevels (levels : Nat → Nat → Nat) : Prop :=
  ∀ n, Monotone (fun m => levels m n)

end LogicLineages.ComputabilityKnowledge.PredictionMeasureOrder
