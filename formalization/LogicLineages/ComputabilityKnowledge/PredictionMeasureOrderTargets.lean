module
public import LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderTargets
open PredictionMeasureOrder PredictionTapeMeasureContract PredictionTapeRuntimeClass

def PositiveThresholdOrder : Prop :=
  ∀ (levels : Nat → Nat → Nat), MonotoneLevels levels →
    ∀ (p : PredictionGame.Policy) (m : Nat), 1 ≤ m →
      ((m : WithTop Nat) ≤ height levels p ↔ Threshold p (levels m))

end LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderTargets
