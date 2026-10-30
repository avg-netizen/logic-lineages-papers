module

public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionLearningProof

@[expose] public section
/-! Finite tests for a common evaln fuel bound. This is not a tape-runtime bound. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCommonFuel
open PredictionGame PredictionLearning PredictionUniformHistory

def booleanHistories : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (booleanHistories n).map (false :: ·) ++ (booleanHistories n).map (true :: ·)

def commonFuelTest (v : Code) (n s : Nat) : Bool :=
  (List.range (n + 1)).all fun k =>
    (booleanHistories n).all fun xs =>
      (boundedMove (compileSelfHistory v k) s xs).isSome

end LogicLineages.ComputabilityKnowledge.PredictionCommonFuel
