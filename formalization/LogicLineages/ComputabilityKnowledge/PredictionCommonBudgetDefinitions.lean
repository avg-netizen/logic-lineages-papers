module

public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionBaselineGameDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCommonBudget
open PredictionGame PredictionLearning PredictionCommonFuel

def commonFuelSearch (v : Code) (n : Nat) : Part Nat :=
  Nat.rfind fun s => Part.some (commonFuelTest v n s)

end LogicLineages.ComputabilityKnowledge.PredictionCommonBudget
