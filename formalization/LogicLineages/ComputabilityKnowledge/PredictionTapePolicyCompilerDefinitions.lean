module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompiler

def transport (f : Nat → Nat) (c : Nat.Partrec.Code) : Nat := f (Encodable.encode c)

def compileSelfHistory (f : Nat → Nat) (u : Nat.Partrec.Code) (z : Nat) : Nat :=
  transport f (PredictionUniformHistory.compileSelfHistory u z)

end LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompiler
