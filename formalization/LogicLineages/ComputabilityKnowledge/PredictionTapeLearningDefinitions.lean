module
public import LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionLearning
@[expose] public section
/-! The accepted ordinary-code learning certificate evaluated after a genuine
uniform reverse binary tape compiler. It preserves actual policies and the
simultaneous game; no evader runtime claim is transported by this translation. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeLearning

def learningMatrix (u : Nat.Partrec.Code) (p e cutoff certificate : Nat) : Bool :=
  PredictionLearning.learningMatrix (PredictionVariableTapePartrec.compile u p)
    (PredictionVariableTapePartrec.compile u e) cutoff certificate

end LogicLineages.ComputabilityKnowledge.PredictionTapeLearning
