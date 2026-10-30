module

public import LogicLineages.ComputabilityKnowledge.PredictionFlipLearningDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReduction
open PredictionGame PredictionLearning PredictionBaselineGame

/-- A literal evaln-availability learning class, not the paper's tape-runtime class. -/
def LearnsAvailable (b : Nat → Nat) (p : Policy) : Prop :=
  ∀ (e : Code) (he : TotalBinary e), UniformAvailable e he b → Learns p (policy e he)

end LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReduction
