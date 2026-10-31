module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardness

def ThresholdPredicate (m p : Nat) (hp : PredictionTapeObservation.TotalBinary p) : Prop :=
  (m : WithTop Nat) ≤ PredictionCanonicalTapeBounds.height (PredictionTapeObservation.policy p hp)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardness
