module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassification

noncomputable def canonicalMeasure (p : Nat) (hp : PredictionTapeObservation.TotalBinary p) : WithTop Nat :=
  PredictionCanonicalTapeBounds.height (PredictionTapeObservation.policy p hp)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassification
