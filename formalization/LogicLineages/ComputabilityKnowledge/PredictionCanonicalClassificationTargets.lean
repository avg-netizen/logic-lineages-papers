module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassificationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassificationTargets
open PredictionCanonicalClassification PredictionTapeObservation PredictionOriginalClassification

def WholeSourceCanonicalTheorem : Prop :=
  (∀ p (hp : TotalBinary p), ∃ h : Nat, canonicalMeasure p hp = (h : WithTop Nat)) ∧
  (∃ m0 : Nat, 1 ≤ m0 ∧ ∀ m : Nat, m0 ≤ m →
    CompletePiThreeOnTotal (fun p hp => (m : WithTop Nat) ≤ canonicalMeasure p hp)) ∧
  MeasureDegree PredictionCanonicalTapeBounds.listing

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassificationTargets
