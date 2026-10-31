module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationTargets
open PredictionOriginalClassification PredictionOriginalHardness PredictionTapeObservation

def WholeSourceOriginalTheorem : Prop := ∀ g : Nat → Nat → Nat, OriginalListing g →
  (∃ m0 : Nat, 1 ≤ m0 ∧ ∀ m : Nat, m0 ≤ m →
    CompletePiThreeOnTotal (fun p hp => (m : WithTop Nat) ≤ originalHeight g (policy p hp))) ∧
  CompletePiThreeOnTotal (fun p hp => originalHeight g (policy p hp)=⊤) ∧
  MeasureDegree g ∧ ComparatorDegree g

end LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationTargets
