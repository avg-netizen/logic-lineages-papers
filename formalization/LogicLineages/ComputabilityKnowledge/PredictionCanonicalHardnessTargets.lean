module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessTargets
open PredictionCanonicalHardness

def CanonicalFixedThresholds : Prop := ∃ m0 : Nat, 1 ≤ m0 ∧ ∀ m : Nat, m0 ≤ m →
  PredictionOriginalClassification.CompletePiThreeOnTotal (ThresholdPredicate m)

def ActualCanonicalMeasureLower : Prop := ∀ A : Nat → Nat,
  PredictionOriginalDegreeLower.MeasureOracle PredictionCanonicalTapeBounds.listing A →
    ComputableIn {fun n => Part.some (A n)} OraclePiThree.thirdJump

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessTargets
