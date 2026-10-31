module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerTargets
open PredictionOriginalDegreeLower PredictionOriginalHardness

def ActualMeasureLower : Prop := ∀ g : Nat → Nat → Nat, OriginalListing g →
  ∀ A : Nat → Nat, MeasureOracle g A →
    ComputableIn {fun n => Part.some (A n)} OraclePiThree.thirdJump

def ActualComparatorLower : Prop := ∀ g : Nat → Nat → Nat, OriginalListing g →
  ∀ A : Nat → Nat, ComparatorOracle g A →
    ComputableIn {fun n => Part.some (A n)} OraclePiThree.thirdJump

end LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerTargets
