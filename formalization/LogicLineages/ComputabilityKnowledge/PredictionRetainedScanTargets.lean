module

public import LogicLineages.ComputabilityKnowledge.PredictionRetainedScanDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRetainedScanTargets
open PredictionCanonicalList PredictionRetainedScan

def EarlierRetainedScanCalibration : Prop :=
  ∀ i : Nat, Representative i ↔ RetainedScanEligible i

end LogicLineages.ComputabilityKnowledge.PredictionRetainedScanTargets
