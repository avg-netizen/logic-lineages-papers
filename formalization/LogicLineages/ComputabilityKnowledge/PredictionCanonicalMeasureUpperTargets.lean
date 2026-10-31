module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperTargets
open PredictionCanonicalMeasureUpper PredictionCanonicalTapeBounds PredictionTapeObservation

def ActualCanonicalThresholdOracle : Prop := ∃ u v : Nat.Partrec.Code,
  ComputableIn {fun n => Part.some (OraclePiThree.thirdJump n)} (selectedDecision u v) ∧
  ∀ p (hp : TotalBinary p) k,
    (selectedDecision u v (Nat.pair p k)=1 ↔
      PredictionTapeRuntimeClass.Threshold (policy p hp) (PredictionOriginalBounds.levelBound listing (k+1)))

def CanonicalFiniteUpper : Prop := ∃ u v : Nat.Partrec.Code,
  RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} (result u v) ∧
  ∀ p (hp : TotalBinary p), ∃ h : Nat,
    result u v p=Part.some (h+1) ∧ height (policy p hp) = (h : WithTop Nat)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperTargets
