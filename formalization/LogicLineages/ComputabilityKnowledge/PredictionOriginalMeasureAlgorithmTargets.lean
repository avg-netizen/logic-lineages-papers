module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmTargets
open PredictionOriginalMeasureAlgorithm PredictionOriginalMeasureMatrices

def RelativeAlgorithm : Prop := ∀ u v : Nat.Partrec.Code,
  ComputableIn {fun n => Part.some (OraclePiThree.thirdJump n)} (levelDecision u v) →
  ComputableIn {fun n => Part.some (OraclePiThree.thirdJump n)} (infinityDecision u v) →
  RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} (result u v)

def ExactOracleMeasure : Prop :=
  ∀ g : Nat → Nat → Nat, Computable₂ g →
    ∃ u v : Nat.Partrec.Code,
      RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} (result u v) ∧
      ∀ (p : Nat) (hp : PredictionTapeObservation.TotalBinary p),
        ∃ output : Nat, result u v p = Part.some output ∧
          outputValue output = PredictionOriginalHardness.originalHeight g (PredictionTapeObservation.policy p hp)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmTargets
