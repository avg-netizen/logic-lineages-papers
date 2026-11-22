module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficientTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficient
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (encodeTerm exactCanonicalTape)
open ActualRawCanonicalNodeMetadata (activeLabelCode labelCalibrationOne classFlagsCalibration)
open ActualFullValueLabels (activeLabel)
open ActualFullValueMaximalMetadata (doubledWeight weights maximalCoefficient)
open ActualFullLabelPairGuards (Answer)

theorem doubledCalibration (t : WeightedOperand) : doubledCode (encodeTerm t) = doubledWeight t := by
  rcases t with ⟨w,op⟩
  cases op <;> rfl

theorem weightsCalibration (ts : List WeightedOperand) : weightsCode (ts.map encodeTerm) = weights ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (encodeTerm t :: ts.map encodeTerm).filterMap
        (fun u => (activeLabelCode u).map (fun _ => doubledCode u)) =
      (t :: ts).filterMap (fun u => (activeLabel u).map (fun _ => doubledWeight u))
    simp only [List.filterMap_cons,labelCalibrationOne,doubledCalibration]
    cases h : activeLabel t with
    | none =>
      simp only [h,Option.map_none]
      exact ih
    | some l =>
      simp only [h,Option.map_some]
      exact congrArg (List.cons (doubledWeight t)) ih

theorem exactRawCanonicalWeightTape : ExactRawCanonicalWeightTape :=
  ⟨doubledCalibration,weightsCalibration⟩

theorem coefficientCalibration (ts : List WeightedOperand) (answers : List Answer) :
    coefficientCode (ts.map encodeTerm) (answers.map Answer.code) = maximalCoefficient ts answers := by
  unfold coefficientCode
  rw [weightsCalibration,classFlagsCalibration] <;> rfl

theorem exactRawCanonicalCoefficient : ExactRawCanonicalCoefficient := by
  refine ⟨coefficientCalibration,?_⟩
  intro ts answers
  rw [← exactCanonicalTape.1 ts,coefficientCalibration]

end LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficient
