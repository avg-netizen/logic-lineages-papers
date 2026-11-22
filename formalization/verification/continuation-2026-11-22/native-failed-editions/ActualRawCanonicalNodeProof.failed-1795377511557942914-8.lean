module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficientProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeDecoratorProof
import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNode
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm encodeTerm groupRaw groupCheckedRaw groupTyped exactCanonicalTape)
open ActualRawSignedStaticCeiling (encodeSyntax)
open ActualRawCanonicalNodeMetadata (classFlagsCalibration)
open ActualRawCanonicalNodeCoefficient (coefficientCode coefficientCalibration)
open ActualRawCanonicalNodeDecorator (decorateCode exactRawDecorateCalibration)
open ActualRawMarkedZeroSuccessor (markedSuccessorCode exactRawMarkedSuccessor)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueLabels (labels)
open ActualFullValueMaximalMetadata (classFlags maximalCoefficient)
open ActualZeroSuccessorMarkedClass (decorate)
open ActualSymbolicZeroSuccessor (successorFromMarks)
open ActualCanonicalSymbolicZeroSuccessor (orderedSuccessor canonicalSuccessor)

theorem exactRawNodeBranches : ExactRawNodeBranches := by
  intro c ts answers
  refine ⟨rfl,rfl,?_⟩
  intro v eq nonzero
  change some (groupedCode (c,groupRaw ts,answers)) = some (v,none)
  simp only [groupedCode,eq,if_neg nonzero]

private theorem zeroBodyCalibration (c : Int) (ts : List WeightedOperand) (answers : List Answer) :
    zeroBodyCode (c,ts.map encodeTerm,answers.map Answer.code) =
      ((decorate ts (classFlags (labels ts) answers)).bind (successorFromMarks c)).map encodeSyntax := by
  change (decorateCode (ts.map encodeTerm) (ActualRawCanonicalNodeMetadata.classFlagsCode
      (ts.map encodeTerm) (answers.map Answer.code))).bind
        (fun marks => markedSuccessorCode (c,marks)) = _
  rw [classFlagsCalibration,exactRawDecorateCalibration]
  cases h : decorate ts (classFlags (labels ts) answers) with
  | none => simp only [h,Option.map_none,Option.bind_none]
  | some marks =>
    simp only [h,Option.map_some,Option.bind_some]
    change markedSuccessorCode (c,marks.map ActualRawMarkedZeroSuccessor.encodeMark) = _
    exact exactRawMarkedSuccessor c marks

theorem exactRawOrderedNode : ExactRawOrderedNode := by
  intro c ts answers
  unfold groupedCode orderedSuccessor
  simp only [coefficientCalibration,zeroBodyCalibration]
  by_cases h : maximalCoefficient ts answers = 0
  · simp only [if_pos h]
  · simp only [if_neg h,Option.map_none]

theorem exactRawCanonicalNode : ExactRawCanonicalNode := by
  intro gate c ts answers
  cases gate with
  | false => rfl
  | true =>
    change some (groupedCode (c,groupRaw (ts.map encodeTerm),answers.map Answer.code)) =
      some (maximalCoefficient (groupTyped ts) answers,(canonicalSuccessor c ts answers).map encodeSyntax)
    rw [← exactCanonicalTape.1 ts,exactRawOrderedNode] <;> rfl

end LogicLineages.PermittedControl.ActualRawCanonicalNode
