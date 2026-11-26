module
public import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsEnumProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapes
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (encodeTerm exactCanonicalTape)
open ActualRawCanonicalNodeMetadata (labelsCalibration)
open ActualFullValueLabels (Label labels)
open ActualFullLabelPairGuards (Answer choices)
open ActualFiniteFullValueGuards (pairs patterns exactFinitePatternEnumeration)

theorem literalTapes (n : Nat) : answerTapes n = (patterns n).map (List.map Answer.code) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [answerTapes,patterns,List.map_flatMap,ih]
    simp only [choices,List.flatMap_cons,List.flatMap_nil,List.map_map,Function.comp_def,
      Answer.code] <;> rfl

theorem exactRawAnswerTapeEnumeration : ExactRawAnswerTapeEnumeration := by
  refine ⟨literalTapes,?_⟩
  intro n tape valid
  rw [literalTapes] at valid
  obtain ⟨typed,has,rfl⟩ := List.mem_map.mp valid
  refine ⟨by simpa only [List.length_map] using (exactFinitePatternEnumeration n typed).mp has,?_⟩
  intro a present
  obtain ⟨ans,_,rfl⟩ := List.mem_map.mp present
  cases ans <;> decide

private theorem widthAux (left right : List Label) :
    (left.flatMap (fun l => right.map (fun r => (l,r)))).length =
      left.length * right.length := by
  induction left with
  | nil => simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons a rest ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons,ih,Nat.succ_mul,Nat.add_comm]

theorem widthCalibration (terms : List WeightedOperand) :
    pairWidth (terms.map encodeTerm) = (pairs (labels terms)).length := by
  unfold pairWidth pairs
  rw [labelsCalibration,List.length_map,widthAux]

theorem candidateCalibration (terms : List WeightedOperand) :
    candidateTapes (terms.map encodeTerm) =
      (patterns (pairs (labels terms)).length).map (List.map Answer.code) := by
  unfold candidateTapes
  rw [widthCalibration,literalTapes]

theorem exactCanonicalAnswerPairs : ExactCanonicalAnswerPairs := by
  refine ⟨fun terms => ⟨widthCalibration terms,candidateCalibration terms⟩,?_⟩
  intro ts
  simp only
  rw [← exactCanonicalTape.1 ts]
  exact ⟨widthCalibration _,candidateCalibration _⟩

end LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapes
