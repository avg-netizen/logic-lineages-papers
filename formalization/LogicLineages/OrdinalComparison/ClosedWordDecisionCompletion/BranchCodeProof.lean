module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.PrefixCodeProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportCalibrationProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion

theorem matrix_calibration (D maximum : Nat) (p : Formula) :
    Code.matrix D maximum (Formula.encode p) = OutcomeTransport.encodeMatrix (matrix D maximum p) := by
  simp only [Code.matrix,residue_calibration,matrix,OutcomeTransportProof.compile_calibration]

theorem commonTail_calibration (D floor : Nat) (p : Formula) :
    Code.commonTail D floor (Formula.encode p) = commonTail D floor p := by
  simp only [Code.commonTail,commonTail,names_calibration,residueTail_calibration,
    OutcomeTransportProof.originalTail_calibration,matrix_calibration,OutcomeTransport.encodeMatrix]

theorem high_calibration (D N : Nat) (p : Formula) :
    Code.highChildren D N (Formula.encode p) =
      (highChildren D N p).map (fun b => (b.1,Formula.encode b.2)) := by
  simp only [Code.highChildren,names_calibration,matrix_calibration,
    OutcomeTransport.encodeMatrix,List.map_map,Function.comp_def,highChildren,
    List.map_flatMap]
  apply congrArg (fun f : Nat → List (Nat × Nat) => (names p).flatMap f)
  funext maximum
  apply List.map_congr_left
  intro q hq
  rw [frame_calibration]
  change (N,WordLinearDecisionCompletion.Code.eliminate maximum
      (Formula.encode (.conj (frame N maximum (names p)) q))) = _
  rw [WordLinearDecisionCompletion.Proof.literalCodeCalibration]

theorem children_calibration (D floor : Nat) (p : Formula) :
    Code.children D floor (Formula.encode p) =
      (children D floor p).map (fun b => (b.1,Formula.encode b.2)) := by
  simp only [Code.children,children,commonTail_calibration,prefix_calibration,
    high_calibration,List.map_append]

theorem literalCodeCalibration : BranchTargets.LiteralCodeCalibration :=
  ⟨initial_calibration,commonTail_calibration,children_calibration⟩

#print axioms matrix_calibration
#print axioms commonTail_calibration
#print axioms high_calibration
#print axioms children_calibration
#print axioms literalCodeCalibration

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeProof
