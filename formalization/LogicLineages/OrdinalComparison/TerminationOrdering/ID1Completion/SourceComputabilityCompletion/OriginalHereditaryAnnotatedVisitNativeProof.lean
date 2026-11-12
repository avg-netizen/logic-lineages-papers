module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedVisit
open OriginalHereditaryVisitScheduler (stateNumber visitNumber returnNumber)
open NumberedMultisetNumeric NumberedLeastCodeRepresentative

theorem visitSimulation : OriginalHereditaryAnnotatedVisitTargets.VisitSimulation := by
  intro n c role typ s agenda outputs
  dsimp only
  unfold stateNumber
  rw [numbersNumber,OriginalHereditaryAnnotatedVisitEvaluationProof.visitEvaluation,
    OriginalHereditaryAnnotatedExpansionNativeProof.nativeExpansion,
    OriginalHereditaryVisitSchedulerMapProof.tagCalibration]
  simp only [OriginalHereditaryAnnotatedExpansion.forgetNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber,OriginalHereditaryExpansion.jobNumber,Nat.unpair_pair]
  rw [OriginalContextInsertionCalibrationProof.lengthContext,
    OriginalHereditaryVisitSchedulerNativeProof.arityChildren s.context s.code]
  have ha := OriginalContextInsertionCalibrationProof.appendNumbers
    ((OriginalHereditaryAnnotatedExpansion.values role typ (codeNumber s.code)
      ((OriginalHereditaryWorkBound.successors s).map (OriginalHereditaryExpansion.jobNumber c))).map visitNumber)
    (returnNumber (OriginalHereditaryAnnotatedExpansion.jobNumber role typ (OriginalHereditaryExpansion.jobNumber c s))
      (OriginalHereditaryWorkBound.children s.context s.code).length s.context.length :: agenda)
  apply congrArg (fun w => Nat.pair w (numbersNumber outputs))
  simpa only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,
    Matrix.cons_val_one,numbersNumber,OriginalHereditaryExpansion.jobNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber] using ha

theorem forgettingSimulation : OriginalHereditaryAnnotatedVisitTargets.ForgettingSimulation := by
  intro n c role typ s agenda outputs
  dsimp only
  rw [visitSimulation,OriginalHereditaryAnnotatedVisitForgetProof.stateCalibration,
    OriginalHereditaryVisitSchedulerNativeProof.visitSimulation]
  simp only [List.map_append,List.map_cons,OriginalHereditaryAnnotatedVisitForgetProof.returnForget,
    OriginalHereditaryAnnotatedExpansion.forgetNumber,OriginalHereditaryAnnotatedExpansion.jobNumber,
    Nat.unpair_pair]
  have hf : (forgetFrameNumber ∘ visitNumber) =
      (visitNumber ∘ OriginalHereditaryAnnotatedExpansion.forgetNumber) := by
    funext j
    exact OriginalHereditaryAnnotatedVisitForgetProof.visitForget j
  rw [List.map_map,hf,← List.map_map,
    OriginalHereditaryAnnotatedExpansionListProof.forgetting]
  simp only [List.map_map]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitNativeProof
