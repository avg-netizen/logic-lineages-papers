module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkEncodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkVisitProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryRuntimeWork OriginalHereditaryAgendaDefinitions
open NumberedMultisetNumeric NumberedLeastCodeRepresentative
open OriginalHereditaryVisitScheduler (visitNumber returnNumber)

theorem agendaAfter {n : Nat} (c : Nat) (a : Job n) (suffix : List (Frame n)) :
    agendaNumber c ((jobs c a).map Frame.visit ++ Frame.returning a :: suffix) =
    numbersNumber (((jobs c a).map (jobNumber c)).map visitNumber ++
      returnNumber (jobNumber c a) (OriginalHereditaryWorkBound.children a.core.context a.core.code).length
        a.core.context.length :: suffix.map (frameNumber c)) := by
  simp only [agendaNumber,List.map_append,List.map_cons,List.map_map,frameNumber]
  rfl

theorem visitWork (R : Program 2) {n : Nat} (c : Nat) (a : Job n)
    (suffix : List (Frame n)) (result : Nat) :
    (Nat.unpair (evaluate (OriginalHereditaryCombinedStep.step R)
      (ofFn ![Nat.pair (agendaNumber c (.visit a :: suffix)) result]))).1 =
      agendaNumber c ((jobs c a).map Frame.visit ++ Frame.returning a :: suffix) := by
  rw [agendaAfter]
  unfold agendaNumber
  rw [List.map_cons,frameNumber,numbersNumber,OriginalHereditaryCombinedStepProof.visitDispatch,
    OriginalHereditaryAnnotatedVisitEvaluationProof.visitEvaluation,Nat.unpair_pair]
  unfold jobNumber
  rw [OriginalHereditaryAnnotatedExpansionNativeProof.nativeExpansion,
    OriginalHereditaryVisitSchedulerMapProof.tagCalibration]
  simp only [OriginalHereditaryAnnotatedExpansion.forgetNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber,OriginalHereditaryExpansion.jobNumber,Nat.unpair_pair]
  rw [OriginalContextInsertionCalibrationProof.lengthContext,
    OriginalHereditaryVisitSchedulerNativeProof.arityChildren a.core.context a.core.code]
  have ha := OriginalContextInsertionCalibrationProof.appendNumbers
    ((OriginalHereditaryAnnotatedExpansion.values a.role a.typ (codeNumber a.core.code)
      ((OriginalHereditaryWorkBound.successors a.core).map (OriginalHereditaryExpansion.jobNumber c))).map visitNumber)
    (returnNumber (jobNumber c a) (OriginalHereditaryWorkBound.children a.core.context a.core.code).length
      a.core.context.length :: suffix.map (frameNumber c))
  have h := OriginalHereditaryRuntimeWorkEncodingProof.jobsEncoding n c a
  rw [← h] at ha ⊢
  simpa only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,
    Matrix.cons_val_one,numbersNumber,List.map_append,List.map_cons,List.map_map,
    frameNumber,jobNumber,OriginalHereditaryExpansion.jobNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber,Function.comp_def] using ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkVisitProof
