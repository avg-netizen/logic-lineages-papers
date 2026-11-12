module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryVisitScheduler OriginalHereditaryExpansion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem arityChildren {n : Nat} (Gamma : List Ty) (q : Code (Fin n)) :
    arityValue (codeNumber q) = (OriginalHereditaryWorkBound.children Gamma q).length := by
  cases q <;> simp [arityValue,tagValue,codeNumber,OriginalHereditaryWorkBound.children,Nat.unpair_pair]

theorem visitSimulation : OriginalHereditaryVisitSchedulerTargets.VisitSimulation := by
  intro n c s agenda outputs
  unfold stateNumber
  rw [numbersNumber,OriginalHereditaryVisitSchedulerEvaluationProof.visitEvaluation]
  simp only [jobNumber,Nat.unpair_pair]
  rw [OriginalHereditaryExpansionNativeProof.successorsCalibration,
    OriginalHereditaryVisitSchedulerMapProof.tagCalibration,
    OriginalContextInsertionCalibrationProof.lengthContext,arityChildren s.context s.code]
  have ha := OriginalContextInsertionCalibrationProof.appendNumbers
    (((OriginalHereditaryWorkBound.successors s).map (jobNumber c)).map visitNumber)
    (returnNumber (jobNumber c s) (OriginalHereditaryWorkBound.children s.context s.code).length
      s.context.length :: agenda)
  rw [ha]
  simp only [List.map_map,Function.comp_apply]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
