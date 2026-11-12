module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryVisitScheduler OriginalHereditaryExpansion
open OriginalRawSyntaxTransport (arityValue tagValue)
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
  have hf : (visitNumber ∘ jobNumber (n := n) c) =
      (fun t => visitNumber (Nat.pair (codeNumber t.code) (Nat.pair c (Encodable.encode t.context)))) := by
    funext t
    rfl
  apply congrArg (fun w => Nat.pair w (numbersNumber outputs))
  simpa only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,
    Matrix.cons_val_one,numbersNumber,jobNumber,List.map_map,hf,Function.comp_apply] using ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
