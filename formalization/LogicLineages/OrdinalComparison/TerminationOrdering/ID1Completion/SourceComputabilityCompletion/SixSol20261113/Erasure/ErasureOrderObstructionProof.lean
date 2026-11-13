module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ErasureOrderObstructionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ErasureOrderObstructionProof
open Source NumberedAuxiliaryCoding NumberedUniformPackedDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ErasureOrderObstruction

/-- Reuse proved all-code native calibration, never unfold the enormous
primitive-recursive execution bound or reflect this into an internal proof. -/
theorem packedErasure (q : Code (Fin 1)) :
    evaluate OriginalRawSyntaxTransport.erasePackedRaw
      (List.Vector.ofFn ![0,0,ContextUniformPrimary.packedNumber (.ground,q)]) =
        ContextUniformPrimary.packedNumber (.ground,erase q) := by
  rw [OriginalRawObjectTransportEvaluationProof.erasePackedEvaluation]
  simp only [ContextUniformPrimary.packedNumber,Nat.unpair_pair]
  have h := OriginalRawSyntaxTransportCodeProof.actualRawSyntaxCodeCalibration.2.1
    1 0 Ty.ground q
  simpa only [NumberedLeastCodeRepresentative.typeNumber,erase] using congrArg (Nat.pair 0) h

theorem actualTypedExchangePair : ActualTypedExchangePair := by
  refine ⟨?_,?_,?_,?_,?_,?_,packedErasure lower,packedErasure upper⟩
  all_goals decide

theorem actualOrderReversal : ActualOrderReversal := by
  constructor <;> decide
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ErasureOrderObstructionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ErasureOrderObstructionProof
