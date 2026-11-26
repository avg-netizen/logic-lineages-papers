module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitForgetProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedVisit
open OriginalHereditaryVisitScheduler (stateNumber visitNumber returnNumber)
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalTypedDecoderEvaluationSupportProof
open OriginalHereditaryVisitSchedulerEvaluationProof (projectionEvaluation)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

theorem frameCalibration : OriginalHereditaryAnnotatedVisitTargets.FrameCalibration := by
  intro f
  simp only [forgetFrame,ifSameEvaluation,leftOfEvaluation,rightOfEvaluation,
    pairOfEvaluation,constantEvaluation,projectionEvaluation,List.Vector.get_ofFn,
    Matrix.cons_val_zero,forgetFrameNumber,OriginalHereditaryAnnotatedExpansion.forgetNumber]

theorem visitForget (j : Nat) :
    forgetFrameNumber (visitNumber j) = visitNumber (OriginalHereditaryAnnotatedExpansion.forgetNumber j) := by
  simp only [forgetFrameNumber,visitNumber,Nat.unpair_pair,ite_true]

theorem returnForget (j a b : Nat) :
    forgetFrameNumber (returnNumber j a b) =
      returnNumber (OriginalHereditaryAnnotatedExpansion.forgetNumber j) a b := by
  simp [forgetFrameNumber,returnNumber,Nat.unpair_pair]

theorem stepCalibration (head tail : Nat) :
    evaluate forgetStep (head ::ᵥ tail ::ᵥ nil) = 1 + Nat.pair (forgetFrameNumber head) tail := by
  rw [forgetStep,consOfEvaluation,unaryCompositionEvaluation]
  have h : evaluate forgetFrame (ofFn ![evaluate (.projection (0 : Fin 2)) (head ::ᵥ tail ::ᵥ nil)]) =
      forgetFrameNumber head := by
    exact frameCalibration head
  rw [h]
  rfl

theorem agendaCalibration (agenda : List Nat) :
    evaluate forgetAgenda (numbersNumber agenda ::ᵥ nil) = numbersNumber (agenda.map forgetFrameNumber) := by
  rw [forgetAgenda,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation,numbersRoundTrip]
  simp only [Option.getD_some]
  induction agenda with
  | nil => rfl
  | cons h t ih => rw [List.foldr_cons,ih,stepCalibration]; rfl

theorem stateCalibration : OriginalHereditaryAnnotatedVisitTargets.StateCalibration := by
  intro agenda result
  rw [forgetState,pairOfEvaluation,unaryCompositionEvaluation]
  simp only [work,results,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,stateNumber,Nat.unpair_pair]
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  simp only [Matrix.cons_val_zero]
  rw [agendaCalibration]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitForgetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitForgetProof
