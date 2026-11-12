module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedExpansion
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem expansionEvaluation (role typ raw parameter : Nat) :
    evaluate expansion (ofFn ![jobNumber role typ (Nat.pair raw parameter)]) =
      evaluate decorateAll (ofFn ![role,typ,raw,
        evaluate OriginalHereditaryExpansion.expansion (ofFn ![raw,parameter])]) := by
  unfold expansion
  simp only [originalJob,leftOfEvaluation,rightOfEvaluation,binaryCompositionEvaluation,
    OriginalHereditaryAnnotatedExpansionEvaluationProof.projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,jobNumber,Nat.unpair_pair]
  rfl

theorem nativeExpansion : OriginalHereditaryAnnotatedExpansionTargets.NativeExpansion := by
  intro n c role typ s
  rw [show OriginalHereditaryExpansion.jobNumber c s =
    Nat.pair (NumberedLeastCodeRepresentative.codeNumber s.code)
      (Nat.pair c (Encodable.encode s.context)) from rfl]
  rw [expansionEvaluation,OriginalHereditaryExpansionNativeProof.successorsCalibration,
    OriginalHereditaryAnnotatedExpansionScanProof.decorateAllEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
