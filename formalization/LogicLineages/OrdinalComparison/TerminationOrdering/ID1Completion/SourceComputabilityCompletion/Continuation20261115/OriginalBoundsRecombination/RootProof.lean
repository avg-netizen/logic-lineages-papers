module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.RootProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedSyntaxBoundsPrimrecSupportProof
open InternalAcceptanceCalibrationProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof

theorem rootImage (n : Nat) (code : Code (Fin n)) :
    evaluate (root n) (ofFn ![codeNumber code]) = Encodable.encode (rootBounds code) := by
  have hg : evaluate (OriginalCodeValidityGuard.check n) (ofFn ![codeNumber code]) = 1 := by
    rw [OriginalCodeValidityGuard.NativeProof.nativeValidity,NumberedNumericDecodingProof.codeRoundTrip]
    rfl
  rw [root,evalBranch,hg]
  simp only [Nat.one_ne_zero,ite_false]
  cases code <;>
    simp only [Continuation20261114.OriginalHeadEncodingBridge.NativeProof.chooseEvaluation,
      codeNumber,List.Vector.get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair,
      pairOfEvaluation,constantEvaluation,leftOfEvaluation,rightEvaluation,
      rootBounds,Encodable.encode_prod_val]
  all_goals norm_num

theorem rootAccepted (n raw : Nat) (code : Code (Fin n)) (hc : decodeCode n raw = some code) :
    evaluate (root n) (ofFn ![raw]) = Encodable.encode (rootBounds code) := by
  have he := NumberedNumericDecodingProof.codeNumericSound n raw code hc
  rw [← he]
  exact rootImage n code
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.RootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.RootProof
