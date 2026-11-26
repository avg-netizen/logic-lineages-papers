module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportNativeProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedLeastCodeRepresentative
open OriginalRawObjectTransport OriginalRawObjectTransportEvaluationProof
open OriginalContextExtensionCalibrationProof OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualRawObjectTypedCalibration :
    OriginalRawObjectTransportTargets.ActualRawObjectTypedCalibration := by
  intro n arity Gamma sigma tau
  have ht := OriginalRawSyntaxTransportTypedProof.actualRawSyntaxTypedCalibration
    n arity [] Gamma sigma tau
  constructor
  · intro q
    rw [objectEncoding,shiftObjectEvaluation,objectEncoding]
    simp only [Nat.unpair_pair,shiftPackedEvaluation,packedNumber,Nat.unpair_pair]
    rw [contextEncoding]
    have hq := ht.1 q
    change evaluate shiftRaw (List.Vector.ofFn ![0,codeNumber (termCode q)]) = _ at hq
    rw [hq]
    simp only [Nat.succ_eq_add_one,Nat.add_comm 1]
    rfl
  constructor
  · intro q
    rw [objectEncoding,eraseObjectEvaluation,objectEncoding]
    simp only [Nat.unpair_pair,contextEncoding,Nat.succ_sub_one,Nat.unpair_pair,
      erasePackedEvaluation,packedNumber,Nat.unpair_pair]
    have hq := ht.2.1 q
    change evaluate eraseRaw (List.Vector.ofFn ![typeNumber sigma,0,codeNumber (termCode q)]) =
      codeNumber (termCode (substitute q (singleSubstitution (.bottom sigma)))) at hq
    rw [hq]
  · intro q
    rw [objectEncoding,rankObjectEvaluation]
    simp only [Nat.unpair_pair,rankPackedEvaluation,packedNumber,Nat.unpair_pair]
    exact ht.2.2 q

/-- Native cancellation is deliberately separate from the internal supplier. -/
theorem nativeCancellation (d input : Nat) :
    evaluate eraseObjectRaw
      (List.Vector.ofFn ![evaluate shiftObjectRaw (List.Vector.ofFn ![d,input])]) = input := by
  rw [shiftObjectEvaluation,eraseObjectEvaluation]
  simp only [Nat.unpair_pair]
  rw [Nat.add_comm 1,Nat.add_sub_cancel]
  simp only [Nat.unpair_pair]
  rw [shiftPackedEvaluation,erasePackedEvaluation]
  simp only [Nat.unpair_pair]
  rw [OriginalRawSyntaxTransportCancellationProof.actualRawSyntaxNativeCancellation]
  rw [Nat.pair_unpair,Nat.pair_unpair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportNativeProof
