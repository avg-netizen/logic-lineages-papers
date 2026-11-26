module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeFilterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedUniformPackedDecoding InternalOriginalUniformParameterLeaves
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof

theorem nativeOriginal : Targets.NativeOriginal := by
  intro n arity H hH v
  rw [candidates,binaryCompositionEvaluation,OriginalClassCodes.NativeProof.nativeOriginal n arity H hH]
  have hgamma : evaluate OriginalClassCodes.gamma v = (Nat.unpair (v.get 1)).2 := by
    rw [OriginalClassCodes.gamma,rightOfEvaluation]
    rfl
  rw [hgamma]
  obtain ⟨Gamma,hg⟩ := OriginalTypedDecoderCodecProof.contextEncodingSurjective (Nat.unpair (v.get 1)).2
  have ho := OriginalTypedDecoderTargetLeafValuesProof.parameterObjectEncoded (v.get 0) (v.get 1) Gamma hg
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none =>
    simp only [OriginalClassCodes.classCodesValue,Continuation20261114.SeededPrimaryPool.candidatesValue,decodedValue,hc]
    exact NativeNumericProof.filterZero H _
  | some ctx =>
    cases hd : rawPackedDecode n arity Gamma (v.get 0) with
    | none =>
      simp only [OriginalClassCodes.classCodesValue,Continuation20261114.SeededPrimaryPool.candidatesValue,decodedValue,hc,ho,hd,Option.map_none,Option.getD_none]
      exact NativeNumericProof.filterZero H _
    | some q =>
      simp only [OriginalClassCodes.classCodesValue,Continuation20261114.SeededPrimaryPool.candidatesValue,decodedValue,hc,ho,hd,Option.map_some,Option.getD_some]
      rw [← hg]
      exact NativeFilterProof.filterOriginal n arity H hH Gamma _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeProof
