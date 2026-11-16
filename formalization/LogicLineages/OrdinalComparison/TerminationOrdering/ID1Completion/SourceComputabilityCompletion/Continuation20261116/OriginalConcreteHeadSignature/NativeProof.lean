module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ArgumentsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.NativeProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem rawSignature (n : Nat) (arity : Fin n → Nat) (raw : Nat) :
    evaluate (signature n arity) (raw ::ᵥ nil) = OriginalTypedDecoder.headSignatureValue n arity raw := by
  have hc : evaluate (Continuation20261115.OriginalHeadDecoderValidity.check n) (raw ::ᵥ nil) =
      (decodeHeadNumber n raw).isSome.toNat :=
    Continuation20261115.OriginalHeadDecoderValidity.NativeProof.nativeDecoderValidity n raw
  rw [signature,evalBranch,hc]
  cases hd : decodeHeadNumber n raw with
  | none => simp [OriginalTypedDecoder.headSignatureValue,hd,constantEvaluation]
  | some h =>
    have hp : headParse n raw = some h := by
      rw [← Continuation20261115.OriginalHeadDecoderValidity.NativeProof.decoderEqualsParser]
      exact hd
    have hh := NumberedRawParserSoundnessSupportProof.headSound n raw h hp
    simp only [Option.isSome_some,Bool.toNat_true,one_ne_zero,if_false,succOfEvaluation,pairOfEvaluation]
    have hr : evaluate Continuation20261114.OriginalHeadResult.headResult (headNumber h ::ᵥ nil) =
        Encodable.encode (Source.SourceMarkedSyntax.headResult (decodeHead h)) :=
      Continuation20261114.OriginalHeadResult.NativeProof.nativeHeadResult n h
    rw [← hh,hr,ArgumentsProof.nativeArguments]
    rw [OriginalTypedDecoder.headSignatureValue,NumberedNumericDecodingSupportProof.headNumericRoundTrip]
    rw [Continuation20261114.OriginalHeadEncodingBridge.NativeProof.typeEncoding,Nat.add_comm]

theorem nativeSignature : Targets.NativeSignature := by
  intro n arity v
  have hv : v = v.get 0 ::ᵥ nil := by
    apply List.Vector.ext
    intro i
    fin_cases i
    rfl
  rw [hv]
  exact rawSignature n arity (v.get 0)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.NativeProof
