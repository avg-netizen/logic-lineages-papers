module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalOriginalUniformParameterLeaves
open NumberedUniformPackedDecoding
open Continuation20261114 Continuation20261115
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem admittedValue (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H) (v : List.Vector Nat 2) :
    evaluate (admitted n H) v = targetValue n arity v :=
  OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H
    (OriginalDecodedContextValidity.contextGuard n) hH
    (OriginalDecodedContextValidity.NativeProof.nativeContext n) v

theorem nativeOriginal : Targets.NativeOriginal := by
  intro n arity H hH v
  rw [classCodes,InternalAcceptanceCalibrationProof.evalBranch,admittedValue n arity H hH,constantEvaluation]
  obtain ⟨Gamma,hg⟩ := OriginalTypedDecoderCodecProof.contextEncodingSurjective (Nat.unpair (v.get 1)).2
  have ho := OriginalTypedDecoderTargetLeafValuesProof.parameterObjectEncoded (v.get 0) (v.get 1) Gamma hg
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none => simp only [targetValue,classCodesValue,decodedValue,hc,ite_true]
  | some ctx =>
    cases hd : rawPackedDecode n arity Gamma (v.get 0) with
    | none => simp only [targetValue,classCodesValue,decodedValue,hc,ho,hd,Option.isSome_none,Bool.toNat_false,Option.map_none,Option.getD_none,ite_true]
    | some q =>
      have hq := TransparentCandidate.NativeProof.rawReencoding n arity Gamma (v.get 0)
      simp only [hd,Option.map_some,Option.getD_some,Option.isSome_some,Bool.toNat_true,ite_true] at hq
      have hctx := NativeCodecProof.contextCanonical n _ _ hc
      have hp : Nat.pair (Encodable.encode ctx) (Encodable.encode Gamma) = v.get 1 := by
        rw [hctx,hg,Nat.pair_unpair]
      have hv : v = ofFn ![Encodable.encode q,Nat.pair (Encodable.encode ctx) (Encodable.encode Gamma)] := by
        rw [hq,hp]
        apply List.Vector.ext
        intro i
        fin_cases i <;> rfl
      simp only [targetValue,classCodesValue,decodedValue,hc,ho,hd,Option.isSome_some,Bool.toNat_true,Nat.one_ne_zero,ite_false,Option.map_some,Option.getD_some]
      rw [hv]
      exact NativeCodecProof.frontendOriginal n arity ctx Gamma q
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeProof
