module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Continuation20261114
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open NumberedNumericDecoding

theorem typeTotal (raw : Nat) :
    Encodable.decode (α := Source.Ty) raw = some (NumberedTypeCodecPrimrec.typeEquiv.symm raw) := rfl

theorem packedDecode (n raw : Nat) :
    (Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) raw).isSome =
      (decodeCode n (Nat.unpair raw).2).isSome := by
  have hp : Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) raw =
      (Encodable.decode (α := Source.Ty) (Nat.unpair raw).1).bind
        (fun ty => (Encodable.decode (α := NumberedAuxiliaryCoding.Code (Fin n)) (Nat.unpair raw).2).map (Prod.mk ty)) :=
    Encodable.decode_prod_val raw
  rw [hp,typeTotal]
  change ((decodeCode n (Nat.unpair raw).2).map (Prod.mk (NumberedTypeCodecPrimrec.typeEquiv.symm (Nat.unpair raw).1))).isSome = _
  cases decodeCode n (Nat.unpair raw).2 <;> rfl

theorem contextAtValue (n : Nat) (v : List.Vector Nat 3) :
    evaluate (contextAt n) v = (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1).isSome.toNat := by
  change evaluate (OriginalDecodedContextValidity.contextGuard n)
    (ofFn ![evaluate (InternalApplicationCertificateConstructors.leftOf (.projection 2)) v]) = _
  rw [OriginalDecodedContextValidity.NativeProof.nativeContext]
  change (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
    (evaluate InternalUnpair.left (ofFn ![v.get 2]))).isSome.toNat = _
  rw [leftEvaluation]
  rfl

theorem packedAtValue (n : Nat) (i : Fin 3) (v : List.Vector Nat 3) :
    evaluate (packedAt n i) v = (Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get i)).isSome.toNat := by
  change evaluate (OriginalCodeValidityGuard.check n)
    (ofFn ![evaluate (InternalApplicationCertificateConstructors.rightOf (.projection i)) v]) = _
  rw [OriginalCodeValidityGuard.NativeProof.nativeValidity,packedDecode]
  change (decodeCode n (evaluate InternalUnpair.right (ofFn ![v.get i]))).isSome.toNat = _
  rw [rightEvaluation]
  rfl

theorem nativeValid : Targets.NativeValid := by
  intro n v
  simp only [valid,conjunctionEvaluation,contextAtValue,packedAtValue,InstalledExchangeRecursor.validValue]
  cases Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1 <;>
    cases Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 0) <;>
    cases Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 1) <;> rfl

theorem contextCodeValue (n : Nat) (v : List.Vector Nat 1) :
    evaluate (contextCodeGuard n) v =
      (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 0)).1).isSome.toNat := by
  change evaluate (OriginalDecodedContextValidity.contextGuard n) (ofFn ![evaluate InternalUnpair.left v]) = _
  rw [OriginalDecodedContextValidity.NativeProof.nativeContext]
  change (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (evaluate InternalUnpair.left v)).isSome.toNat = _
  rw [leftEvaluation]

theorem windowProjection (v : List.Vector Nat 1) :
    evaluate (.composition InternalUnpair.left (fun _ : Fin 1 => InternalUnpair.left)) v =
      (Nat.unpair (Nat.unpair (v.get 0)).1).1 := by
  change evaluate InternalUnpair.left (ofFn ![evaluate InternalUnpair.left v]) = _
  rw [leftEvaluation]
  change (Nat.unpair (evaluate InternalUnpair.left v)).1 = _
  rw [leftEvaluation]

theorem nativeWindow : Targets.NativeWindow := by
  intro n v
  rw [window,evalBranch,contextCodeValue]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 0)).1 with
  | none =>
    simp only [Option.isSome_none,Bool.toNat_false,ite_true,InstalledExchangeRecursor.windowValue,hc,Option.map_none,Option.getD_none]
    rfl
  | some ctx =>
    simp only [Option.isSome_some,Bool.toNat_true,Nat.one_ne_zero,ite_false,windowProjection,
      InstalledExchangeRecursor.windowValue,hc,Option.map_some,Option.getD_some]
    have he := OriginalUniverseDecoderContextCodecProof.outerContextDecodeSound n (Nat.unpair (v.get 0)).1 ctx hc
    rw [← he,Encodable.encode_prod_val,Nat.unpair_pair]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.NativeProof
