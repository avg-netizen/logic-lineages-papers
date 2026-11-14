module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open TransparentMetadataFields
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem annotationOfCode (n : Nat) (target : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hc : evaluate (TransparentChildFields.rawCode target) v = codeNumber c) :
    evaluate (annotationRaw target) v = Encodable.encode (NumberedExchangeCodeFieldsProof.fields c).2.1 := by
  change _ = typeNumber _
  simp only [annotationRaw,choose,payload,evalBranch,sameOfEvaluation,constantEvaluation,
    leftOfEvaluation,rightOfEvaluation,hc]
  cases c <;> simp [codeNumber,Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields,
    typeNumber,headNumber,typesNumber] <;> rfl

theorem headOfCode (n : Nat) (target : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hc : evaluate (TransparentChildFields.rawCode target) v = codeNumber c) :
    evaluate (headRaw target) v = headNumber (NumberedExchangeCodeFieldsProof.fields c).2.2.1 := by
  change _ = headNumber _
  simp only [headRaw,choose,payload,evalBranch,sameOfEvaluation,constantEvaluation,
    leftOfEvaluation,rightOfEvaluation,hc]
  cases c <;> simp [codeNumber,Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields,
    typeNumber,headNumber,typesNumber] <;> rfl

theorem labelOfCode (n : Nat) (target : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hc : evaluate (TransparentChildFields.rawCode target) v = codeNumber c) :
    evaluate (labelRaw target) v = (NumberedExchangeCodeFieldsProof.fields c).2.2.2.1 := by
  simp only [labelRaw,choose,payload,evalBranch,sameOfEvaluation,constantEvaluation,
    leftOfEvaluation,rightOfEvaluation,hc]
  cases c <;> simp [codeNumber,Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields,
    typeNumber,headNumber,typesNumber] <;> rfl

theorem typesOfCode (n : Nat) (target : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hc : evaluate (TransparentChildFields.rawCode target) v = codeNumber c) :
    evaluate (typesRaw target) v = Encodable.encode (NumberedExchangeCodeFieldsProof.fields c).2.2.2.2.1 := by
  rw [← OriginalHeadEncodingBridge.NativeProof.nativeTypeListEncoding]
  simp only [typesRaw,choose,payload,evalBranch,sameOfEvaluation,constantEvaluation,
    leftOfEvaluation,rightOfEvaluation,hc]
  cases c <;> simp [codeNumber,Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields,
    typeNumber,headNumber,typesNumber] <;> rfl

theorem convertedHeadOfCode (n : Nat) (target : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hc : evaluate (TransparentChildFields.rawCode target) v = codeNumber c) :
    evaluate OriginalHeadEncodingBridge.encodeHead (List.Vector.ofFn ![evaluate (headRaw target) v]) =
      Encodable.encode (NumberedExchangeCodeFieldsProof.fields c).2.2.1 := by
  rw [headOfCode n target v c hc]
  exact OriginalHeadEncodingBridge.NativeProof.nativeHeadEncoding n _

theorem zeroHeadEncoding : evaluate OriginalHeadEncodingBridge.encodeHead (List.Vector.ofFn ![0]) = 0 :=
  OriginalHeadEncodingBridge.NativeProof.nativeHeadEncoding 0 (.zero)

theorem encodedHeadValue (V : Program 3) (target : Bool) (v : List.Vector Nat 3) :
    evaluate (EncodedMetadataFields.head V target) v =
      evaluate OriginalHeadEncodingBridge.encodeHead (List.Vector.ofFn ![evaluate (TransparentMetadataFields.head V target) v]) :=
  unaryCompositionEvaluation _ _ v

theorem nativeMetadata : Targets.NativeMetadata := by
  intro n arity V hV target v
  rw [encodedHeadValue]
  simp only [EncodedMetadataFields.annotation,EncodedMetadataFields.label,EncodedMetadataFields.types,
    TransparentMetadataFields.annotation,TransparentMetadataFields.head,TransparentMetadataFields.label,
    TransparentMetadataFields.types,TransparentMetadataFields.guarded,evalBranch,hV]
  cases hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) with
  | none =>
    simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,ite_true,constantEvaluation]
    exact ⟨rfl,zeroHeadEncoding,rfl,rfl⟩
  | some p =>
    cases hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
    | none =>
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,ite_true,constantEvaluation]
      exact ⟨rfl,zeroHeadEncoding,rfl,rfl⟩
    | some window =>
      have hp := TransparentChildFields.NativeProof.decodedNodeCodes n (v.get 0) p hn
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,
        show ¬(1 = 0) by decide,ite_false]
      cases target with
      | false =>
        simp only [Bool.false_eq_true,ite_false,ExchangeLayer.NativeProof.input1,ExchangeLayer.NativeProof.input2,
          ExchangeLayer.NativeProof.input3,ExchangeLayer.NativeProof.input4]
        have hc : evaluate (TransparentChildFields.rawCode false) v = codeNumber p.1 :=
          (TransparentTagFields.NativeProof.rawCodeValues v).1.trans hp.1
        exact ⟨annotationOfCode n false v p.1 hc,convertedHeadOfCode n false v p.1 hc,
          labelOfCode n false v p.1 hc,typesOfCode n false v p.1 hc⟩
      | true =>
        simp only [ite_true,ExchangeLayer.NativeProof.input8,ExchangeLayer.NativeProof.input9,
          ExchangeLayer.NativeProof.input10,ExchangeLayer.NativeProof.input11]
        have hc : evaluate (TransparentChildFields.rawCode true) v = codeNumber p.2 :=
          (TransparentTagFields.NativeProof.rawCodeValues v).2.trans hp.2
        exact ⟨annotationOfCode n true v p.2 hc,convertedHeadOfCode n true v p.2 hc,
          labelOfCode n true v p.2 hc,typesOfCode n true v p.2 hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.NativeProof
