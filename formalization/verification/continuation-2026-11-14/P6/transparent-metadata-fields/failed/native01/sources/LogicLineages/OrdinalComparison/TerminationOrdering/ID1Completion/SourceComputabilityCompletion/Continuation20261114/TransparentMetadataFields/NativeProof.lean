module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
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
    evaluate (headRaw target) v = Encodable.encode (NumberedExchangeCodeFieldsProof.fields c).2.2.1 := by
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
  change _ = typesNumber _
  simp only [typesRaw,choose,payload,evalBranch,sameOfEvaluation,constantEvaluation,
    leftOfEvaluation,rightOfEvaluation,hc]
  cases c <;> simp [codeNumber,Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields,
    typeNumber,headNumber,typesNumber] <;> rfl

theorem nativeMetadata : Targets.NativeMetadata := by
  intro n arity V hV target v
  simp only [annotation,head,label,types,guarded,evalBranch,hV]
  cases hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) with
  | none =>
    simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,ite_true]
    exact ⟨rfl,rfl,rfl,rfl⟩
  | some p =>
    cases hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
    | none =>
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,ite_true]
      exact ⟨rfl,rfl,rfl,rfl⟩
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
        exact ⟨annotationOfCode n false v p.1 hc,headOfCode n false v p.1 hc,
          labelOfCode n false v p.1 hc,typesOfCode n false v p.1 hc⟩
      | true =>
        simp only [ite_true,ExchangeLayer.NativeProof.input8,ExchangeLayer.NativeProof.input9,
          ExchangeLayer.NativeProof.input10,ExchangeLayer.NativeProof.input11]
        have hc : evaluate (TransparentChildFields.rawCode true) v = codeNumber p.2 :=
          (TransparentTagFields.NativeProof.rawCodeValues v).2.trans hp.2
        exact ⟨annotationOfCode n true v p.2 hc,headOfCode n true v p.2 hc,
          labelOfCode n true v p.2 hc,typesOfCode n true v p.2 hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.NativeProof
