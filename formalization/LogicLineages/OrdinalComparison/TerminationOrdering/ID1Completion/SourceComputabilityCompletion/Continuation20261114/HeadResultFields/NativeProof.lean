module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem resultOfCode (n : Nat) (target : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hc : evaluate (TransparentChildFields.rawCode target) v = codeNumber c) :
    evaluate OriginalHeadResult.headResult
      (List.Vector.ofFn ![evaluate (TransparentMetadataFields.headRaw target) v]) =
    Encodable.encode (Source.SourceMarkedSyntax.headResult
      (NumberedAuxiliaryDecoding.decodeHead (NumberedExchangeCodeFieldsProof.fields c).2.2.1)) := by
  rw [EncodedMetadataFields.NativeProof.headOfCode n target v c hc]
  exact OriginalHeadResult.NativeProof.nativeHeadResult n _

theorem zeroResult : evaluate OriginalHeadResult.headResult (List.Vector.ofFn ![0]) = 0 :=
  OriginalHeadResult.NativeProof.nativeHeadResult 0 (.zero)

theorem nativeResults : Targets.NativeResults := by
  intro n arity V hV target v
  rw [result,unaryCompositionEvaluation]
  simp only [TransparentMetadataFields.head,TransparentMetadataFields.guarded,evalBranch,hV]
  cases hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) with
  | none =>
    simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,ite_true,constantEvaluation]
    exact zeroResult
  | some p =>
    cases hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
    | none =>
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,ite_true,constantEvaluation]
      exact zeroResult
    | some window =>
      have hp := TransparentChildFields.NativeProof.decodedNodeCodes n (v.get 0) p hn
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,
        show ¬(1 = 0) by decide,ite_false]
      cases target with
      | false =>
        simp only [Bool.false_eq_true,ite_false,ExchangeLayer.NativeProof.input17]
        have hc : evaluate (TransparentChildFields.rawCode false) v = codeNumber p.1 :=
          (TransparentTagFields.NativeProof.rawCodeValues v).1.trans hp.1
        exact resultOfCode n false v p.1 hc
      | true =>
        simp only [ite_true,ExchangeLayer.NativeProof.input18]
        have hc : evaluate (TransparentChildFields.rawCode true) v = codeNumber p.2 :=
          (TransparentTagFields.NativeProof.rawCodeValues v).2.trans hp.2
        exact resultOfCode n true v p.2 hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.NativeProof
