module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportSelectorProof OriginalRawSyntaxTransportEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem rawValues (target : Bool) (v : List.Vector Nat 3) :
    evaluate (firstRaw target) v =
      (if arityValue (evaluate (rawCode target) v) = 0 then 0 else firstValue (evaluate (rawCode target) v)) ∧
    evaluate (secondRaw target) v =
      (if arityValue (evaluate (rawCode target) v) = 2 then secondValue (evaluate (rawCode target) v) else 0) := by
  simp only [firstRaw,secondRaw,evalBranch,arityOfEvaluation,firstOfEvaluation,secondOfEvaluation,
    sameOfEvaluation,constantEvaluation]
  split_ifs <;> simp_all

theorem canonicalChildren (n : Nat) (c : Code (Fin n)) :
    (if arityValue (codeNumber c) = 0 then 0 else firstValue (codeNumber c)) =
      Encodable.encode (NumberedExchangeCodeFieldsProof.fields c).2.2.2.2.2.1 ∧
    (if arityValue (codeNumber c) = 2 then secondValue (codeNumber c) else 0) =
      Encodable.encode (NumberedExchangeCodeFieldsProof.fields c).2.2.2.2.2.2 := by
  change _ = codeNumber _ ∧ _ = codeNumber _
  cases c <;> simp [arityValue,firstValue,secondValue,tagValue,payloadValue,codeNumber,
    Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields]

theorem decodedNodeCodes (n raw : Nat) (p : ExchangeNumericSuppliers.Node n)
    (h : Encodable.decode raw = some p) :
    (Nat.unpair raw).1 = codeNumber p.1 ∧ (Nat.unpair raw).2 = codeNumber p.2 := by
  rw [Encodable.decode_prod_val] at h
  cases hx : Encodable.decode (α := Code (Fin n)) (Nat.unpair raw).1 with
  | none => simp only [hx,Option.bind_none] at h; cases h
  | some a =>
    cases hy : Encodable.decode (α := Code (Fin n)) (Nat.unpair raw).2 with
    | none => simp only [hx,hy,Option.bind_some,Option.map_none] at h; cases h
    | some c =>
      simp only [hx,hy,Option.bind_some,Option.map_some,Option.some.injEq] at h
      cases h
      exact ⟨(NumberedNumericDecodingProof.codeNumericSound n _ a hx).symm,
        (NumberedNumericDecodingProof.codeNumericSound n _ c hy).symm⟩

theorem nativeChildren : Targets.NativeChildren := by
  intro n arity V hV target v
  simp only [first,second,evalBranch,hV]
  cases hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) with
  | none =>
    simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,ite_true]
    constructor <;> rfl
  | some p =>
    cases hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
    | none =>
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,ite_true]
      constructor <;> rfl
    | some window =>
      have hp := decodedNodeCodes n (v.get 0) p hn
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,
        show ¬(1 = 0) by decide,ite_false]
      cases target with
      | false =>
        simp only [Bool.false_eq_true,ite_false,ExchangeLayer.NativeProof.input5,ExchangeLayer.NativeProof.input6]
        have hr : evaluate (rawCode false) v = codeNumber p.1 := (TransparentTagFields.NativeProof.rawCodeValues v).1.trans hp.1
        have hh := rawValues false v
        rw [hr] at hh
        exact ⟨hh.1.trans (canonicalChildren n p.1).1,hh.2.trans (canonicalChildren n p.1).2⟩
      | true =>
        simp only [ite_true,ExchangeLayer.NativeProof.input12,ExchangeLayer.NativeProof.input13]
        have hr : evaluate (rawCode true) v = codeNumber p.2 := (TransparentTagFields.NativeProof.rawCodeValues v).2.trans hp.2
        have hh := rawValues true v
        rw [hr] at hh
        exact ⟨hh.1.trans (canonicalChildren n p.2).1,hh.2.trans (canonicalChildren n p.2).2⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
