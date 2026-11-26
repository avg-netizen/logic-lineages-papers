module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.EncodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.NativeProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric

theorem actualHead (n : Nat) (V : Program 3) (side : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hv : evaluate V v = 1) (hc : evaluate (TransparentChildFields.rawCode side) v = codeNumber c) :
    evaluate (TransparentMetadataFields.head V side) v =
      headNumber (NumberedExchangeCodeFieldsProof.fields c).2.2.1 := by
  rw [TransparentMetadataFields.head,TransparentMetadataFields.guarded,evalBranch,hv]
  simp only [show ¬(1=0) by decide,ite_false]
  exact EncodedMetadataFields.NativeProof.headOfCode n side v c hc

theorem actualFirst (n : Nat) (V : Program 3) (side : Bool) (v : List.Vector Nat 3) (c : Code (Fin n))
    (hv : evaluate V v = 1) (hc : evaluate (TransparentChildFields.rawCode side) v = codeNumber c) :
    evaluate (TransparentChildFields.first V side) v =
      codeNumber (NumberedExchangeCodeFieldsProof.fields c).2.2.2.2.2.1 := by
  rw [TransparentChildFields.first,evalBranch,hv]
  simp only [show ¬(1=0) by decide,ite_false]
  have h := (TransparentChildFields.NativeProof.rawValues side v).1
  rw [hc] at h
  exact h.trans (TransparentChildFields.NativeProof.canonicalChildren n c).1

theorem actualBody (n : Nat) (arity : Fin n → Nat) (V : Program 3) (v : List.Vector Nat 3)
    (p : ExchangeNumericSuppliers.Node n) (window : ExchangeNumericSuppliers.Window n)
    (hv : evaluate V v = 1)
    (hn : Encodable.decode (v.get 0) = some p) (hw : Encodable.decode (v.get 2) = some window) :
    evaluate (body n arity V) v =
      (NumberedExchangeCode.headMove arity window.1 window.2
        (NumberedExchangeCodeFieldsProof.fields p.1).2.2.1 (NumberedExchangeCodeFieldsProof.fields p.1).2.2.2.2.2.1
        (NumberedExchangeCodeFieldsProof.fields p.2).2.2.1 (NumberedExchangeCodeFieldsProof.fields p.2).2.2.2.2.2.1).toNat := by
  have hp := TransparentChildFields.NativeProof.decodedNodeCodes n (v.get 0) p hn
  have hs : evaluate (TransparentChildFields.rawCode false) v = codeNumber p.1 :=
    (TransparentTagFields.NativeProof.rawCodeValues v).1.trans hp.1
  have ht : evaluate (TransparentChildFields.rawCode true) v = codeNumber p.2 :=
    (TransparentTagFields.NativeProof.rawCodeValues v).2.trans hp.2
  have hwin := EncodingProof.windowComponents n (v.get 2) window hw
  have hsymbols : evaluate symbols v = numbersNumber (window.1.map Fin.val) := by
    rw [symbols,leftOfEvaluation]
    exact hwin.1
  have htypes : evaluate types v = numbersNumber (window.2.map typeNumber) := by
    rw [types,rightOfEvaluation]
    exact hwin.2
  let gs : Fin 6 → Program 3 := ![TransparentMetadataFields.head V false,TransparentChildFields.first V false,
    TransparentMetadataFields.head V true,TransparentChildFields.first V true,symbols,types]
  have hargs : (ofFn (fun i => evaluate (gs i) v)) =
      ofFn ![headNumber (NumberedExchangeCodeFieldsProof.fields p.1).2.2.1,
        codeNumber (NumberedExchangeCodeFieldsProof.fields p.1).2.2.2.2.2.1,
        headNumber (NumberedExchangeCodeFieldsProof.fields p.2).2.2.1,
        codeNumber (NumberedExchangeCodeFieldsProof.fields p.2).2.2.2.2.2.1,
        numbersNumber (window.1.map Fin.val),numbersNumber (window.2.map typeNumber)] := by
    apply List.Vector.ext
    intro i
    fin_cases i
    · exact actualHead n V false v p.1 hv hs
    · exact actualFirst n V false v p.1 hv hs
    · exact actualHead n V true v p.2 hv ht
    · exact actualFirst n V true v p.2 hv ht
    · exact hsymbols
    · exact htypes
  change evaluate (OriginalHeadMove.headMove n arity) (ofFn (fun i => evaluate (gs i) v)) = _
  rw [hargs]
  exact OriginalHeadMove.NativeProof.nativeHeadMove n arity window.1 window.2 _ _ _ _

theorem nativeField : Targets.NativeField := by
  intro n arity V hV v
  rw [move,evalBranch,hV]
  cases hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) with
  | none => simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,ite_true,constantEvaluation]
  | some p =>
    cases hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
    | none => simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,ite_true,constantEvaluation]
    | some window =>
      have hv : evaluate V v = 1 := by rw [hV]; simp only [TransparentExchangeLayer.validValue,hn,hw]
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,
        show ¬(1=0) by decide,ite_false,ExchangeLayer.NativeProof.input16]
      exact actualBody n arity V v p window hv hn hw

theorem nativeFields : Targets.NativeFields := by
  intro n arity U V hU hV
  have hS : ∀ i v, evaluate (suppliers n arity U V i) v = TransparentExchangeLayer.fieldValue n arity i v := by
    intro i v
    by_cases hi : i=16
    · subst i
      simpa only [suppliers,ite_true] using nativeField n arity V hV v
    · simpa only [suppliers,if_neg hi] using hU i v
  exact ResultStructuralFields.NativeProof.nativeFields n arity (suppliers n arity U V) V hS hV

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.NativeProof
