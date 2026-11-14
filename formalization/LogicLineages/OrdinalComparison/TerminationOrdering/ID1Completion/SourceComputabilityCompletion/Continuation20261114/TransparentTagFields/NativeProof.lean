module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem rawCodeValues (v : List.Vector Nat 3) :
    evaluate sourceCode v = (Nat.unpair (v.get 0)).1 ∧
    evaluate targetCode v = (Nat.unpair (v.get 0)).2 := by
  constructor
  · change evaluate InternalUnpair.left (List.Vector.ofFn ![v.get 0]) = _
    rw [InternalEqualityTestEvaluationProof.vectorOne]
    exact (InternalUnpairEvaluationProof.exactUnpairEvaluation _).1
  · change evaluate InternalUnpair.right (List.Vector.ofFn ![v.get 0]) = _
    rw [InternalEqualityTestEvaluationProof.vectorOne]
    exact (InternalUnpairEvaluationProof.exactUnpairEvaluation _).2

theorem rawTagValues (v : List.Vector Nat 3) :
    evaluate sourceRawTag v = (Nat.unpair (Nat.unpair (v.get 0)).1).1 ∧
    evaluate targetRawTag v = (Nat.unpair (Nat.unpair (v.get 0)).2).1 := by
  constructor
  · change evaluate InternalUnpair.left (List.Vector.ofFn ![evaluate sourceCode v]) = _
    rw [(rawCodeValues v).1,InternalEqualityTestEvaluationProof.vectorOne]
    exact (InternalUnpairEvaluationProof.exactUnpairEvaluation _).1
  · change evaluate InternalUnpair.left (List.Vector.ofFn ![evaluate targetCode v]) = _
    rw [(rawCodeValues v).2,InternalEqualityTestEvaluationProof.vectorOne]
    exact (InternalUnpairEvaluationProof.exactUnpairEvaluation _).1

theorem decodedTag (n raw : Nat) (a : Code (Fin n))
    (h : Encodable.decode raw = some a) :
    (Nat.unpair raw).1 = (NumberedExchangeCodeFieldsProof.fields a).1 := by
  have hc := NumberedNumericDecodingProof.codeNumericSound n raw a h
  rw [← hc]
  cases a <;> simp only [codeNumber,Nat.unpair_pair,NumberedExchangeCodeFieldsProof.fields]

theorem decodedNodeTags (n raw : Nat) (p : ExchangeNumericSuppliers.Node n)
    (h : Encodable.decode raw = some p) :
    (Nat.unpair (Nat.unpair raw).1).1 = (NumberedExchangeCodeFieldsProof.fields p.1).1 ∧
    (Nat.unpair (Nat.unpair raw).2).1 = (NumberedExchangeCodeFieldsProof.fields p.2).1 := by
  rw [Encodable.decode_prod_val] at h
  cases hx : Encodable.decode (α := Code (Fin n)) (Nat.unpair raw).1 with
  | none => simp only [hx,Option.bind_none] at h; cases h
  | some a =>
    cases hy : Encodable.decode (α := Code (Fin n)) (Nat.unpair raw).2 with
    | none => simp only [hx,hy,Option.bind_some,Option.map_none] at h; cases h
    | some c =>
      simp only [hx,hy,Option.bind_some,Option.map_some,Option.some.injEq] at h
      cases h
      exact ⟨decodedTag n _ a hx,decodedTag n _ c hy⟩

theorem nativeTags : Targets.NativeTags := by
  intro n arity V hV v
  simp only [sourceTag,targetTag,evalBranch,hV]
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
      have ht := decodedNodeTags n (v.get 0) p hn
      simp only [TransparentExchangeLayer.validValue,TransparentExchangeLayer.fieldValue,hn,hw,
        show ¬(1 = 0) by decide,ite_false,ExchangeLayer.NativeProof.input0,ExchangeLayer.NativeProof.input7]
      exact ⟨(rawTagValues v).1.trans ht.1,(rawTagValues v).2.trans ht.2⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.NativeProof
