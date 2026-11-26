module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.NativeProof
open NumberedUniformPackedDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem decodedCodeField (n raw : Nat) (q : RawPacked n)
    (h : Encodable.decode (α := RawPacked n) raw = some q) :
    Encodable.decode (α := NumberedAuxiliaryCoding.Code (Fin n)) (Nat.unpair raw).2 = some q.2 := by
  rw [Encodable.decode_prod_val] at h
  cases ht : Encodable.decode (α := Source.Ty) (Nat.unpair raw).1 with
  | none => simp only [ht,Option.bind_none] at h; cases h
  | some ty =>
    cases hc : Encodable.decode (α := NumberedAuxiliaryCoding.Code (Fin n)) (Nat.unpair raw).2 with
    | none => simp only [ht,hc,Option.bind_some,Option.map_none] at h; cases h
    | some code =>
      simp only [ht,hc,Option.bind_some,Option.map_some,Option.some.injEq] at h
      cases h
      exact hc

theorem nodeDecode (n source target : Nat) (a b : RawPacked n)
    (ha : Encodable.decode (α := RawPacked n) source = some a)
    (hb : Encodable.decode (α := RawPacked n) target = some b) :
    Encodable.decode (α := ExchangeNumericSuppliers.Node n)
      (Nat.pair (Nat.unpair source).2 (Nat.unpair target).2) = some (a.2,b.2) := by
  rw [Encodable.decode_prod_val,Nat.unpair_pair,decodedCodeField n source a ha,decodedCodeField n target b hb]
  rfl

theorem codeFieldValue (i : Fin 3) (v : List.Vector Nat 3) :
    evaluate (codeField i) v = (Nat.unpair (v.get i)).2 := by
  change evaluate InternalUnpair.right (List.Vector.ofFn ![v.get i]) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  exact (InternalUnpairEvaluationProof.exactUnpairEvaluation (v.get i)).2

theorem nodeValue (v : List.Vector Nat 3) : evaluate nodeCode v =
    Nat.pair (Nat.unpair (v.get 0)).2 (Nat.unpair (v.get 1)).2 := by
  change evaluate InternalPairing.pairing
    (List.Vector.ofFn ![evaluate (codeField 0) v,evaluate (codeField 1) v]) = _
  rw [codeFieldValue,codeFieldValue,InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalPairingEvaluationProof.exactPairingEvaluation _ _

theorem nativeStructural : Targets.NativeStructural := by
  intro n arity R D J V K hX hV hK v
  rw [structural,evalBranch,hV]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1 with
  | none =>
    simp only [validValue,hc,TypedPrimaryEdge.structuralValue,ite_true]
    rfl
  | some ctx =>
    cases ha : Encodable.decode (α := RawPacked n) (v.get 0) with
    | none =>
      simp only [validValue,hc,ha,TypedPrimaryEdge.structuralValue,ite_true]
      rfl
    | some a =>
      cases hb : Encodable.decode (α := RawPacked n) (v.get 1) with
      | none =>
        simp only [validValue,hc,ha,hb,TypedPrimaryEdge.structuralValue,ite_true]
        rfl
      | some b =>
        have hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (evaluate nodeCode v) = some (a.2,b.2) := by
          rw [nodeValue]
          exact nodeDecode n (v.get 0) (v.get 1) a b ha hb
        have hk : evaluate (windowCode K) v = Encodable.encode ctx.1 := by
          change evaluate K (List.Vector.ofFn ![v.get 2]) = _
          rw [hK]
          simp only [windowValue,List.Vector.get_ofFn,Matrix.cons_val_zero,hc,Option.map_some,Option.getD_some]
        simp only [validValue,hc,ha,hb,TypedPrimaryEdge.structuralValue,Nat.one_ne_zero,ite_false]
        change evaluate (ExchangeSelectedRecursor.exchange R D J)
          (List.Vector.ofFn ![evaluate nodeCode v,evaluate (windowCode K) v]) = _
        rw [hX]
        change ExchangeNumericSuppliers.valueAt n arity (evaluate nodeCode v) (evaluate (windowCode K) v) = _
        rw [hk]
        simp only [ExchangeNumericSuppliers.valueAt,hn,Encodable.encodek]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.NativeProof
