module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem fieldsValue (n : Nat) (arity : Fin n → Nat) (U : Fin 19 → Program 3)
    (hU : ∀ i, i ≠ 14 → i ≠ 15 → ∀ v, evaluate (U i) v = fieldValue n arity i v)
    (v : List.Vector Nat 3) (p : ExchangeNumericSuppliers.Node n) (window : ExchangeNumericSuppliers.Window n)
    (hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) = some p)
    (hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) = some window)
    (i : Fin 19) :
    evaluate (fields U i) v =
      (ExchangeLayer.input n arity (window,NumberedExchangeCodeFieldsProof.fields p.1,
        NumberedExchangeCodeFieldsProof.fields p.2,
        ((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map (fun value => value == 1))).get i := by
  by_cases hi : i = 14
  · subst i
    simp only [fields,ite_true]
    rw [ExchangeLayer.NativeProof.input14]
    exact ExchangeAnswerSlots.NativeProof.nativeSlots 0 v
  · by_cases hj : i = 15
    · subst i
      simp only [fields,hi,ite_false,ite_true]
      rw [ExchangeLayer.NativeProof.input15]
      exact ExchangeAnswerSlots.NativeProof.nativeSlots 3 v
    · simp only [fields,hi,hj,ite_false]
      rw [hU i hi hj v]
      simp only [fieldValue,hn,hw]

theorem bodyValue (n : Nat) (arity : Fin n → Nat) (U : Fin 19 → Program 3)
    (hU : ∀ i, i ≠ 14 → i ≠ 15 → ∀ v, evaluate (U i) v = fieldValue n arity i v)
    (v : List.Vector Nat 3) (p : ExchangeNumericSuppliers.Node n) (window : ExchangeNumericSuppliers.Window n)
    (hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) = some p)
    (hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) = some window) :
    evaluate (body U) v =
      (NumberedExchangeCodePrimrecProof.layer n arity (window,NumberedExchangeCodeFieldsProof.fields p.1,
        NumberedExchangeCodeFieldsProof.fields p.2,
        ((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map (fun value => value == 1))).toNat := by
  let input := ExchangeLayer.input n arity (window,NumberedExchangeCodeFieldsProof.fields p.1,
    NumberedExchangeCodeFieldsProof.fields p.2,
    ((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map (fun value => value == 1))
  have hv : List.Vector.ofFn (fun i => evaluate (fields U i) v) = input := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    exact fieldsValue n arity U hU v p window hn hw i
  change evaluate ExchangeLayer.layer (List.Vector.ofFn (fun i => evaluate (fields U i) v)) = _
  rw [hv]
  exact ExchangeLayer.NativeProof.nativeCalibration n arity _

theorem nativeOptional : Targets.NativeOptional := by
  intro n arity U V hU hV v
  rw [optional,evalBranch,hV]
  cases hn : Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) with
  | none =>
    simp only [validValue,hn,ite_true,ExchangeNumericSuppliers.layerValue,ExchangeNumericSuppliers.layerAt]
    rfl
  | some p =>
    cases hw : Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
    | none =>
      simp only [validValue,hn,hw,ite_true,ExchangeNumericSuppliers.layerValue,ExchangeNumericSuppliers.layerAt]
      rfl
    | some window =>
      simp only [validValue,hn,hw,Nat.one_ne_zero,ite_false]
      change Nat.succ (evaluate (body U) v) = _
      rw [bodyValue n arity U hU v p window hn hw]
      simp only [ExchangeNumericSuppliers.layerValue,ExchangeNumericSuppliers.layerAt,hn,hw,
        Encodable.encode_some,Encodable.encode_nat,Nat.succ_eq_add_one]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.NativeProof
