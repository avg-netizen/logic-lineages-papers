module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.PrimitiveProof
attribute [local irreducible] Primrec

theorem rankPrimitive (n : Nat) : Primrec (rankValue n) := by
  let V := List.Vector Nat 2
  have h0 : Primrec (fun v : V => v.get 0) := Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  have hn : Primrec (fun v : V => Encodable.decode (α := Node n) (v.get 0)) := Primrec.decode.comp h0
  have hr : Primrec (fun p : Node n => NumberedLeastCodeRepresentative.codeNumber p.1) :=
    (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.fst
  exact (Primrec.option_getD.comp (Primrec.option_map hn (hr.comp Primrec.snd).to₂) (Primrec.const 0)).of_eq
    (by intro v; rfl)

theorem depsPrimitive (n : Nat) : Primrec (depsValue n) := by
  let V := List.Vector Nat 2
  have h0 : Primrec (fun v : V => v.get 0) := Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  have hn : Primrec (fun v : V => Encodable.decode (α := Node n) (v.get 0)) := Primrec.decode.comp h0
  have hd : Primrec (fun p : Node n =>
      (NumberedExchangeCodeFieldsProof.dependencies p).map Encodable.encode) :=
    Primrec.list_map (NumberedExchangeCodeFieldsProof.dependenciesPrimitive n)
      (Primrec.encode.comp Primrec.snd).to₂
  have hlist := Primrec.option_getD.comp (Primrec.option_map hn (hd.comp Primrec.snd).to₂) (Primrec.const [])
  exact (NumberedListCodecPrimrecProof.encoderPrimitive.comp hlist).of_eq (by intro v; rfl)

theorem answersPrimitive : Primrec (fun v : List.Vector Nat 3 =>
    ((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map (fun value => value == 1)) := by
  have h1 : Primrec (fun v : List.Vector Nat 3 => v.get 1) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const 1)
  have hl := Primrec.option_getD.comp (NumberedListCodecPrimrecProof.decoderPrimitive.comp h1) (Primrec.const [])
  have he : Primrec (fun p : List.Vector Nat 3 × Nat => p.2 == 1) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 1)).decide.of_eq
      (by intro p; exact (Bool.beq_eq_decide_eq p.2 1).symm)
  exact Primrec.list_map hl he.to₂

theorem layerPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (layerValue n arity) := by
  let V := List.Vector Nat 3
  let A := (V × Node n) × Window n
  have getP (i : Fin 3) : Primrec (fun v : V => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hn : Primrec (fun v : V => Encodable.decode (α := Node n) (v.get 0)) :=
    Primrec.decode.comp (getP 0)
  have hw : Primrec (fun v : V => Encodable.decode (α := Window n) (v.get 2)) :=
    Primrec.decode.comp (getP 2)
  have hv : Primrec (fun a : A => a.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun a : A => a.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun a : A => NumberedExchangeCodeFieldsProof.fields a.1.2.1) :=
    (NumberedExchangeCodeFieldsProof.fieldsPrimitive n).comp (Primrec.fst.comp hp)
  have hy : Primrec (fun a : A => NumberedExchangeCodeFieldsProof.fields a.1.2.2) :=
    (NumberedExchangeCodeFieldsProof.fieldsPrimitive n).comp (Primrec.snd.comp hp)
  have ha : Primrec (fun a : A =>
      ((NumberedMultisetNumeric.decodeNumbers (a.1.1.get 1)).getD []).map (fun value => value == 1)) :=
    answersPrimitive.comp hv
  have hcalc : Primrec (fun a : A =>
      (NumberedExchangeCodePrimrecProof.layer n arity
        (a.2,NumberedExchangeCodeFieldsProof.fields a.1.2.1,
          NumberedExchangeCodeFieldsProof.fields a.1.2.2,
          ((NumberedMultisetNumeric.decodeNumbers (a.1.1.get 1)).getD []).map (fun value => value == 1))).toNat) :=
    (Primrec.dom_bool Bool.toNat).comp
      ((NumberedExchangeCodePrimrecProof.layerPrimitive n arity).comp (Primrec.snd.pair (hx.pair (hy.pair ha))))
  have hm := Primrec.option_map (hw.comp Primrec.fst) hcalc.to₂
  have hb := Primrec.option_bind hn hm.to₂
  have ho := Primrec.option_getD.comp hb (Primrec.const 0)
  apply (Primrec.succ.comp ho).of_eq
  intro v
  cases hn : Encodable.decode (α := Node n) (v.get 0) <;>
    cases hw : Encodable.decode (α := Window n) (v.get 2) <;>
    simp only [layerValue,layerAt,hn,hw,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
      Encodable.encode_some,Encodable.encode_nat,Nat.succ_eq_add_one]

theorem nativePrimitiveSuppliers : Targets.NativePrimitiveSuppliers := by
  intro n arity
  exact ⟨rankPrimitive n,depsPrimitive n,layerPrimitive n arity⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.PrimitiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.PrimitiveProof
