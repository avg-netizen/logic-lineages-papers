module
public import Mathlib.Tactic.FinCases
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.PrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.PrimitiveProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedExchangeCode NumberedExchangeCodeFieldsProof
open NumberedSyntaxBoundsPrimrecSupportProof NumberedHeadSignaturePrimrecProof
open NumberedExchangeCodePrimrecProof (LayerInput)
attribute [local irreducible] Primrec

theorem inputCoordinatePrimitive (n : Nat) (arity : Fin n → Nat) (i : Fin 19) :
    Primrec (fun p : LayerInput n => (ExchangeLayer.input n arity p).get i) := by
  have hwindow : Primrec (fun p : LayerInput n => (p.1 : List (Fin n) × List Ty)) := (Primrec.fst.comp Primrec.id)
  have hanswers : Primrec (fun p : LayerInput n => (p.2.2.2 : List Bool)) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
  have hxtag : Primrec (fun p : LayerInput n => (p.2.1.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
  have hxann : Primrec (fun p : LayerInput n => (p.2.1.2.1 : Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))
  have hxhead : Primrec (fun p : LayerInput n => (p.2.1.2.2.1 : HeadCode (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))))
  have hxlabel : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))))
  have hxtypes : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.2.1 : List Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))))))
  have hxfirst : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.2.2.1 : Code (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))))))
  have hxsecond : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.2.2.2 : Code (Fin n))) :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))))))
  have hytag : Primrec (fun p : LayerInput n => (p.2.2.1.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  have hyann : Primrec (fun p : LayerInput n => (p.2.2.1.2.1 : Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))
  have hyhead : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.1 : HeadCode (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))
  have hylabel : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))
  have hytypes : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.2.1 : List Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))))
  have hyfirst : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.2.2.1 : Code (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))))
  have hysecond : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.2.2.2 : Code (Fin n))) :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))))

  have hleft : Primrec (fun p : LayerInput n => p.2.2.2.getD 0 false) :=
    (Primrec.list_getD false).comp hanswers (Primrec.const 0)
  have hright : Primrec (fun p : LayerInput n => p.2.2.2.getD 3 false) :=
    (Primrec.list_getD false).comp hanswers (Primrec.const 3)
  have hroot : Primrec (fun p : LayerInput n =>
      headMove arity p.1.1 p.1.2 p.2.1.2.2.1 p.2.1.2.2.2.2.2.1
        p.2.2.1.2.2.1 p.2.2.1.2.2.2.2.2.1) :=
    (NumberedExchangeRootPrimrecProof.headMovePrimitive n arity).comp
      (hwindow.pair ((hxhead.pair hxfirst).pair (hyhead.pair hyfirst)))
  fin_cases i
  · simpa only [ExchangeLayer.NativeProof.input0] using (hxtag)
  · simpa only [ExchangeLayer.NativeProof.input1] using (Primrec.encode.comp hxann)
  · simpa only [ExchangeLayer.NativeProof.input2] using (Primrec.encode.comp hxhead)
  · simpa only [ExchangeLayer.NativeProof.input3] using (hxlabel)
  · simpa only [ExchangeLayer.NativeProof.input4] using (Primrec.encode.comp hxtypes)
  · simpa only [ExchangeLayer.NativeProof.input5] using (Primrec.encode.comp hxfirst)
  · simpa only [ExchangeLayer.NativeProof.input6] using (Primrec.encode.comp hxsecond)
  · simpa only [ExchangeLayer.NativeProof.input7] using (hytag)
  · simpa only [ExchangeLayer.NativeProof.input8] using (Primrec.encode.comp hyann)
  · simpa only [ExchangeLayer.NativeProof.input9] using (Primrec.encode.comp hyhead)
  · simpa only [ExchangeLayer.NativeProof.input10] using (hylabel)
  · simpa only [ExchangeLayer.NativeProof.input11] using (Primrec.encode.comp hytypes)
  · simpa only [ExchangeLayer.NativeProof.input12] using (Primrec.encode.comp hyfirst)
  · simpa only [ExchangeLayer.NativeProof.input13] using (Primrec.encode.comp hysecond)
  · simpa only [ExchangeLayer.NativeProof.input14] using ((Primrec.dom_bool Bool.toNat).comp hleft)
  · simpa only [ExchangeLayer.NativeProof.input15] using ((Primrec.dom_bool Bool.toNat).comp hright)
  · simpa only [ExchangeLayer.NativeProof.input16] using ((Primrec.dom_bool Bool.toNat).comp hroot)
  · simpa only [ExchangeLayer.NativeProof.input17] using (Primrec.encode.comp ((headResultPrimitive n).comp hxhead))
  · simpa only [ExchangeLayer.NativeProof.input18] using (Primrec.encode.comp ((headResultPrimitive n).comp hyhead))

theorem validPrimitive (n : Nat) : Primrec (TransparentExchangeLayer.validValue n) := by
  let V := List.Vector Nat 3
  let N := ExchangeNumericSuppliers.Node n
  let W := ExchangeNumericSuppliers.Window n
  have getP (i : Fin 3) : Primrec (fun v : V => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hn : Primrec (fun v : V => Encodable.decode (α := N) (v.get 0)) := Primrec.decode.comp (getP 0)
  have hw : Primrec (fun v : V => Encodable.decode (α := W) (v.get 2)) := Primrec.decode.comp (getP 2)
  have he : Primrec (fun _ : (V × N) × W => (1 : Nat)) := Primrec.const 1
  have hm := Primrec.option_map (hw.comp Primrec.fst) he.to₂
  have ho := Primrec.option_getD.comp (Primrec.option_bind hn hm.to₂) (Primrec.const 0)
  apply ho.of_eq
  intro v
  cases hn : Encodable.decode (α := N) (v.get 0) <;>
    cases hw : Encodable.decode (α := W) (v.get 2) <;>
    simp only [TransparentExchangeLayer.validValue,hn,hw,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

theorem fieldPrimitive (n : Nat) (arity : Fin n → Nat) (i : Fin 19) :
    Primrec (TransparentExchangeLayer.fieldValue n arity i) := by
  let V := List.Vector Nat 3
  let N := ExchangeNumericSuppliers.Node n
  let W := ExchangeNumericSuppliers.Window n
  let A := (V × N) × W
  have getP (i : Fin 3) : Primrec (fun v : V => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hn : Primrec (fun v : V => Encodable.decode (α := N) (v.get 0)) := Primrec.decode.comp (getP 0)
  have hw : Primrec (fun v : V => Encodable.decode (α := W) (v.get 2)) := Primrec.decode.comp (getP 2)
  have hv : Primrec (fun a : A => a.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun a : A => a.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun a : A => fields a.1.2.1) := (fieldsPrimitive n).comp (Primrec.fst.comp hp)
  have hy : Primrec (fun a : A => fields a.1.2.2) := (fieldsPrimitive n).comp (Primrec.snd.comp hp)
  have ha : Primrec (fun a : A =>
      ((NumberedMultisetNumeric.decodeNumbers (a.1.1.get 1)).getD []).map (fun value => value == 1)) :=
    ExchangeNumericSuppliers.PrimitiveProof.answersPrimitive.comp hv
  have he : Primrec (fun a : A => (ExchangeLayer.input n arity
      (a.2,fields a.1.2.1,fields a.1.2.2,
        ((NumberedMultisetNumeric.decodeNumbers (a.1.1.get 1)).getD []).map (fun value => value == 1))).get i) :=
    (inputCoordinatePrimitive n arity i).comp (Primrec.snd.pair (hx.pair (hy.pair ha)))
  have hm := Primrec.option_map (hw.comp Primrec.fst) he.to₂
  have ho := Primrec.option_getD.comp (Primrec.option_bind hn hm.to₂) (Primrec.const 0)
  apply ho.of_eq
  intro v
  cases hn : Encodable.decode (α := N) (v.get 0) <;>
    cases hw : Encodable.decode (α := W) (v.get 2) <;>
    simp only [TransparentExchangeLayer.fieldValue,hn,hw,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

theorem primitiveFields : Targets.PrimitiveFields := by
  intro n arity
  exact ⟨validPrimitive n,fieldPrimitive n arity⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.PrimitiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.PrimitiveProof
