module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipLeafSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.SelectionProof
open Source InternalOriginalUniformParameterLeaves NumberedUniformPackedDecoding
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] Primrec

theorem verticesPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : (OrdinaryArithmeticQuotient.Context n × ContextUniform.Object) × RawPacked n =>
      ContextUniformPrimary.vertices arity p.1.1.1.1 p.1.1.1.2 p.1.2.1 p.2) :=
  (ContextUniformPrimaryPrimitiveProof.verticesPrimitive n arity).comp
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))

theorem countPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (countValue n arity) := by
  apply InternalOriginalUniformParameterLeavesPrimitiveProof.decodedValuePrimitive n
    (fun p => ((rawPackedDecode n arity p.2.1 p.2.2).map
      (fun q => (ContextUniformPrimary.vertices arity p.1.1.1 p.1.1.2 p.2.1 q).length)).getD 0)
  have hd := (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have hv := Primrec.list_length.comp (verticesPrimitive n arity)
  exact Primrec.option_getD.comp (Primrec.option_map hd hv.to₂) (Primrec.const 0)

theorem poolPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (poolValue n arity) := by
  apply InternalOriginalUniformParameterLeavesPrimitiveProof.decodedValuePrimitive n
    (fun p => ((rawPackedDecode n arity p.2.1 p.2.2).map
      (fun q => Membership.entriesCode (ContextUniformPrimary.vertices arity p.1.1.1 p.1.1.2 p.2.1 q))).getD 0)
  have hd := (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have hv := MembershipLeafSelectionProof.entriesPrimitive _ (verticesPrimitive n arity)
  exact Primrec.option_getD.comp (Primrec.option_map hd hv.to₂) (Primrec.const 0)

theorem edgePrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (edgeValue n arity) := by
  let V := List.Vector Nat 3
  let Ctx := OrdinaryArithmeticQuotient.Context n
  have getP (i : Fin 3) : Primrec (fun v : V => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp (getP 2)))
  have ha : Primrec (fun v : V => Encodable.decode (α := RawPacked n) (v.get 0)) :=
    Primrec.decode.comp (getP 0)
  have hb : Primrec (fun v : V => Encodable.decode (α := RawPacked n) (v.get 1)) :=
    Primrec.decode.comp (getP 1)
  have he : Primrec (fun p : ((V × Ctx) × RawPacked n) × RawPacked n =>
      (NumberedExchangeCode.packedCodeExchange arity p.1.1.2.1.1 p.1.1.2.1.2 p.1.2 p.2).toNat) :=
    (Primrec.dom_bool Bool.toNat).comp
      ((ContextUniformPrimaryPrimitiveProof.packedExchangePrimitive n arity).comp
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  have hm := Primrec.option_map (hb.comp (Primrec.fst.comp Primrec.fst)) he.to₂
  have hi := Primrec.option_bind (ha.comp Primrec.fst) hm.to₂
  have ho := Primrec.option_getD.comp (Primrec.option_bind hc hi.to₂) (Primrec.const 0)
  apply ho.of_eq
  intro v
  cases hc : Encodable.decode (α := Ctx) (Nat.unpair (v.get 2)).1 <;>
    cases ha : Encodable.decode (α := RawPacked n) (v.get 0) <;>
    cases hb : Encodable.decode (α := RawPacked n) (v.get 1) <;>
    simp only [edgeValue,hc,ha,hb,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

theorem supplierSelection : Targets.SupplierSelection := by
  intro n arity
  obtain ⟨C,hC⟩ := Proof.allPrimitiveFunctions 2 _ (countPrimitive n arity)
  obtain ⟨P,hP⟩ := Proof.allPrimitiveFunctions 2 _ (poolPrimitive n arity)
  obtain ⟨E,hE⟩ := Proof.allPrimitiveFunctions 3 _ (edgePrimitive n arity)
  exact ⟨C,P,E,hC,hP,hE⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.SelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.SelectionProof
