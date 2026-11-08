module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsDecoderProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof
open Source InternalOriginalUniformParameterLeaves
open NumberedQuotientPathPrimrecSupportProof

attribute [local irreducible] Primrec

/-- Composition through the ORIGINAL context and Object decoders. The finite
context-table decoder is the proved original decoder, not Primrec.decode. -/
theorem decodedValuePrimitive (n : Nat)
    (f : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object → Nat)
    (hf : Primrec f) :
    Primrec (fun v : List.Vector Nat 2 =>
      decodedValue n (fun ctx obj => f (ctx,obj)) (v.get 0) (v.get 1)) := by
  have getP (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp (getP 1)))
  have ho : Primrec (fun v : List.Vector Nat 2 => parameterObject (v.get 0) (v.get 1)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp
      (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp (getP 1))) (getP 0))
  have hb : Primrec (fun p : (List.Vector Nat 2 × OrdinaryArithmeticQuotient.Context n) ×
      ContextUniform.Object => f (p.1.2,p.2)) :=
    hf.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hm := Primrec.option_map (ho.comp Primrec.fst) hb.to₂
  have hp := Primrec.option_getD.comp (Primrec.option_bind hc hm.to₂) (Primrec.const 0)
  apply hp.of_eq
  intro v
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 <;>
    cases ho : parameterObject (v.get 0) (v.get 1) <;>
    simp only [decodedValue, hc, ho, Option.bind_none, Option.bind_some,
      Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]

theorem sourcePrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (sourceValue n arity) := by
  apply decodedValuePrimitive n (fun p =>
    (NumberedNumericCarrier.rawCarrierTest n arity p.1.1.1 p.1.1.2 p.2.1 p.2.2).toNat)
  exact (Primrec.dom_bool Bool.toNat).comp
    ((NumberedUniversePrimrecProof.rawCarrierPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))))

theorem targetPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (targetValue n arity) := by
  apply decodedValuePrimitive n (fun p =>
    (NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2).isSome.toNat)
  exact (Primrec.dom_bool Bool.toNat).comp
    (Primrec.option_isSome.comp
      ((NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd))

theorem representativePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (representativeValue n arity) := by
  apply decodedValuePrimitive n (fun p =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2).map
      (ContextUniformPrimary.representative arity p.1.1.1 p.1.1.2 p.2.1)).getD 0)
  let Input := OrdinaryArithmeticQuotient.Context n × ContextUniform.Object
  have hd : Primrec (fun p : Input =>
      NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have hw : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hg : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hr := (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
    (hw.pair (hg.pair Primrec.snd))
  exact Primrec.option_getD.comp (Primrec.option_map hd hr.to₂) (Primrec.const 0)

theorem memberPrimitive (n : Nat) : Primrec (memberValue n) := by
  apply decodedValuePrimitive n (fun p =>
    InternalStructuralEndpointGuard.membershipValue p.1.1.2 p.2.2)
  let Input := OrdinaryArithmeticQuotient.Context n × ContextUniform.Object
  have hd : Primrec (fun p : Input => NumberedNumericDecoding.decodeType p.2.2) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp (Primrec.snd.comp Primrec.snd)
  have hm : PrimrecPred (fun p : Input × Ty => p.2 ∈ p.1.1.1.2) :=
    (NumberedHeadWindowPrimrecProof.memberPrimitive Ty).comp Primrec.snd
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  apply ((Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd hm.decide.to₂)).of_eq
  intro p
  cases h : NumberedNumericDecoding.decodeType p.2.2 <;>
    simp only [InternalStructuralEndpointGuard.membershipValue, h,
      Option.any_none, Option.any_some, Bool.toNat_false]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof
