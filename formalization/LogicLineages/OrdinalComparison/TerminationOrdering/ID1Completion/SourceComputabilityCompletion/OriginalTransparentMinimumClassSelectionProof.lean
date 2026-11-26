module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumClassSelectionProof
open OriginalTransparentMinimum InternalOriginalUniformParameterLeaves
open NumberedQuotientPathPrimrecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

/-- Compile the original class predicate through its original context and Object
codecs, retaining the candidate as a separate argument throughout. -/
theorem classPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (classValue n arity) := by
  have getP (i : Fin 3) : Primrec (fun v : List.Vector Nat 3 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp (getP 2)))
  have ho : Primrec (fun v : List.Vector Nat 3 => parameterObject (v.get 0) (v.get 2)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp
      (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp (getP 2))) (getP 0))
  let Input := (List.Vector Nat 3 × OrdinaryArithmeticQuotient.Context n) × ContextUniform.Object
  have hd : Primrec (fun p : Input =>
      NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have hw : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hg : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hv : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n => p.1.1.1.get 1) :=
    (getP 1).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have ht := (ContextUniformPrimaryPrimitiveProof.classNumberTestPrimitive n arity).comp
    ((hw.pair (hg.pair Primrec.snd)).pair hv)
  have hb := (Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd ht.to₂)
  have hm := Primrec.option_map (ho.comp Primrec.fst) hb.to₂
  have hp := Primrec.option_getD.comp (Primrec.option_bind hc hm.to₂) (Primrec.const 0)
  apply hp.of_eq
  intro v
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 2)).1 <;>
    cases ho : parameterObject (v.get 0) (v.get 2) <;>
    simp only [classValue,decodedValue,hc,ho,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

theorem actualOriginalTransparentMinimumClassSelection :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumClassSelection := by
  intro n arity
  exact Proof.allPrimitiveFunctions 3 _ (classPrimitive n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumClassSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumClassSelectionProof
