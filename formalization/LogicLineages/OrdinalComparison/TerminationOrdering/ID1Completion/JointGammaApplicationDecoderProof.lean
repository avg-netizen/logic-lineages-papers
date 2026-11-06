module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsDecoderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDecoderProof
open Source JointGammaApplication NumberedQuotientPathPrimrecSupportProof

attribute [local irreducible] Primrec

theorem decodedPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : DecodedInput => OrdinaryArithmeticApplication.decodedApplication n arity
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have hctx := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp Primrec.snd : Primrec (fun p : DecodedInput => p.2.1))
  have hs : Primrec (fun p : DecodedInput × OrdinaryArithmeticQuotient.Context n =>
      NumberedNumericDecoding.decodeType p.1.2.2.1) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ht : Primrec (fun p : (DecodedInput × OrdinaryArithmeticQuotient.Context n) × Ty =>
      NumberedNumericDecoding.decodeType p.1.1.2.2.2.1) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))))
  let Inner := ((DecodedInput × OrdinaryArithmeticQuotient.Context n) × Ty) × Ty
  have hb : Primrec (fun p : Inner => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun p : Inner => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hxy : Primrec (fun p : Inner => p.1.1.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb)))
  have happ : Primrec (fun p : Inner => NumberedNumericApplication.canonicalApplication n arity
      p.1.1.2.1.1 p.1.1.2.1.2 p.1.1.1.1 p.1.2 p.2 p.1.1.1.2.2.2.2.1 p.1.1.1.2.2.2.2.2) :=
    (JointGammaApplicationPrimitiveProof.actualOriginalApplicationPrimitive n arity).comp
      (((Primrec.fst.comp hc).pair (Primrec.fst.comp hb)).pair
        ((Primrec.snd.comp Primrec.fst).pair
          (Primrec.snd.pair ((Primrec.fst.comp hxy).pair (Primrec.snd.comp hxy)))))
  exact Primrec.option_bind hctx (Primrec.option_bind hs (Primrec.option_bind ht happ.to₂).to₂).to₂

theorem actualObjectApplicationPrimitive : JointGammaApplicationTargets.ActualObjectApplicationPrimitive := by
  intro n arity
  let Inner := ((List.Vector Nat 6 × ContextUniform.Object) × ContextUniform.Object) × ContextUniform.Object
  have getP (i : Fin 6) : Primrec (fun v : List.Vector Nat 6 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hv : Primrec (fun p : Inner => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hf : Primrec (fun p : Inner => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : Inner => p.1.2) := Primrec.snd.comp Primrec.fst
  have hz : Primrec (fun p : Inner => p.2) := Primrec.snd
  have happ := (decodedPrimitive n arity).comp
    ((Primrec.fst.comp hf).pair (((getP 0).comp hv).pair
      (((getP 1).comp hv).pair (((getP 2).comp hv).pair
        ((Primrec.snd.comp hf).pair (Primrec.snd.comp ha))))))
  have hguard : PrimrecPred (fun p : Inner => p.1.1.2.1 = p.1.2.1 ∧ p.1.1.2.1 = p.2.1) :=
    (Primrec.eq.comp (Primrec.fst.comp hf) (Primrec.fst.comp ha)).and
      (Primrec.eq.comp (Primrec.fst.comp hf) (Primrec.fst.comp hz))
  have hb := Primrec.and.comp hguard.decide
    (Primrec.eq.comp happ (Primrec.option_some.comp (Primrec.snd.comp hz))).decide
  have hdResult : Primrec (fun p : (List.Vector Nat 6 × ContextUniform.Object) × ContextUniform.Object =>
      Encodable.decode (α := ContextUniform.Object) (p.1.1.get 5)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp
      ((getP 5).comp (Primrec.fst.comp Primrec.fst))
  have hi := optionAnyPrimitive hdResult hb.to₂
  have hdArgument : Primrec (fun p : List.Vector Nat 6 × ContextUniform.Object =>
      Encodable.decode (α := ContextUniform.Object) (p.1.get 4)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp ((getP 4).comp Primrec.fst)
  have hj := optionAnyPrimitive hdArgument hi.to₂
  have hdFunction := JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp (getP 3)
  apply ((Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hdFunction hj.to₂)).of_eq
  intro v
  cases hf : Encodable.decode (α := ContextUniform.Object) (v.get 3) <;>
    cases ha : Encodable.decode (α := ContextUniform.Object) (v.get 4) <;>
      cases hz : Encodable.decode (α := ContextUniform.Object) (v.get 5)
  all_goals simp only [applicationValue,hf,ha,hz,OrdinaryArithmeticApplication.applicationValue,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Option.any_none,Option.any_some,Bool.toNat_false]
  split_ifs with h
  · rw [decide_eq_true h,Bool.true_and]
    rfl
  · rw [decide_eq_false h,Bool.false_and]
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDecoderProof
