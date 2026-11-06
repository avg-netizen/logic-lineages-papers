module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsDecoderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedPrimitiveProof
open Source NumberedAuxiliaryCoding NumberedUniformPackedDecoding JointGammaTyped
open NumberedQuotientPathPrimrecSupportProof

attribute [local irreducible] Primrec

theorem actualRawTypedCalibration : JointGammaTypedTargets.ActualRawTypedCalibration := by
  intro n arity symbols S Gamma tau value
  unfold rawTypedCarrier NumberedTypedCarrier.typedCanonicalCarrierTest
  rw [NumberedUniformPackedDecodingProof.rawUniverseCalibration]
  cases hd : NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma value with
  | none => rfl
  | some q =>
    simp only [Option.map_some,Option.any_some]
    rw [ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma q]
    rfl

theorem rawTypedPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Input n => rawTypedCarrier n arity p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Input n =>
      rawUniverseDecode n arity p.1.1.1 p.1.1.2 p.1.2 p.2.2) :=
    (NumberedUniformPackedDecodingProof.rawUniverseDecoderPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)))
  have hw : Primrec (fun p : Input n × RawPacked n => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hg : Primrec (fun p : Input n × RawPacked n => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec (fun p : Input n × RawPacked n => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hv : Primrec (fun p : Input n × RawPacked n => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hr := (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
    (hw.pair (hg.pair Primrec.snd))
  have hb := Primrec.and.comp
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) ht).decide
    (Primrec.eq.comp hr hv).decide
  apply (optionAnyPrimitive hd hb.to₂).of_eq
  intro p
  simp only [rawTypedCarrier,Bool.decide_and]

theorem actualOriginalTypedPrimitive : JointGammaTypedTargets.ActualOriginalTypedPrimitive := by
  intro n arity
  exact (rawTypedPrimitive n arity).of_eq (by
    intro p
    exact actualRawTypedCalibration n arity p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)

theorem actualObjectTypedPrimitive : JointGammaTypedTargets.ActualObjectTypedPrimitive := by
  intro n arity
  let Mid := (List.Vector Nat 3 × ContextUniform.Object) × OrdinaryArithmeticQuotient.Context n
  have getP (i : Fin 3) : Primrec (fun v : List.Vector Nat 3 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hctx : Primrec (fun p : Mid × Ty => p.1.2) := Primrec.snd.comp Primrec.fst
  have hobj : Primrec (fun p : Mid × Ty => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec (fun p : Mid × Ty => NumberedTypedCarrier.typedCanonicalCarrierTest n arity
      p.1.2.1.1 p.1.2.1.2 p.1.1.2.1 p.2 p.1.1.2.2) :=
    (actualOriginalTypedPrimitive n arity).comp
      (((Primrec.fst.comp hctx).pair (Primrec.fst.comp hobj)).pair
        (Primrec.snd.pair (Primrec.snd.comp hobj)))
  have ht : Primrec (fun p : Mid => NumberedNumericDecoding.decodeType (p.1.1.get 1)) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      ((getP 1).comp (Primrec.fst.comp Primrec.fst))
  have hi := optionAnyPrimitive ht hb.to₂
  have hc : Primrec (fun p : List.Vector Nat 3 × ContextUniform.Object =>
      Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (p.1.get 0)) :=
    (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp ((getP 0).comp Primrec.fst)
  have hj := optionAnyPrimitive hc hi.to₂
  have ho := JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp (getP 2)
  apply ((Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive ho hj.to₂)).of_eq
  intro v
  cases hd : Encodable.decode (α := ContextUniform.Object) (v.get 2) <;>
    simp only [typedValue,hd,OrdinaryArithmeticTypedCarrier.typedValue,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Option.any_none,Option.any_some,Bool.toNat_false] <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedPrimitiveProof
