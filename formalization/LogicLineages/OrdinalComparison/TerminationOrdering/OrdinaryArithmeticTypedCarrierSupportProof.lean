module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierSupportProof
open Source NumberedRewriteReduction NumberedNumericCarrier NumberedLeastCodeRepresentative NumberedTypedCarrier
open OrdinaryArithmeticQuotient OrdinaryArithmeticTypedCarrier
open QuotientDirectPrimrecSupportProof
abbrev Input (n : Nat) := (List (Fin n) × List Ty) × Ty × Nat

theorem checkerPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Input n => typedCanonicalCarrierTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Input n => decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.2) :=
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      (g := fun p : Input n => (p.1,p.2.2)) (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have htype : Primrec (fun q : Packed (Fin n) arity Gamma => q.1) :=
    Primrec.fst.comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma)
  have ht : Primrec (fun p : Input n × Packed (Fin n) arity Gamma => decide (p.2.1=p.1.2.1)) :=
    (Primrec.eq.comp (htype.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).decide
  have hr : Primrec (fun p : Input n × Packed (Fin n) arity Gamma => representativeCode p.1.1.1 p.1.1.2 p.2) :=
    (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
      (g := fun p : Input n × Packed (Fin n) arity Gamma => (p.1.1,p.2))
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have he : Primrec (fun p : Input n × Packed (Fin n) arity Gamma => decide (representativeCode p.1.1.1 p.1.1.2 p.2=p.1.2.2)) :=
    (Primrec.eq.comp hr (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).decide
  apply (optionAnyPrimitive hd (Primrec.and.comp ht he).to₂).of_eq
  intro p
  unfold typedCanonicalCarrierTest
  cases decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.2 <;> simp

theorem wrapperPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (typedValue n arity Gamma) := by
  have hg (i : Fin 3) : Primrec (fun v : List.Vector Nat 3 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hd := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp (hg 0)
  have ht : Primrec (fun p : List.Vector Nat 3 × OrdinaryArithmeticQuotient.Context n =>
      (NumberedNumericDecoding.decodeType (p.1.get 1)).any (fun tau =>
        typedCanonicalCarrierTest n arity p.2.1.1 p.2.1.2 Gamma tau (p.1.get 2))) :=
    optionAnyPrimitive (NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp ((hg 1).comp Primrec.fst))
      ((checkerPrimitive n arity Gamma).comp
        (g := fun p : (List.Vector Nat 3 × OrdinaryArithmeticQuotient.Context n) × Ty =>
          (p.1.2.1,p.2,p.1.1.get 2))
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.snd.pair ((hg 2).comp (Primrec.fst.comp Primrec.fst))))).to₂
  exact (Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd ht.to₂)

theorem calibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context typ value : Nat) :
    typedValue n arity Gamma (List.Vector.ofFn ![context,typ,value])=1 ↔ encodedTyped n arity Gamma context typ value := by
  simp only [typedValue,OrdinaryArithmeticQuotientProof.boolNatOne,
    OrdinaryArithmeticCarrierSupportProof.optionAnyTrue,List.Vector.get_ofFn,Matrix.cons_val_zero]
  constructor
  · rintro ⟨ctx,hc,tau,ht,h⟩
    exact ⟨ctx,tau,hc,ht,h⟩
  · rintro ⟨ctx,tau,hc,ht,h⟩
    exact ⟨ctx,hc,tau,ht,h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierSupportProof
