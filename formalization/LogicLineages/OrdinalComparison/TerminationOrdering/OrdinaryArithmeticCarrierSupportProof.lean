module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierSupportProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier NumberedNumericCarrier QuotientDirectCarrier
open QuotientDirectPrimrecSupportProof

theorem listAllPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).all (g a)) := by
  have hfold : Primrec (fun a => (f a).foldr (fun b ok => g a b && ok) true) :=
    Primrec.list_foldr hf (Primrec.const true)
      (Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  apply hfold.of_eq
  intro a
  generalize f a = values
  induction values with
  | nil => rfl
  | cons b values ih => simp [List.foldr_cons,List.all_cons,ih]

theorem scalarPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : OrdinaryArithmeticQuotient.Context n × Nat => canonicalCarrierTest n arity p.1.1.1 p.1.1.2 Gamma p.2) :=
  (NumberedRepresentativePrimrecProof.canonicalCarrierPrimitive n arity Gamma).comp
    (g := fun p : OrdinaryArithmeticQuotient.Context n × Nat => (p.1.1,p.2))
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)

theorem listPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : OrdinaryArithmeticQuotient.Context n × List Nat => listCarrierTest n arity p.1.1.1 p.1.1.2 Gamma p.2) :=
  listAllPrimitive Primrec.snd
    ((scalarPrimitive n arity Gamma).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem decodedScalarPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (scalarValue n arity Gamma) := by
  have hg (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hd := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp (hg 0)
  have hb := (scalarPrimitive n arity Gamma).comp (Primrec.snd.pair ((hg 1).comp Primrec.fst))
  exact (Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd hb.to₂)

theorem decodedListPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (listValue n arity Gamma) := by
  have hg (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hd := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp (hg 0)
  have hl : Primrec (fun p : List.Vector Nat 2 × OrdinaryArithmeticQuotient.Context n =>
      (Encodable.decode (α := List Nat) (p.1.get 1)).any
        (listCarrierTest n arity p.2.1.1 p.2.1.2 Gamma)) :=
    optionAnyPrimitive (Primrec.decode.comp ((hg 1).comp Primrec.fst))
      ((listPrimitive n arity Gamma).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
  exact (Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd hl.to₂)

theorem optionAnyTrue {A : Type} (o : Option A) (f : A → Bool) :
    o.any f = true ↔ ∃ a, o = some a ∧ f a = true := by
  cases o <;> simp

theorem scalarCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (ctx value : Nat) :
    scalarValue n arity Gamma (List.Vector.ofFn ![ctx,value]) = 1 ↔ encodedScalar n arity Gamma ctx value := by
  simp only [scalarValue,OrdinaryArithmeticQuotientProof.boolNatOne,optionAnyTrue,
    List.Vector.get_ofFn,Matrix.cons_val_zero]
  rfl

theorem listCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (ctx value : Nat) :
    listValue n arity Gamma (List.Vector.ofFn ![ctx,value]) = 1 ↔ encodedList n arity Gamma ctx value := by
  simp only [listValue,OrdinaryArithmeticQuotientProof.boolNatOne,optionAnyTrue,
    List.Vector.get_ofFn,Matrix.cons_val_zero]
  constructor
  · rintro ⟨context,hc,values,hv,ht⟩
    exact ⟨context,values,hc,hv,ht⟩
  · rintro ⟨context,values,hc,hv,ht⟩
    exact ⟨context,hc,values,hv,ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierSupportProof
