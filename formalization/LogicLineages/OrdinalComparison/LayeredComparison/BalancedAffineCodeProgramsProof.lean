module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeTargets
public import LogicLineages.OrdinalComparison.RawNormCode
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode.Proof
open BalancedEvaluation
attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode

private theorem upperData_primitive : Primrec upperData :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option UpperData)))
    (Primrec.const (0,[],[]))

private theorem certificateData_primitive : Primrec certificateData :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option CertificateData)))
    (Primrec.const (0,[]))

private theorem atomData_primitive : Primrec atomData :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option AtomData)))
    (Primrec.const (0,0,0,[]))

private theorem replicate_primitive : Primrec₂ (fun n a : Nat => List.replicate n a) := by
  apply (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst).to₂).of_eq
  intro p
  simp

private theorem numeral_primitive : Primrec (fun p : List Nat × Nat => numeral p.1 p.2) := by
  have hbase : Primrec (fun p : List Nat × Nat => 4*p.2) :=
    Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd
  have hupper : Primrec (fun p : (List Nat × Nat) × (Nat × List Nat) =>
      Encodable.encode ((p.1.2,List.replicate p.2.1 0,[]) : UpperData)) :=
    Primrec.encode.comp ((Primrec.snd.comp Primrec.fst).pair
      ((replicate_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).pair
        (Primrec.const [])))
  apply (Primrec.list_casesOn Primrec.fst hbase hupper.to₂).of_eq
  intro p
  cases p.1 <;> rfl

private def upperAddCode (k E F : Nat) : Nat :=
  Encodable.encode (((upperData E).1+(upperData F).1,
    (List.range k).map (fun j => (upperData E).2.1.getD j 0+(upperData F).2.1.getD j 0),
    (upperData E).2.2++(upperData F).2.2) : UpperData)

private theorem add_cons (k : Nat) (Γ : List Nat) (E F : Nat) :
    add (k::Γ) E F = upperAddCode k E F := rfl

private theorem upper_add_primitive : Primrec (fun p : Nat × Nat × Nat =>
    upperAddCode p.1 p.2.1 p.2.2) := by
  let D := Nat × Nat × Nat
  have he : Primrec (fun p : D => upperData p.2.1) :=
    upperData_primitive.comp (Primrec.fst.comp Primrec.snd)
  have hf : Primrec (fun p : D => upperData p.2.2) :=
    upperData_primitive.comp (Primrec.snd.comp Primrec.snd)
  have hce : Primrec (fun p : D => (upperData p.2.1).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp he)
  have hcf : Primrec (fun p : D => (upperData p.2.2).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hf)
  have hcoefficients : Primrec (fun p : D => (List.range p.1).map (fun j =>
      (upperData p.2.1).2.1.getD j 0+(upperData p.2.2).2.1.getD j 0)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (Primrec.nat_add.comp
        ((Primrec.list_getD (0 : Nat)).comp (hce.comp Primrec.fst) Primrec.snd)
        ((Primrec.list_getD (0 : Nat)).comp (hcf.comp Primrec.fst) Primrec.snd)).to₂
  exact Primrec.encode.comp
    ((Primrec.nat_add.comp (Primrec.fst.comp he) (Primrec.fst.comp hf)).pair
      (hcoefficients.pair (Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.snd.comp he))
        (Primrec.snd.comp (Primrec.snd.comp hf)))))

attribute [local irreducible] upperAddCode upperData certificateData atomData

private theorem add_primitive : Primrec (fun p : List Nat × Nat × Nat =>
    add p.1 p.2.1 p.2.2) := by
  let D := List Nat × Nat × Nat
  have hbase : Primrec (fun p : D => 4*Nat.pair p.2.1 p.2.2+2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))) (Primrec.const 2)
  have hupper : Primrec (fun p : D × (Nat × List Nat) =>
      upperAddCode p.2.1 p.1.2.1 p.1.2.2) :=
    upper_add_primitive.comp ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp Primrec.fst))
  apply (Primrec.list_casesOn Primrec.fst hbase hupper.to₂).of_eq
  intro p
  rcases p with ⟨Γ,E,F⟩
  cases Γ with
  | nil => rfl
  | cons k Γ => exact (add_cons k Γ E F).symm

private theorem fold_primitive : Primrec (fun p : List Nat × List Nat =>
    p.2.foldr (add p.1) (numeral p.1 0)) :=
  Primrec.list_foldr Primrec.snd
    (numeral_primitive.comp (Primrec.fst.pair (Primrec.const 0)))
    (add_primitive.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

private theorem scale_primitive : Primrec (fun p : List Nat × Nat × Nat =>
    scale p.1 p.2.1 p.2.2) :=
  fold_primitive.comp (Primrec.fst.pair
    (replicate_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))

private theorem combination_primitive :
    Primrec (fun p : List Nat × Nat × Nat × List Nat × List Nat =>
      combination p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let D := List Nat × Nat × Nat × List Nat × List Nat
  have hshape : Primrec (fun p : D => p.1) := Primrec.fst
  have hsize : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hconstant : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcoefficients : Primrec (fun p : D => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbasis : Primrec (fun p : D => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hterms : Primrec (fun p : D => (List.range p.2.1).map (fun j =>
      scale p.1 (p.2.2.2.1.getD j 0) (p.2.2.2.2.getD j 0))) :=
    Primrec.list_map (Primrec.list_range.comp hsize)
      (scale_primitive.comp ((hshape.comp Primrec.fst).pair
        (((Primrec.list_getD (0 : Nat)).comp (hcoefficients.comp Primrec.fst) Primrec.snd).pair
          ((Primrec.list_getD (0 : Nat)).comp (hbasis.comp Primrec.fst) Primrec.snd)))).to₂
  exact add_primitive.comp (hshape.pair
    ((numeral_primitive.comp (hshape.pair hconstant)).pair
      (fold_primitive.comp (hshape.pair hterms))))

private theorem lowerPart_primitive : Primrec (fun p : Nat × List Nat × Nat × Nat =>
    lowerPart p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := Nat × List Nat × Nat × Nat
  have hshape : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : D => upperData p.2.2.2) :=
    upperData_primitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hc : Primrec (fun p : D => certificateData p.2.2.1) :=
    certificateData_primitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact combination_primitive.comp (hshape.pair (Primrec.fst.pair
    ((Primrec.fst.comp he).pair ((Primrec.fst.comp (Primrec.snd.comp he)).pair
      (Primrec.snd.comp hc)))))

private theorem completeInput_primitive : Primrec (fun p : Nat × List Nat × Nat × Nat =>
    completeInput p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := Nat × List Nat × Nat × Nat
  have hshape : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : D => atomData p.2.2.2) :=
    atomData_primitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hc : Primrec (fun p : D => certificateData p.2.2.1) :=
    certificateData_primitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hhead : Primrec (fun p : D => (atomData p.2.2.2).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp ha)
  have hoffset : Primrec (fun p : D => (atomData p.2.2.2).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hfactors : Primrec (fun p : D => (atomData p.2.2.2).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hpositive : Primrec (fun p : D => (List.range p.1).map (fun j =>
      (atomData p.2.2.2).2.2.2.getD j 0+1)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (Primrec.succ.comp
        ((Primrec.list_getD (0 : Nat)).comp (hfactors.comp Primrec.fst) Primrec.snd)).to₂
  have hnorm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  exact combination_primitive.comp (hshape.pair (Primrec.fst.pair
    ((Primrec.nat_add.comp (hnorm.comp hhead) hoffset).pair
      (hpositive.pair (Primrec.snd.comp hc)))))

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨numeral_primitive, add_primitive, scale_primitive, combination_primitive,
    lowerPart_primitive, completeInput_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode.Proof
