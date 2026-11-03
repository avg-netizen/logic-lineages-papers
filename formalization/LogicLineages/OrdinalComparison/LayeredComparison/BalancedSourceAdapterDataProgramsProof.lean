module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import LogicLineages.OrdinalComparison.RawNormCode
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Program
open BalancedEvaluation
open IntegerAlgorithms.Proof (ofNat_primitive negate_primitive add_primitive abs_primitive)

attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode

private theorem upperData_primitive : Primrec upperData :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option UpperData)))
    (Primrec.const (0,[],[]))

private theorem certificateData_primitive : Primrec certificateData :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option CertificateData)))
    (Primrec.const (0,[]))

attribute [local irreducible] upperData certificateData

private theorem stored_atoms_primitive : Primrec (fun E : Nat => (upperData E).2.2) :=
  Primrec.snd.comp (Primrec.snd.comp upperData_primitive)

private theorem stored_outside_primitive : Primrec (fun E : Nat => (upperData E).2.1) :=
  Primrec.fst.comp (Primrec.snd.comp upperData_primitive)

private theorem stored_constant_primitive : Primrec (fun E : Nat => (upperData E).1) :=
  Primrec.fst.comp upperData_primitive

private theorem subtract_primitive : Primrec₂ (fun a b : Int => a-b) := by
  apply (add_primitive.comp Primrec.fst (negate_primitive.comp Primrec.snd)).of_eq
  intro p
  exact (sub_eq_add_neg p.1 p.2).symm

private theorem sum_primitive : Primrec (fun xs : List Nat => xs.sum) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0 : Nat))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [ih]

private theorem maximum_primitive : Primrec BalancedRow.maximum :=
  Primrec.list_foldr Primrec.id (Primrec.const (0 : Nat))
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem upperAtoms_primitive : Primrec₂ upperAtoms :=
  Primrec.list_append.comp (stored_atoms_primitive.comp Primrec.fst)
    (stored_atoms_primitive.comp Primrec.snd)

theorem coefficients_primitive : Primrec₂ coefficients := by
  have hp : Primrec (fun a : AtomData => (a.1+1 : Int)) := by
    apply (ofNat_primitive.comp (Primrec.succ.comp Primrec.fst)).of_eq
    intro a
    simp
  have hleft : Primrec (fun E : Nat =>
      (upperData E).2.2.map (fun a => (a.1+1 : Int))) :=
    Primrec.list_map stored_atoms_primitive (hp.comp Primrec.snd).to₂
  have hright : Primrec (fun E : Nat =>
      (upperData E).2.2.map (fun a => -((a.1+1 : Int)))) :=
    Primrec.list_map stored_atoms_primitive
      (negate_primitive.comp (hp.comp Primrec.snd)).to₂
  exact Primrec.list_append.comp (hleft.comp Primrec.fst) (hright.comp Primrec.snd)

attribute [local irreducible] upperAtoms coefficients

theorem headCodes_primitive : Primrec₂ headCodes :=
  Primrec.list_map upperAtoms_primitive
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to₂

theorem originalConstant_primitive : Primrec₂ originalConstant :=
  subtract_primitive.comp
    (ofNat_primitive.comp (stored_constant_primitive.comp Primrec.fst))
    (ofNat_primitive.comp (stored_constant_primitive.comp Primrec.snd))

theorem outsideCoefficients_primitive :
    Primrec (fun p : Nat × Nat × Nat => outsideCoefficients p.1 p.2.1 p.2.2) := by
  let D := Nat × Nat × Nat
  have he : Primrec (fun p : D => (upperData p.2.1).2.1) :=
    stored_outside_primitive.comp (Primrec.fst.comp Primrec.snd)
  have hf : Primrec (fun p : D => (upperData p.2.2).2.1) :=
    stored_outside_primitive.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec (fun p : D × Nat =>
      ((upperData p.1.2.1).2.1.getD p.2 0 : Int)) :=
    ofNat_primitive.comp
      ((Primrec.list_getD (0 : Nat)).comp (he.comp Primrec.fst) Primrec.snd)
  have hright : Primrec (fun p : D × Nat =>
      ((upperData p.1.2.2).2.1.getD p.2 0 : Int)) :=
    ofNat_primitive.comp
      ((Primrec.list_getD (0 : Nat)).comp (hf.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (subtract_primitive.comp hleft hright).to₂

theorem factors_primitive : Primrec₂ factors := by
  have hstored : Primrec (fun p : Nat × AtomData => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.succ.comp
      ((Primrec.list_getD (0 : Nat)).comp (hstored.comp Primrec.fst) Primrec.snd)).to₂

theorem normOffset_primitive : Primrec normOffset :=
  Primrec.nat_add.comp
    ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp
      (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

attribute [local irreducible] headCodes originalConstant outsideCoefficients factors normOffset

theorem coefficientMass_primitive : Primrec₂ coefficientMass :=
  sum_primitive.comp
    (Primrec.list_map coefficients_primitive (abs_primitive.comp Primrec.snd).to₂)

theorem outsideMaximum_primitive :
    Primrec (fun p : Nat × Nat × Nat => outsideMaximum p.1 p.2.1 p.2.2) :=
  maximum_primitive.comp
    (Primrec.list_map outsideCoefficients_primitive (abs_primitive.comp Primrec.snd).to₂)

theorem multiplierMaximum_primitive :
    Primrec (fun p : Nat × Nat × Nat => multiplierMaximum p.1 p.2.1 p.2.2) := by
  let D := Nat × Nat × Nat
  have ha : Primrec (fun p : D => upperAtoms p.2.1 p.2.2) :=
    upperAtoms_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec₂ (fun p : D => fun a : AtomData => factors p.1 a) :=
    factors_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.nat_max.comp (Primrec.const 1)
    (maximum_primitive.comp (Primrec.list_flatMap ha hf))

theorem offsetMaximum_primitive : Primrec₂ offsetMaximum :=
  maximum_primitive.comp
    (Primrec.list_map upperAtoms_primitive (normOffset_primitive.comp Primrec.snd).to₂)

theorem normMaximum_primitive : Primrec₂ normMaximum :=
  maximum_primitive.comp (Primrec.list_map headCodes_primitive
    ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp Primrec.snd).to₂)

attribute [local irreducible] coefficientMass outsideMaximum multiplierMaximum
  offsetMaximum normMaximum

theorem threshold_primitive :
    Primrec (fun p : Nat × Nat × Nat => threshold p.1 p.2.1 p.2.2) := by
  let D := Nat × Nat × Nat
  have he : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun p : D => (originalConstant p.2.1 p.2.2).natAbs) :=
    abs_primitive.comp (originalConstant_primitive.comp he hf)
  have hc : Primrec (fun p : D => 2*coefficientMass p.2.1 p.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) (coefficientMass_primitive.comp he hf)
  have hout : Primrec (fun p : D =>
      4*outsideMaximum p.1 p.2.1 p.2.2+4*(originalConstant p.2.1 p.2.2).natAbs+4) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) outsideMaximum_primitive)
        (Primrec.nat_mul.comp (Primrec.const 4) hk)) (Primrec.const 4)
  have hab : Primrec (fun p : D =>
      multiplierMaximum p.1 p.2.1 p.2.2+offsetMaximum p.2.1 p.2.2+2) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp multiplierMaximum_primitive (offsetMaximum_primitive.comp he hf))
      (Primrec.const 2)
  have hn : Primrec (fun p : D => normMaximum p.2.1 p.2.2+2) :=
    Primrec.nat_add.comp (normMaximum_primitive.comp he hf) (Primrec.const 2)
  exact Primrec.nat_max.comp (Primrec.const 16)
    (Primrec.nat_max.comp hc (Primrec.nat_max.comp hout (Primrec.nat_max.comp hab hn)))

theorem lowerCertificate_primitive : Primrec lowerCertificate :=
  Primrec.fst.comp certificateData_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Program
