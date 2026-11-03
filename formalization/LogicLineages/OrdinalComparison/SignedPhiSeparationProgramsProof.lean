module
public import LogicLineages.OrdinalComparison.SignedPhiSeparationTargets
public import LogicLineages.OrdinalComparison.SignedShiftCollectionProgramsProof
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
open SignedShiftCollection
open SignedShiftCollection.Proof
open LayeredComparison.IntegerAlgorithms.Proof

attribute [local irreducible] Nat.sqrt Nat.unpair domainOffset collected
  greatestKey greatestShift leadingCoefficient

private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem subtraction_primitive : Primrec₂ (fun a b : Int => a - b) := by
  apply (add_primitive.comp Primrec.fst (negate_primitive.comp Primrec.snd)).of_eq
  intro p
  exact (sub_eq_add_neg p.1 p.2).symm

private theorem naturalSum_primitive : Primrec (fun xs : List Nat => xs.sum) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [ih]

private theorem integerSum_primitive : Primrec (fun xs : List Int => xs.sum) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0 : Int))
    (add_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem lowerRow_primitive : Primrec lowerRow := by
  have hrel : PrimrecRel (fun (a : Int × Nat) (k : Nat) => a.2 < k) :=
    Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (PrimrecRel.listFilter hrel).comp collected_primitive greatestKey_primitive

attribute [local irreducible] lowerRow

theorem lowerMass_primitive : Primrec lowerMass :=
  naturalSum_primitive.comp (Primrec.list_map lowerRow_primitive
    (abs_primitive.comp (Primrec.fst.comp Primrec.snd)).to₂)

attribute [local irreducible] lowerMass

theorem delta_primitive : Primrec delta :=
  Primrec.ite (Primrec.eq.comp collected_primitive
      (Primrec.const ([] : CommonHeadLargeRow.Row))) domainOffset_primitive
    (Primrec.nat_max.comp domainOffset_primitive
      (toNat_primitive.comp (subtraction_primitive.comp
        (add_primitive.comp (ofNat_primitive.comp lowerMass_primitive)
          (Primrec.const (1 : Int))) greatestShift_primitive)))

attribute [local irreducible] delta

theorem argument_primitive : Primrec₂ argument :=
  toNat_primitive.comp
    (add_primitive.comp (ofNat_primitive.comp Primrec.fst) Primrec.snd)

attribute [local irreducible] argument Phi

theorem value_primitive : Primrec₂ value := by
  have heach : Primrec₂ (fun p : Row × Nat => fun a : Int × Int =>
      a.1 * (Phi (argument p.2 a.2) : Int)) :=
    mul_primitive.comp (Primrec.fst.comp Primrec.snd)
      (ofNat_primitive.comp (Phi_primrec.comp
        (argument_primitive.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))))
  exact integerSum_primitive.comp (Primrec.list_map Primrec.fst heach)

attribute [local irreducible] value

theorem shiftedInput_primitive : Primrec₂ shiftedInput :=
  Primrec.nat_add.comp Primrec.snd (delta_primitive.comp Primrec.fst)

theorem rebasedInput_primitive : Primrec₂ rebasedInput :=
  Primrec.nat_add.comp Primrec.snd (Primrec.nat_sub.comp
    (delta_primitive.comp Primrec.fst) (domainOffset_primitive.comp Primrec.fst))

attribute [local irreducible] shiftedInput rebasedInput

theorem originalArguments_primitive : Primrec₂ originalArguments :=
  Primrec.list_map Primrec.fst
    (argument_primitive.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to₂

attribute [local irreducible] originalArguments

theorem shiftedArguments_primitive : Primrec₂ shiftedArguments :=
  originalArguments_primitive.comp Primrec.fst shiftedInput_primitive

theorem uniformPrimitiveRecursiveData : Targets.UniformPrimitiveRecursiveData :=
  ⟨SignedShiftCollection.Proof.uniformPrimitiveRecursiveData,
    lowerRow_primitive, lowerMass_primitive, delta_primitive, argument_primitive,
    value_primitive, shiftedInput_primitive, rebasedInput_primitive,
    originalArguments_primitive, shiftedArguments_primitive,
    value_primitive.comp Primrec.fst shiftedInput_primitive⟩

end LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
