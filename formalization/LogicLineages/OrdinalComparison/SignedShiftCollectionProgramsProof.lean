module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import Mathlib.Data.List.Dedup

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection.Proof

open LayeredComparison.IntegerAlgorithms.Proof
  (ofNat_primitive negate_primitive add_primitive abs_primitive sign_primitive)

attribute [local irreducible] Nat.sqrt Nat.unpair

/-! These are programs for the displayed operations themselves. In particular,
the original row supplies the offset before any zero block is removed. -/

private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem subtract_primitive : Primrec₂ (fun a b : Int => a - b) := by
  apply (add_primitive.comp Primrec.fst (negate_primitive.comp Primrec.snd)).of_eq
  intro p
  exact (sub_eq_add_neg p.1 p.2).symm

private theorem maximum_primitive :
    Primrec (fun xs : List Nat => xs.foldl max 0) :=
  Primrec.list_foldl Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem integerSum_primitive : Primrec (fun xs : List Int => xs.sum) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0 : Int))
    (add_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- The literal right-fold implementation of natural-key deduplication. -/
private theorem dedup_primitive : Primrec (fun xs : List Nat => xs.dedup) := by
  have hm : PrimrecPred (fun p : Nat × List Nat => p.1 ∈ p.2) :=
    (Primrec.nat_lt.comp Primrec.list_idxOf
      (Primrec.list_length.comp Primrec.snd)).of_eq
        (fun _ => List.idxOf_lt_length_iff)
  have hs : Primrec₂ (fun (_ : List Nat) => fun p : Nat × List Nat =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2) :=
    (Primrec.ite (hm.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const ([] : List Nat)) hs).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons] at ih ⊢
    rw [ih, List.dedup_cons']

/-- Both the signed input block sum and the unchanged natural-key collector
use this same finite sum of equality-selected integer coefficients. -/
private theorem blockCoefficient_primitive {α : Type*} [Primcodable α]
    [DecidableEq α] : Primrec₂ (fun row : List (Int × α) => fun b : α =>
      (row.map (fun a => if a.2 = b then a.1 else 0)).sum) := by
  have heach : Primrec₂ (fun p : List (Int × α) × α => fun a : Int × α =>
      if a.2 = p.2 then a.1 else 0) :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  exact integerSum_primitive.comp (Primrec.list_map Primrec.fst heach)

private theorem naturalKeys_primitive : Primrec CommonHeadCollectedRow.keys :=
  dedup_primitive.comp
    (Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂)

private theorem naturalCoefficient_primitive :
    Primrec₂ CommonHeadCollectedRow.coefficient := blockCoefficient_primitive

attribute [local irreducible] CommonHeadCollectedRow.keys CommonHeadCollectedRow.coefficient

private theorem nonzeroFilter_primitive : Primrec (fun xs : CommonHeadLargeRow.Row =>
    xs.filter (fun a => a.1 != 0)) := by
  have hp : PrimrecPred (fun a : Int × Nat => a.1 ≠ 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : Int))).not
  apply (Primrec.listFilter hp).of_eq
  intro xs
  apply List.filter_congr
  intro a ha
  by_cases h : a.1 = 0 <;> simp [h]

/-- This proves effectiveness of `CommonHeadCollectedRow.collect` without
substituting a different collector or assuming an effectiveness supplier. -/
private theorem naturalCollect_primitive : Primrec CommonHeadCollectedRow.collect :=
  nonzeroFilter_primitive.comp
    (Primrec.list_map naturalKeys_primitive
      (Primrec.pair naturalCoefficient_primitive Primrec.snd).to₂)

attribute [local irreducible] CommonHeadCollectedRow.collect

theorem domainOffset_primitive : Primrec domainOffset :=
  maximum_primitive.comp
    (Primrec.list_map Primrec.id
      (toNat_primitive.comp
        (negate_primitive.comp (Primrec.snd.comp Primrec.snd))).to₂)

attribute [local irreducible] domainOffset

theorem rebaseKey_primitive : Primrec₂ rebaseKey :=
  toNat_primitive.comp
    (add_primitive.comp (ofNat_primitive.comp (domainOffset_primitive.comp Primrec.fst))
      Primrec.snd)

theorem originalShift_primitive : Primrec₂ originalShift :=
  subtract_primitive.comp (ofNat_primitive.comp Primrec.snd)
    (ofNat_primitive.comp (domainOffset_primitive.comp Primrec.fst))

attribute [local irreducible] rebaseKey originalShift

theorem rebaseRow_primitive : Primrec rebaseRow :=
  Primrec.list_map Primrec.id
    ((Primrec.fst.comp Primrec.snd).pair
      (rebaseKey_primitive.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂

attribute [local irreducible] rebaseRow

theorem collected_primitive : Primrec collected :=
  naturalCollect_primitive.comp rebaseRow_primitive

theorem coefficient_primitive : Primrec₂ coefficient := blockCoefficient_primitive

attribute [local irreducible] collected coefficient

theorem greatestKey_primitive : Primrec greatestKey :=
  maximum_primitive.comp
    (Primrec.list_map collected_primitive (Primrec.snd.comp Primrec.snd).to₂)

attribute [local irreducible] greatestKey

theorem greatestShift_primitive : Primrec greatestShift :=
  originalShift_primitive.comp Primrec.id greatestKey_primitive

attribute [local irreducible] greatestShift

theorem leadingCoefficient_primitive : Primrec leadingCoefficient :=
  coefficient_primitive.comp Primrec.id greatestShift_primitive

theorem uniformPrimitiveRecursiveData : Targets.UniformPrimitiveRecursiveData :=
  ⟨domainOffset_primitive, rebaseKey_primitive, originalShift_primitive,
    rebaseRow_primitive, collected_primitive, coefficient_primitive,
    greatestKey_primitive, greatestShift_primitive, leadingCoefficient_primitive⟩

end LogicLineages.OrdinalComparison.SignedShiftCollection.Proof
