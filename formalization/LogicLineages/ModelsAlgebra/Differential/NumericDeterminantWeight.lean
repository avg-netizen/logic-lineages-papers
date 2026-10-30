module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantTargets
public import LogicLineages.ModelsAlgebra.Differential.RationalCode
public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndex
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.NumericDeterminant

private theorem rational_fold_product {α : Type*} (l : List α) (f : α → RationalCode.Code) :
    RationalCode.value (l.foldr (fun i acc => RationalCode.mul (f i) acc) RationalCode.one) =
      (l.map (fun i => RationalCode.value (f i))).prod := by
  induction l with
  | nil => simp [RationalCode.value_one]
  | cons a l ih =>
    simpa only [List.foldr_cons, RationalCode.value_mul, List.map_cons, List.prod_cons] using
      congrArg (fun z => RationalCode.value (f a) * z) ih

theorem pair_sign_value (a b : ℕ) :
    RationalCode.value (pairSign a b) =
      if a < b then (1 : ℚ) else if b < a then -1 else 0 := by
  unfold pairSign
  split_ifs <;> simp [RationalCode.value_one, RationalCode.value_neg, RationalCode.value_zero]

theorem weight_value (n k : ℕ) : RationalCode.value (weight n k) =
    ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j,
      RationalCode.value (pairSign (digit n k i) (digit n k j)) := by
  unfold weight
  rw [rational_fold_product, ← List.prod_toFinset _
    (show (List.range n).Nodup from List.nodup_range)]
  simp only [List.toFinset_range]
  apply Finset.prod_congr rfl
  intro j _
  rw [rational_fold_product, ← List.prod_toFinset _
    (show (List.range j).Nodup from List.nodup_range)]
  simp only [List.toFinset_range]

private theorem prod_Iio_nat {M : Type*} [CommMonoid M] (n : ℕ) (j : Fin n) (f : ℕ → M) :
    (∏ i ∈ Finset.Iio j, f i.val) = ∏ i ∈ Finset.range j.val, f i := by
  classical
  apply Finset.prod_bij (fun i _ => i.val)
  · intro i hi
    have hfin : i < j := Finset.mem_Iio.mp hi
    exact Finset.mem_range.mpr hfin
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    have hij := Finset.mem_range.mp hi
    refine ⟨⟨i, hij.trans j.isLt⟩, Finset.mem_Iio.mpr hij, rfl⟩
  · intro _ _
    rfl

theorem permutation_weight : Targets.numericDeterminantPermutationWeight := by
  intro n σ
  classical
  let k := KroneckerIndex.index (n + 2) (fun i : Fin n => (σ i).val)
  have hbound : KroneckerIndex.Bounded (n + 2) (fun i : Fin n => (σ i).val) := by
    intro i
    change (σ i).val < n + 2
    have hi := (σ i).isLt
    omega
  have hd (i : Fin n) : digit n k i.val = (σ i).val := by
    have he := KroneckerIndex.digits_index n (n + 2) (by omega)
      (fun i : Fin n => (σ i).val) hbound
    exact congrFun he i
  have hs : ((σ.sign : ℤ) : ℚ) =
      ∏ j : Fin n, ∏ i ∈ Finset.Iio j, (if σ i < σ j then (1 : ℚ) else -1) := by
    rw [σ.sign_eq_prod_prod_Iio]
    simp only [Units.coe_prod, Int.cast_prod, apply_ite, Units.val_one, Units.val_neg,
      Int.cast_one, Int.cast_neg]
  rw [hs, weight_value, Finset.prod_range]
  apply Finset.prod_congr rfl
  intro j _
  rw [← prod_Iio_nat n j]
  apply Finset.prod_congr rfl
  intro i hij
  rw [pair_sign_value, hd i, hd j]
  have hne : (σ i).val ≠ (σ j).val := by
    intro heq
    exact (ne_of_lt (Finset.mem_Iio.mp hij)) (σ.injective (Fin.ext heq))
  change (if (σ i).val < (σ j).val then (1 : ℚ)
    else if (σ j).val < (σ i).val then -1 else 0) =
      if (σ i).val < (σ j).val then (1 : ℚ) else -1
  by_cases hlt : (σ i).val < (σ j).val
  · simp [hlt]
  · have hgt : (σ j).val < (σ i).val := by omega
    simp [hlt, hgt]

end LogicLineages.ModelsAlgebra.Differential.NumericDeterminant
