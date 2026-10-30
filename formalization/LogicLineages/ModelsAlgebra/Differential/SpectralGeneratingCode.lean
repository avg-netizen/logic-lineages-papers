module

public import LogicLineages.ModelsAlgebra.Differential.SpectralOuterCode
public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode

open Polynomial

private theorem conditional_fold_value {α : Type*} (l : List α) (p : α → Prop)
    [DecidablePred p] (f : α → OuterCode) (a : OuterCode) :
    outerValue (l.foldr (fun i acc => if p i then outerAdd (f i) acc else acc) a) =
      (l.map (fun i => if p i then outerValue (f i) else 0)).sum + outerValue a := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hi : p i
    · simp only [List.foldr_cons, if_pos hi, outer_add_correct, ih,
        List.map_cons, if_pos hi, List.sum_cons, add_assoc]
    · simp only [List.foldr_cons, if_neg hi, ih,
        List.map_cons, if_neg hi, List.sum_cons, zero_add]

private theorem accumulator_fold_value {α : Type*} (l : List α)
    (f : α → OuterCode → OuterCode) (r : α → Polynomial (Polynomial ℚ))
    (hf : ∀ i a, outerValue (f i a) = r i + outerValue a) (a : OuterCode) :
    outerValue (l.foldr f a) = (l.map r).sum + outerValue a := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.foldr_cons, hf, ih, List.map_cons, List.sum_cons, add_assoc]

theorem generating_correct : Targets.spectralGeneratingCodeCorrect := by
  intro n B fc
  classical
  let term (k j : ℕ) := outerMonomial
    (BoxPolynomialCode.monomial (fc.getD j RationalCode.zero) (B ^ k)) (j - (k + 1))
  let row (k : ℕ) (a : OuterCode) := (List.range (n + 1)).foldr
    (fun j inner => if k + 1 ≤ j then outerAdd (term k j) inner else inner) a
  let contribution (k : ℕ) := ∑ j ∈ Finset.range (n + 1),
    if k + 1 ≤ j then outerValue (term k j) else 0
  have hrow (k : ℕ) (a : OuterCode) : outerValue (row k a) = contribution k + outerValue a := by
    have h := conditional_fold_value (List.range (n + 1)) (fun j => k + 1 ≤ j) (term k) a
    rw [← List.sum_toFinset _
      (show (List.range (n + 1)).Nodup from List.nodup_range)] at h
    simpa only [List.toFinset_range] using h
  have hgen := accumulator_fold_value (List.range n) row contribution hrow []
  change outerValue ((List.range n).foldr row []) = _
  rw [hgen]
  simp only [outerValue, OrderOneAlgorithm.inputValue, add_zero]
  rw [← List.sum_toFinset _ (show (List.range n).Nodup from List.nodup_range)]
  simp only [List.toFinset_range]
  rw [Finset.sum_range, SpectralResultant.generating, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ j ∈ Finset.range (n + 1),
    if k.val + 1 ≤ j then outerValue (term k.val j) else 0) = _
  rw [Polynomial.map_sum]
  have hsub : Finset.Icc (k.val + 1) n ⊆ Finset.range (n + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2)
  calc
    _ = ∑ j ∈ Finset.Icc (k.val + 1) n,
        if k.val + 1 ≤ j then outerValue (term k.val j) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro j hj hjnot
      apply if_neg
      intro hjlo
      exact hjnot (Finset.mem_Icc.mpr ⟨hjlo, Nat.le_of_lt_succ (Finset.mem_range.mp hj)⟩)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (Finset.mem_Icc.mp hj).1]
      change outerValue (outerMonomial
        (BoxPolynomialCode.monomial (fc.getD j RationalCode.zero) (B ^ k.val))
          (j - (k.val + 1))) = _
      rw [outer_monomial_correct,
        BoxPolynomialCode.monomial_calibration (fc.getD j RationalCode.zero) (B ^ k.val),
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
      apply congrArg (fun a : Polynomial ℚ =>
        (Polynomial.C a : Polynomial (Polynomial ℚ)) * Polynomial.X ^ (j - (k.val + 1)))
      rw [map_mul]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        KroneckerPolynomial.encode, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [DensePolynomial.coefficients fc j]

end LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
