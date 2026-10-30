module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantWeight
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomial

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.NumericDeterminant

private theorem polynomial_fold_product {α : Type*} (l : List α)
    (f : α → DensePolynomial.Code) :
    DensePolynomial.value (l.foldr (fun i acc => DensePolynomial.mul (f i) acc)
      [RationalCode.one]) = (l.map (fun i => DensePolynomial.value (f i))).prod := by
  induction l with
  | nil => simp [DensePolynomial.value, RationalCode.value_one]
  | cons a l ih =>
    simpa only [List.foldr_cons, DensePolynomial.value_mul, List.map_cons, List.prod_cons] using
      congrArg (fun z => DensePolynomial.value (f a) * z) ih

private theorem polynomial_fold_sum {α : Type*} (l : List α)
    (f : α → DensePolynomial.Code) :
    DensePolynomial.value (l.foldr (fun i acc => DensePolynomial.add (f i) acc) []) =
      (l.map (fun i => DensePolynomial.value (f i))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa only [List.foldr_cons, DensePolynomial.value_add, List.map_cons, List.sum_cons] using
      congrArg (fun z => DensePolynomial.value (f a) + z) ih

theorem product_value (n : ℕ) (m : MatrixCode) (k : ℕ) :
    DensePolynomial.value (product n m k) =
      ∏ i ∈ Finset.range n, DensePolynomial.value (entry n m (digit n k i) i) := by
  rw [product, polynomial_fold_product, ← List.prod_toFinset _
    (show (List.range n).Nodup from List.nodup_range)]
  simp only [List.toFinset_range]

theorem determinant_value (n : ℕ) (m : MatrixCode) :
    DensePolynomial.value (determinant n m) =
      ∑ k ∈ Finset.range ((n + 2) ^ n), DensePolynomial.value (summand n m k) := by
  rw [determinant, polynomial_fold_sum,
    ← List.sum_toFinset _
      (show (List.range ((n + 2) ^ n)).Nodup from List.nodup_range)]
  simp only [List.toFinset_range]

theorem valid_iff (n k : ℕ) : valid n k = true ↔ ∀ i : Fin n, digit n k i.val < n := by
  simp only [valid, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

private theorem weight_nonzero_injective (n k : ℕ) (hw : RationalCode.value (weight n k) ≠ 0) :
    Function.Injective (fun i : Fin n => digit n k i.val) := by
  intro i j heq
  change digit n k i.val = digit n k j.val at heq
  by_contra hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  apply hw
  rw [weight_value]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Finset.prod_eq_zero (Finset.mem_range.mpr j.isLt)
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hlt)
    rw [pair_sign_value, heq]
    simp
  · apply Finset.prod_eq_zero (Finset.mem_range.mpr i.isLt)
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hgt)
    rw [pair_sign_value, heq]
    simp

private theorem nonzero_summand_permutation (n : ℕ) (m : MatrixCode) (k : ℕ)
    (hk : k < (n + 2) ^ n) (hn : DensePolynomial.value (summand n m k) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n),
      KroneckerIndex.index (n + 2) (fun i : Fin n => (σ i).val) = k := by
  classical
  have hv : valid n k = true := by
    by_contra hnot
    apply hn
    simp only [summand, if_neg hnot, DensePolynomial.value]
  have hw : RationalCode.value (weight n k) ≠ 0 := by
    intro hz
    apply hn
    rw [summand, if_pos hv, DensePolynomial.value_scale, hz, map_zero, zero_mul]
  let f : Fin n → Fin n := fun i => ⟨digit n k i.val, (valid_iff n k).mp hv i⟩
  have hi : Function.Injective f := by
    intro i j heq
    exact weight_nonzero_injective n k hw (congrArg Fin.val heq)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩
  refine ⟨σ, ?_⟩
  exact KroneckerIndex.index_digits n (n + 2) k (by omega) hk

private theorem permutation_summand (n : ℕ) (m : MatrixCode) (σ : Equiv.Perm (Fin n)) :
    DensePolynomial.value (summand n m
      (KroneckerIndex.index (n + 2) (fun i : Fin n => (σ i).val))) =
      ((σ.sign : ℤ) : Polynomial ℚ) * ∏ i : Fin n, value n m (σ i) i := by
  classical
  let k := KroneckerIndex.index (n + 2) (fun i : Fin n => (σ i).val)
  have hb : KroneckerIndex.Bounded (n + 2) (fun i : Fin n => (σ i).val) := by
    intro i
    change (σ i).val < n + 2
    have hi := (σ i).isLt
    omega
  have hd (i : Fin n) : digit n k i.val = (σ i).val :=
    congrFun (KroneckerIndex.digits_index n (n + 2) (by omega)
      (fun i : Fin n => (σ i).val) hb) i
  have hv : valid n k = true := (valid_iff n k).mpr fun i => by
    rw [hd i]
    exact (σ i).isLt
  rw [summand, if_pos hv, DensePolynomial.value_scale, permutation_weight n σ,
    product_value, Finset.prod_range, map_intCast]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hd i]
  rfl

theorem determinant_correct : Targets.numericDeterminantCorrect := by
  intro n m
  classical
  rw [determinant_value, Matrix.det_apply']
  symm
  apply Finset.sum_bij_ne_zero
    (fun (σ : Equiv.Perm (Fin n)) _ _ =>
      KroneckerIndex.index (n + 2) (fun i : Fin n => (σ i).val))
  · intro σ _ _
    apply Finset.mem_range.mpr
    apply KroneckerIndex.index_bound n (n + 2) (by omega)
    intro i
    change (σ i).val < n + 2
    have hi := (σ i).isLt
    omega
  · intro σ _ _ τ _ _ heq
    have hb (ρ : Equiv.Perm (Fin n)) :
        KroneckerIndex.Bounded (n + 2) (fun i : Fin n => (ρ i).val) := by
      intro i
      change (ρ i).val < n + 2
      have hi := (ρ i).isLt
      omega
    have hh := KroneckerIndex.index_injective n (n + 2) (by omega)
      (fun i : Fin n => (σ i).val) (fun i : Fin n => (τ i).val) (hb σ) (hb τ) heq
    apply Equiv.ext
    intro i
    exact Fin.ext (congrFun hh i)
  · intro k hk hnonzero
    obtain ⟨σ, hσ⟩ := nonzero_summand_permutation n m k (Finset.mem_range.mp hk) hnonzero
    refine ⟨σ, Finset.mem_univ σ, ?_, hσ⟩
    intro hz
    apply hnonzero
    rw [← hσ, permutation_summand, hz]
  · intro σ _ _
    exact (permutation_summand n m σ).symm

end LogicLineages.ModelsAlgebra.Differential.NumericDeterminant
