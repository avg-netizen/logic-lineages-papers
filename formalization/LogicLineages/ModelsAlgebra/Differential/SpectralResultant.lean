module

public import LogicLineages.ModelsAlgebra.Differential.SpectralGenerating
public import Mathlib.Algebra.MvPolynomial.Degrees

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultant

open Polynomial

theorem resultant_calibration : Targets.spectralResultantCalibration := by
  intro K _ _ n f root _ hd hf
  classical
  let φ : MvPolynomial (Fin n) ℚ →+* MvPolynomial (Fin n) K :=
    MvPolynomial.map (algebraMap ℚ K)
  let g := (generating n f).map φ
  have hg : g.natDegree ≤ n - 1 :=
    natDegree_map_le.trans (generating_degree n f)
  have hF : (f.map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin n) ℚ)).map φ =
      ∏ i : Fin n, (X - C (MvPolynomial.C (root i))) := by
    calc
      _ = (f.map (algebraMap ℚ K)).map
          (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) := by
        rw [Polynomial.map_map, Polynomial.map_map]
        congr 1
        apply RingHom.ext
        intro q
        exact MvPolynomial.map_C (algebraMap ℚ K) q
      _ = _ := by
        rw [hf, Polynomial.map_prod]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hdegree : (∏ i : Fin n,
      (X - C (MvPolynomial.C (root i)) : Polynomial (MvPolynomial (Fin n) K))).natDegree = n := by
    rw [← hF, Polynomial.map_map, natDegree_map, hd]
  have hprod := resultant_prod_left Finset.univ
    (fun i : Fin n => (X - C (MvPolynomial.C (root i)) : Polynomial (MvPolynomial (Fin n) K)))
    g (n - 1) (by simp) hg
  rw [hdegree] at hprod
  unfold obstruction
  rw [← resultant_map_map, hF]
  change (∏ i : Fin n, (X - C (MvPolynomial.C (root i)))).resultant g n (n - 1) = _
  rw [hprod]
  unfold SpectralProduct.obstruction
  apply Finset.prod_congr rfl
  intro i _
  rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hg]
  change ((generating n f).map φ).eval (MvPolynomial.C (root i)) = _
  rw [← eval₂_eq_eval_map]
  exact generating_root_calibration K n f root hd hf i

private theorem linear_form_degree {K : Type*} [Field K] (n : ℕ) (p : Polynomial K)
    (i : Fin n) : (SpectralProduct.linearForm n p).degreeOf i ≤ 1 := by
  classical
  unfold SpectralProduct.linearForm
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X k) i (p.coeff k.val)).trans ?_
  rw [MvPolynomial.degreeOf_X]
  split_ifs <;> omega

private theorem product_degree {K : Type*} [Field K] (n : ℕ) (root : Fin n → K)
    (i : Fin n) : (SpectralProduct.obstruction root).degreeOf i ≤ n := by
  classical
  unfold SpectralProduct.obstruction
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      exact linear_form_degree n (SpectralProduct.rawPolynomial root k) i
    _ = n := by simp

theorem resultant_box : Targets.spectralResultantBox := by
  intro K _ _ n f root _ hm hd hf d hds i
  classical
  have hmap := resultant_calibration K n f root hm hd hf
  have hsupport : d ∈ (MvPolynomial.map (algebraMap ℚ K) (obstruction n f)).support := by
    rw [MvPolynomial.support_map_of_injective _ (algebraMap ℚ K).injective]
    exact hds
  rw [hmap] at hsupport
  exact (MvPolynomial.le_degreeOf_of_mem_support i hsupport).trans_lt
    ((product_degree n root i).trans_lt (Nat.lt_succ_self n))

end LogicLineages.ModelsAlgebra.Differential.SpectralResultant
