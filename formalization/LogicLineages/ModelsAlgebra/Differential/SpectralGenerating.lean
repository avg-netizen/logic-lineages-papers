module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantTargets
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultant

open Polynomial

private theorem generating_degree_general {R : Type*} [CommRing R] (n : ℕ) (f : R[X]) :
    (generating n f).natDegree ≤ n - 1 := by
  classical
  unfold generating
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
  have hjn := (Finset.mem_Icc.mp hj).2
  calc
    _ ≤ j - (k.val + 1) := by
      change (C (MvPolynomial.C (f.coeff j) * MvPolynomial.X k) *
        X ^ (j - (k.val + 1))).natDegree ≤ j - (k.val + 1)
      rw [C_mul_X_pow_eq_monomial]
      exact natDegree_monomial_le _
    _ ≤ n - 1 := by omega

theorem generating_degree : Targets.spectralGeneratingDegree := generating_degree_general

private theorem expand_factor {K : Type*} [Field K] {n : ℕ}
    (root : Fin n → K) (i : Fin n) :
    (X - C (root i)) * SpectralProduct.rawPolynomial root i =
      ∏ j : Fin n, (X - C (root j)) :=
  Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun j => X - C (root j)) (Finset.mem_univ i)

private theorem evaluate_term {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (a : ℚ) (k : Fin n) (e : ℕ) (r : K) :
    Polynomial.eval₂ (MvPolynomial.map (algebraMap ℚ K)) (MvPolynomial.C r)
      (Polynomial.C (MvPolynomial.C a * MvPolynomial.X k) * Polynomial.X ^ e) =
      MvPolynomial.C (r ^ e * algebraMap ℚ K a) * MvPolynomial.X k := by
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [← map_pow]
  calc
    MvPolynomial.C (algebraMap ℚ K a) * MvPolynomial.X k * MvPolynomial.C (r ^ e) =
        MvPolynomial.C (r ^ e) * MvPolynomial.C (algebraMap ℚ K a) * MvPolynomial.X k := by
      ring
    _ = _ := by rw [← map_mul]

theorem generating_root_calibration : Targets.spectralGeneratingRootCalibration := by
  intro K _ _ n f root hd hf i
  classical
  have hquot : f.map (algebraMap ℚ K) /ₘ (X - C (root i)) =
      SpectralProduct.rawPolynomial root i := by
    rw [hf, ← expand_factor root i]
    exact mul_divByMonic_cancel_left _ (monic_X_sub_C _)
  have hcoeff (k : Fin n) : (SpectralProduct.rawPolynomial root i).coeff k.val =
      ∑ j ∈ Finset.Icc (k.val + 1) n,
        root i ^ (j - (k.val + 1)) * algebraMap ℚ K (f.coeff j) := by
    rw [← hquot, coeff_divByMonic_X_sub_C, natDegree_map, hd]
    simp only [coeff_map]
  unfold atRoot generating SpectralProduct.linearForm
  rw [eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval₂_finsetSum]
  simp_rw [evaluate_term]
  rw [← Finset.sum_mul, ← map_sum, ← hcoeff k]

end LogicLineages.ModelsAlgebra.Differential.SpectralResultant
