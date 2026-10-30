module

public import LogicLineages.ModelsAlgebra.Differential.SpectralDescentTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralProduct

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralDescent

open Polynomial

private theorem expand_factor {K : Type*} [Field K] {n : ℕ}
    (root : Fin n → K) (i : Fin n) :
    (X - C (root i)) * SpectralProduct.rawPolynomial root i =
      ∏ j : Fin n, (X - C (root j)) :=
  Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun j => X - C (root j)) (Finset.mem_univ i)

private theorem linearForm_map {K : Type*} [Field K] (n : ℕ)
    (σ : K →+* K) (p : Polynomial K) :
    MvPolynomial.map σ (SpectralProduct.linearForm n p) =
      SpectralProduct.linearForm n (p.map σ) := by
  simp only [SpectralProduct.linearForm, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, Polynomial.coeff_map]

private theorem obstruction_fixed (f : Polynomial ℚ) (n : ℕ)
    (root : Fin n → f.SplittingField) (hr : Function.Injective root)
    (hf : f.map (algebraMap ℚ f.SplittingField) = ∏ i : Fin n, (X - C (root i)))
    (σ : f.SplittingField ≃ₐ[ℚ] f.SplittingField) :
    MvPolynomial.map σ.toRingHom (SpectralProduct.obstruction root) =
      SpectralProduct.obstruction root := by
  classical
  let K := f.SplittingField
  have hmapf : (f.map (algebraMap ℚ K)).map σ.toRingHom = f.map (algebraMap ℚ K) := by
    rw [Polynomial.map_map]
    congr 1
    ext q
    exact σ.commutes q
  have hroot (i : Fin n) : (f.map (algebraMap ℚ K)).eval (root i) = 0 := by
    rw [hf, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hσroot (i : Fin n) : ∃ j : Fin n, root j = σ (root i) := by
    have heval : (f.map (algebraMap ℚ K)).eval (σ (root i)) = 0 := by
      rw [← hmapf]
      calc
        ((f.map (algebraMap ℚ K)).map σ.toRingHom).eval (σ (root i)) =
            σ ((f.map (algebraMap ℚ K)).eval (root i)) :=
          Polynomial.eval_map_apply σ.toRingHom (root i)
        _ = 0 := by rw [hroot i, map_zero]
    rw [hf, eval_prod] at heval
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp heval
    refine ⟨j, ?_⟩
    exact (sub_eq_zero.mp (by simpa only [eval_sub, eval_X, eval_C] using hj)).symm
  choose g hg using hσroot
  have hginj : Function.Injective g := by
    intro i j hij
    apply hr
    apply σ.injective
    exact (hg i).symm.trans ((congrArg root hij).trans (hg j))
  let e : Fin n ≃ Fin n := Equiv.ofBijective g (⟨hginj, Finite.surjective_of_injective hginj⟩)
  have he (i : Fin n) : root (e i) = σ (root i) := hg i
  have hraw (i : Fin n) : (SpectralProduct.rawPolynomial root i).map σ.toRingHom =
      SpectralProduct.rawPolynomial root (e i) := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero (root (e i)))
    calc
      (X - C (root (e i))) * (SpectralProduct.rawPolynomial root i).map σ.toRingHom =
          ((X - C (root i)) * SpectralProduct.rawPolynomial root i).map σ.toRingHom := by
        rw [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, he]
        rfl
      _ = (f.map (algebraMap ℚ K)).map σ.toRingHom := by rw [expand_factor, ← hf]
      _ = f.map (algebraMap ℚ K) := hmapf
      _ = (X - C (root (e i))) * SpectralProduct.rawPolynomial root (e i) := by
        rw [expand_factor, hf]
  rw [SpectralProduct.obstruction, map_prod]
  simp_rw [linearForm_map, hraw]
  exact Equiv.prod_comp e (fun i => SpectralProduct.linearForm n (SpectralProduct.rawPolynomial root i))

theorem rational_descent : Targets.spectralObstructionRationalDescent := by
  intro f n root _hm hr hf
  classical
  let K := f.SplittingField
  have hsep : f.Separable := by
    apply (Polynomial.separable_map (algebraMap ℚ K)).mp
    rw [hf]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr hr
  letI : f.IsSplittingField ℚ K := Polynomial.IsSplittingField.splittingField f
  letI : IsGalois ℚ K := IsGalois.of_separable_splitting_field (F := ℚ) (E := K) hsep
  have hcoeff (d : Fin n →₀ ℕ) :
      (SpectralProduct.obstruction root).coeff d ∈ Set.range (algebraMap ℚ K) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    have h := congrArg (MvPolynomial.coeff d) (obstruction_fixed f n root hr hf σ)
    simp only [MvPolynomial.coeff_map] at h
    exact h
  have hmem : SpectralProduct.obstruction root ∈
      Set.range (MvPolynomial.map (algebraMap ℚ K)) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨d, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact hcoeff d
  obtain ⟨R, hR⟩ := hmem
  refine ⟨R, hR, ?_⟩
  intro hzero
  have hbad : SpectralProduct.obstruction root = 0 := by
    rw [← hR, hzero, map_zero]
  exact SpectralProduct.product_nonzero K n root hr hbad

end LogicLineages.ModelsAlgebra.Differential.SpectralDescent
