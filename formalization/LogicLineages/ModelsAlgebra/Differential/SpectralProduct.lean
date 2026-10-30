module

public import LogicLineages.ModelsAlgebra.Differential.SpectralProductTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralModel

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralProduct

open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_and_scale : Targets.spectralRawDegreeAndScale := by
  intro K _ n root hr i
  constructor
  · change (∏ j ∈ Finset.univ.erase i, (X - C (root j))).natDegree < n
    rw [Polynomial.natDegree_prod_of_monic (Finset.univ.erase i)
      (fun j => X - C (root j)) (fun j _ => monic_X_sub_C (root j))]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hi := i.isLt
    omega
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro hij
    exact (Finset.mem_erase.mp hj).1 (hr hij).symm

theorem linear_form_evaluation : Targets.spectralLinearFormEvaluation := by
  intro K F _ _ _ D n p a hp
  simp only [linearForm, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => algebraMap K F (p.coeff k) * ((D : F → F)^[k]) a) n]
  change _ = (Polynomial.aeval D.toLinearMap p) a
  rw [Polynomial.aeval_eq_sum_range' hp]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
    Module.End.pow_apply, Algebra.smul_def]
  rfl

theorem product_evaluation : Targets.spectralProductEvaluation := by
  intro K F _ _ _ D n root a hr
  rw [obstruction, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact linear_form_evaluation K F D n (rawPolynomial root i) a
    (degree_and_scale K n root hr i).1

private theorem normalization (D : Derivation K F F) (n : ℕ) (root : Fin n → K)
    (i : Fin n) (a : F) :
    LagrangeCoordinate.coordinate D root i a = (scale root i)⁻¹ •
      LinearOperator.coordinate D root i a := by
  simpa only [scale, Finset.prod_inv_distrib] using
    LagrangeCoordinate.normalization K F D n root i a

theorem product_nonvanishing : Targets.spectralProductNonvanishing := by
  intro K F _ _ _ D n root a hr
  rw [product_evaluation K F D n root a hr, Finset.prod_ne_zero_iff]
  have heach (i : Fin n) : LagrangeCoordinate.coordinate D root i a ≠ 0 ↔
      LinearOperator.coordinate D root i a ≠ 0 := by
    rw [normalization]
    have hu : IsUnit (scale root i)⁻¹ :=
      isUnit_iff_ne_zero.mpr (inv_ne_zero (degree_and_scale K n root hr i).2)
    exact not_congr hu.smul_eq_zero
  simp only [Finset.mem_univ, forall_const, ← heach]

theorem raw_coordinate_substitution : Targets.spectralRawCoordinateSubstitution := by
  intro K _ n root hr i
  let F := SpectralModel.ModelField K n
  let D := SpectralModel.derivation K n root
  let a := SpectralModel.point K n
  let x := SpectralModel.coordinateVariable K n
  have hcal := SpectralChange.calibration K F D n root a hr
  have hc : (fun j : Fin n => LagrangeCoordinate.coordinate D root j a) = x :=
    funext (SpectralModel.coordinates K n root hr)
  rw [hc] at hcal
  have hraw : LinearOperator.coordinate D root i a = scale root i • x i := by
    have hnorm := normalization D n root i a
    rw [SpectralModel.coordinates K n root hr] at hnorm
    have h := congrArg (fun v : F => scale root i • v) hnorm
    rw [smul_smul, mul_inv_cancel₀ (degree_and_scale K n root hr i).2, one_smul] at h
    exact h.symm
  apply (show Function.Injective (MvPolynomial.aeval x) from SpectralModel.variables_independent K n)
  rw [← AlgHom.comp_apply, hcal]
  rw [linear_form_evaluation K F D n (rawPolynomial root i) a
    (degree_and_scale K n root hr i).1]
  change LinearOperator.coordinate D root i a = _
  rw [hraw]
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.smul_def]

theorem product_substitution : Targets.spectralProductSubstitution := by
  intro K _ n root hr
  rw [obstruction, map_prod]
  simp_rw [raw_coordinate_substitution K n root hr]
  rw [Finset.prod_mul_distrib, ← map_prod]

theorem product_nonzero : Targets.spectralProductNonzero := by
  intro K _ n root hr hzero
  have h := congrArg (SpectralChange.toCoordinates root) hzero
  rw [product_substitution K n root hr, map_zero] at h
  have hs : (∏ i : Fin n, scale root i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (degree_and_scale K n root hr i).2)
  have hC : (MvPolynomial.C (∏ i : Fin n, scale root i) : MvPolynomial (Fin n) K) ≠ 0 := by
    intro hzero
    apply hs
    simpa only [MvPolynomial.coeff_zero_C, MvPolynomial.coeff_zero] using
      congrArg (MvPolynomial.coeff 0) hzero
  have hX : (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero i)
  exact mul_ne_zero hC hX h

end LogicLineages.ModelsAlgebra.Differential.SpectralProduct
