module

public import LogicLineages.ModelsAlgebra.Differential.MissingSpectralModelTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralProduct

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.MissingSpectralModel

open Polynomial

variable {K : Type*} [Field K]

private theorem operator_missing (n : ℕ) (root : Fin n → K) (skipped : Fin n)
    (p : Polynomial K) :
    LinearOperator.applyOperator (SpectralModel.derivation K n root) p
      (SpectralModel.missingPoint K n skipped) =
      ∑ j : Fin n, p.eval (root j) •
        (if j = skipped then 0 else SpectralModel.coordinateVariable K n j) := by
  change (Polynomial.aeval (SpectralModel.derivation K n root).toLinearMap p)
    (∑ j : Fin n, if j = skipped then 0 else SpectralModel.coordinateVariable K n j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Module.End.aeval_apply_of_mem_apply_eq_smul
  by_cases hj : j = skipped
  · simp only [if_pos hj, map_zero, smul_zero]
  · simp only [if_neg hj]
    exact SpectralModel.variable_derivative K n root j

theorem equation : Targets.missingSpectralModelEquation := by
  intro K _ n root skipped
  rw [operator_missing]
  apply Finset.sum_eq_zero
  intro i _
  have heval : (∏ j : Fin n, (X - C (root j))).eval (root i) = 0 := by
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  rw [heval, zero_smul]

theorem coordinates : Targets.missingSpectralModelCoordinates := by
  intro K _ n root hr skipped i
  change LinearOperator.applyOperator (SpectralModel.derivation K n root)
    (Lagrange.basis Finset.univ root i) (SpectralModel.missingPoint K n skipped) = _
  rw [operator_missing]
  have heval (j : Fin n) : (Lagrange.basis Finset.univ root i).eval (root j) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact Lagrange.eval_basis_self (fun _ _ _ _ h => hr h) (Finset.mem_univ i)
    · rw [if_neg hij]
      exact Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)
  simp_rw [heval]
  simp only [ite_smul, one_smul, zero_smul]
  simp

theorem calibration : Targets.missingSpectralModelCalibration := by
  intro K _ n root hr skipped q
  let D := SpectralModel.derivation K n root
  let a := SpectralModel.missingPoint K n skipped
  let x := SpectralModel.coordinateVariable K n
  have hcal := SpectralChange.calibration K (SpectralModel.ModelField K n) D n root a hr
  have hc : (fun i : Fin n => LagrangeCoordinate.coordinate D root i a) =
      (fun i : Fin n => if i = skipped then 0 else x i) :=
    funext (coordinates K n root hr skipped)
  rw [hc] at hcal
  have hdelete : (MvPolynomial.aeval x : MvPolynomial (Fin n) K →ₐ[K]
      SpectralModel.ModelField K n).comp (Hyperplane.restrictZero skipped) =
      MvPolynomial.aeval (fun i : Fin n => if i = skipped then 0 else x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Hyperplane.restrictZero, MvPolynomial.aeval_X]
    by_cases hi : i = skipped <;> simp [hi]
  calc
    _ = MvPolynomial.aeval (fun i : Fin n => if i = skipped then 0 else x i)
        (SpectralChange.toCoordinates root q) := (AlgHom.congr_fun hcal q).symm
    _ = _ := (AlgHom.congr_fun hdelete (SpectralChange.toCoordinates root q)).symm

theorem obstruction_zero : Targets.missingSpectralModelObstructionZero := by
  intro K _ n root hr skipped
  by_contra hnonzero
  have hcoord := (SpectralProduct.product_nonvanishing K (SpectralModel.ModelField K n)
    (SpectralModel.derivation K n root) n root (SpectralModel.missingPoint K n skipped) hr).mp hnonzero
  apply hcoord skipped
  rw [coordinates K n root hr skipped skipped]
  simp

theorem avoidance : Targets.missingSpectralModelAvoidance := by
  intro K _ n root hr skipped q hrestriction
  rw [calibration K n root hr skipped q]
  intro hzero
  apply hrestriction
  have hinj : Function.Injective (MvPolynomial.aeval (SpectralModel.coordinateVariable K n)) :=
    SpectralModel.variables_independent K n
  apply hinj
  simpa only [map_zero] using hzero

end LogicLineages.ModelsAlgebra.Differential.MissingSpectralModel
