module

public import LogicLineages.ModelsAlgebra.Differential.SpectralModelTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralChange
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralModel

open Polynomial

variable {K : Type*} [Field K]

theorem variables_independent : Targets.spectralModelVariablesIndependent := by
  intro K _ n
  change Function.Injective (MvPolynomial.aeval (coordinateVariable K n))
  have h : MvPolynomial.aeval (coordinateVariable K n) =
      IsScalarTower.toAlgHom K (CoordinateRing K n) (ModelField K n) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X]
    rfl
  rw [h]
  exact IsFractionRing.injective (CoordinateRing K n) (ModelField K n)

theorem variable_derivative : Targets.spectralModelVariableDerivative := by
  intro K _ n root i
  change FractionField.extension (polynomialD K n root)
    (algebraMap (CoordinateRing K n) (ModelField K n) (MvPolynomial.X i)) = _
  rw [FractionField.extension_algebraMap]
  exact MvPolynomial.mkDerivation_X
    (R := K) (fun j : Fin n => root j • coordinateVariable K n j) i

private theorem eigen_operator (n : ℕ) (root : Fin n → K)
    (p : Polynomial K) (i : Fin n) :
    LinearOperator.applyOperator (derivation K n root) p (coordinateVariable K n i) =
      p.eval (root i) • coordinateVariable K n i := by
  apply Module.End.aeval_apply_of_mem_apply_eq_smul
  exact variable_derivative K n root i

private theorem operator_point (n : ℕ) (root : Fin n → K) (p : Polynomial K) :
    LinearOperator.applyOperator (derivation K n root) p (point K n) =
      ∑ i : Fin n, p.eval (root i) • coordinateVariable K n i := by
  change (Polynomial.aeval (derivation K n root).toLinearMap p)
    (∑ i : Fin n, coordinateVariable K n i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact eigen_operator n root p i

theorem equation : Targets.spectralModelEquation := by
  intro K _ n root
  rw [operator_point]
  apply Finset.sum_eq_zero
  intro i _
  have heval : (∏ j : Fin n, (X - C (root j))).eval (root i) = 0 := by
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  rw [heval, zero_smul]

theorem coordinates : Targets.spectralModelCoordinateCalibration := by
  intro K _ n root hr i
  change LinearOperator.applyOperator (derivation K n root)
    (Lagrange.basis Finset.univ root i) (point K n) = _
  rw [operator_point]
  have heval (j : Fin n) : (Lagrange.basis Finset.univ root i).eval (root j) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact Lagrange.eval_basis_self (fun _ _ _ _ h => hr h) (Finset.mem_univ i)
    · rw [if_neg hij]
      exact Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)
  simp_rw [heval]
  simp

theorem generic_jets : Targets.spectralModelGenericJets := by
  intro K _ n root hr
  have hcal := SpectralChange.calibration K (ModelField K n) (derivation K n root)
    n root (point K n) hr
  have hc : (fun i : Fin n => LagrangeCoordinate.coordinate (derivation K n root)
      root i (point K n)) = coordinateVariable K n :=
    funext (coordinates K n root hr)
  rw [hc] at hcal
  have hsubst : Function.Injective (SpectralChange.toCoordinates root) := by
    intro p q hpq
    have h := congrArg (SpectralChange.toJets root) hpq
    have hleft := (SpectralChange.inverse K n root hr).1
    simpa only [← AlgHom.comp_apply, hleft, AlgHom.id_apply] using h
  change Function.Injective (MvPolynomial.aeval (fun k : Fin n =>
    (((derivation K n root) : ModelField K n → ModelField K n)^[k.val]) (point K n)))
  rw [← hcal]
  change Function.Injective (fun p => MvPolynomial.aeval (coordinateVariable K n)
    (SpectralChange.toCoordinates root p))
  exact Function.Injective.comp
    (show Function.Injective (MvPolynomial.aeval (coordinateVariable K n)) from
      variables_independent K n) hsubst

end LogicLineages.ModelsAlgebra.Differential.SpectralModel
