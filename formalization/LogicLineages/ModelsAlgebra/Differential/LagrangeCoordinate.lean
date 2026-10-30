module

public import LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinateTargets
public import LogicLineages.ModelsAlgebra.Differential.LinearOperator
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinate

open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem operator_C_mul (D : Derivation K F F) (c : K) (p : Polynomial K) (a : F) :
    LinearOperator.applyOperator D (C c * p) a = c • LinearOperator.applyOperator D p a := by
  rw [LinearOperator.composition K F D]
  simp [LinearOperator.applyOperator, LinearOperator.operator, Module.algebraMap_end_apply]

private theorem operator_sum {ι : Type*} (D : Derivation K F F) (s : Finset ι)
    (p : ι → Polynomial K) (a : F) :
    LinearOperator.applyOperator D (∑ i ∈ s, p i) a =
      ∑ i ∈ s, LinearOperator.applyOperator D (p i) a := by
  simp [LinearOperator.applyOperator, LinearOperator.operator, LinearMap.sum_apply]

private theorem root_injOn {n : ℕ} (root : Fin n → K) (hr : Function.Injective root) :
    Set.InjOn root (Finset.univ : Finset (Fin n)) := by
  intro i _ j _ h
  exact hr h

private theorem basis_degree_lt {n : ℕ} (root : Fin n → K) (hr : Function.Injective root)
    (i : Fin n) : (Lagrange.basis Finset.univ root i).natDegree < n := by
  rw [Lagrange.natDegree_basis (root_injOn root hr) (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  have hi := i.isLt
  omega

private theorem reconstruction_polynomial {n : ℕ} (root : Fin n → K)
    (hr : Function.Injective root) (k : Fin n) :
    (X ^ k.val : Polynomial K) =
      ∑ i : Fin n, C (root i ^ k.val) * Lagrange.basis Finset.univ root i := by
  have hd : (X ^ k.val : Polynomial K).degree < (Finset.univ : Finset (Fin n)).card := by
    rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast k.isLt
  have h := Lagrange.eq_interpolate_of_eval_eq
    (r := fun i => root i ^ k.val) (root_injOn root hr) hd (by intros; simp)
  simpa only [Lagrange.interpolate_apply] using h

theorem normalization : Targets.lagrangeCoordinateNormalization := by
  intro K F _ _ _ D n root i a
  have hp : Lagrange.basis Finset.univ root i =
      C (∏ j ∈ Finset.univ.erase i, (root i - root j)⁻¹) *
        ∏ j ∈ Finset.univ.erase i, (X - C (root j)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, ← map_prod]
  rw [coordinate, hp, operator_C_mul]
  rfl

theorem eigenvalues : Targets.lagrangeCoordinateEigenvalues := by
  intro K F _ _ _ D n root a ha i
  simp only [normalization K F D n root i a]
  change D.toLinearMap (_ • _) = _
  have hd : D.toLinearMap (LinearOperator.coordinate D root i a) =
      root i • LinearOperator.coordinate D root i a :=
    LinearOperator.spectral_coordinates K F D n root a ha i
  rw [D.toLinearMap.map_smul, hd]
  exact smul_comm _ _ _

theorem jet_reconstruction : Targets.lagrangeJetReconstruction := by
  intro K F _ _ _ D n root a hr k
  have hX : LinearOperator.applyOperator D (X ^ k.val) a = ((D : F → F)^[k.val]) a := by
    simp only [LinearOperator.applyOperator, LinearOperator.operator, aeval_X_pow,
      Module.End.pow_apply]
    rfl
  rw [← hX, reconstruction_polynomial root hr k, operator_sum]
  simp only [operator_C_mul, coordinate]

theorem coordinate_from_jets : Targets.lagrangeCoordinateFromJets := by
  intro K F _ _ _ D n root i a hr
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (Lagrange.basis Finset.univ root i).coeff k • ((D : F → F)^[k]) a) n]
  change (Polynomial.aeval D.toLinearMap (Lagrange.basis Finset.univ root i)) a = _
  rw [Polynomial.aeval_eq_sum_range' (basis_degree_lt root hr i)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.pow_apply]
  rfl

theorem coefficients_left_inverse : Targets.lagrangeCoefficientsLeftInverse := by
  intro K _ n root hr i j
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (Lagrange.basis Finset.univ root i).coeff k * root j ^ k) n,
    ← Polynomial.eval_eq_sum_range' (basis_degree_lt root hr i) (root j)]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact Lagrange.eval_basis_self (root_injOn root hr) (Finset.mem_univ i)
  · rw [if_neg hij]
    exact Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)

theorem coefficients_right_inverse : Targets.lagrangeCoefficientsRightInverse := by
  intro K _ n root hr k l
  have h := congrArg (fun p : Polynomial K => p.coeff l.val) (reconstruction_polynomial root hr k)
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow] at h
  by_cases hkl : k = l
  · subst l
    simpa only [if_pos rfl] using h.symm
  · have hv : l.val ≠ k.val := fun hv => hkl (Fin.ext hv.symm)
    simpa only [if_neg hkl, if_neg hv] using h.symm

end LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinate
