module

public import LogicLineages.ModelsAlgebra.Differential.SpectralChangeTargets
public import LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinate
public import LogicLineages.ModelsAlgebra.Differential.SpectralIndependence

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralChange

open MvPolynomial

variable {K : Type*} [Field K]

private theorem sum_linear {n : ℕ} (a : Fin n → K) (b : Fin n → Fin n → K) :
    (∑ i : Fin n, C (a i) * ∑ j : Fin n, C (b i j) * X j : MvPolynomial (Fin n) K) =
      ∑ j : Fin n, C (∑ i : Fin n, a i * b i j) * X j := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]

private theorem toCoordinates_X {n : ℕ} (root : Fin n → K) (k : Fin n) :
    toCoordinates root (X k) = ∑ i : Fin n, C (root i ^ k.val) * X i := by
  simp [toCoordinates]

private theorem toJets_X {n : ℕ} (root : Fin n → K) (i : Fin n) :
    toJets root (X i) =
      ∑ k : Fin n, C ((Lagrange.basis Finset.univ root i).coeff k.val) * X k := by
  simp [toJets]

theorem inverse : Targets.spectralChangeInverse := by
  intro K _ n root hr
  constructor
  · apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, toCoordinates_X, map_sum, map_mul,
      MvPolynomial.algHom_C, toJets_X, AlgHom.id_apply]
    change (∑ i : Fin n, C (root i ^ k.val) *
      ∑ l : Fin n, C ((Lagrange.basis Finset.univ root i).coeff l.val) * X l) = X k
    rw [sum_linear]
    simp_rw [LagrangeCoordinate.coefficients_right_inverse K n root hr]
    simp
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, toJets_X, map_sum, map_mul,
      MvPolynomial.algHom_C, toCoordinates_X, AlgHom.id_apply]
    change (∑ k : Fin n, C ((Lagrange.basis Finset.univ root i).coeff k.val) *
      ∑ j : Fin n, C (root j ^ k.val) * X j) = X i
    rw [sum_linear]
    simp_rw [LagrangeCoordinate.coefficients_left_inverse K n root hr]
    simp

theorem calibration : Targets.spectralChangeCalibration := by
  intro K F _ _ _ D n root a hr
  apply MvPolynomial.algHom_ext
  intro k
  simp only [AlgHom.comp_apply, toCoordinates_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simpa only [Algebra.smul_def] using
    (LagrangeCoordinate.jet_reconstruction K F D n root a hr k).symm

theorem generic_jet_independence : Targets.spectralGenericJetIndependence := by
  intro K F _ _ _ _ D n root a hr hx ha
  have hinj : Function.Injective root := hr.injective
  have hAI : AlgebraicIndependent K (fun i : Fin n => LagrangeCoordinate.coordinate D root i a) :=
    algebraicIndependent_of_rat_independent_eigenvalues D _ root hx
      (LagrangeCoordinate.eigenvalues K F D n root a ha) hr
  have hsubst : Function.Injective (toCoordinates root) := by
    intro p q hpq
    have h := congrArg (toJets root) hpq
    have hleft := (inverse K n root hinj).1
    simpa only [← AlgHom.comp_apply, hleft, AlgHom.id_apply] using h
  change Function.Injective (MvPolynomial.aeval (fun k : Fin n => ((D : F → F)^[k.val]) a))
  rw [← calibration K F D n root a hinj]
  change Function.Injective (fun p =>
    (MvPolynomial.aeval (fun i : Fin n => LagrangeCoordinate.coordinate D root i a))
      (toCoordinates root p))
  exact Function.Injective.comp
    (show Function.Injective (MvPolynomial.aeval (fun i : Fin n =>
      LagrangeCoordinate.coordinate D root i a)) from hAI) hsubst

end LogicLineages.ModelsAlgebra.Differential.SpectralChange
