module

public import LogicLineages.ModelsAlgebra.Differential.LinearOperatorTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.LinearOperator

open Polynomial

theorem literal_evaluation : Targets.linearOperatorLiteralEvaluation := by
  intro K F _ _ _ D p a
  simp only [applyOperator, operator, aeval_def, eval₂_eq_sum, Polynomial.sum_def,
    LinearMap.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
    Module.End.pow_apply]
  rfl

theorem composition : Targets.linearOperatorComposition := by
  intro K F _ _ _ D p q a
  change (Polynomial.aeval D.toLinearMap (p * q)) a =
    (Polynomial.aeval D.toLinearMap p) ((Polynomial.aeval D.toLinearMap q) a)
  rw [map_mul]
  rfl

theorem factor : Targets.linearOperatorFactor := by
  intro K F _ _ _ D c a
  simp [applyOperator, operator, Module.algebraMap_end_apply]

private theorem jet_eq_iterate {F : Type*} [Field F] [CharZero F]
    (D : Derivation ℚ F F) (a : F) (n : ℕ) :
    jet D a n = ((D : F → F)^[n]) a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [jet, ih, Function.iterate_succ_apply']

theorem source_equation : Targets.linearOperatorSourceEquation := by
  intro F _ _ D p a
  rw [literal_evaluation ℚ F D p a]
  simp [jetEval, linearEquation, jet_eq_iterate, Algebra.smul_def]

theorem spectral_coordinates : Targets.linearOperatorSpectralCoordinates := by
  intro K F _ _ _ D n root a ha i
  have hp : (∏ j : Fin n, (X - C (root j))) =
      (X - C (root i)) * ∏ j ∈ (Finset.univ.erase i), (X - C (root j)) := by
    exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun j => X - C (root j)) (Finset.mem_univ i)).symm
  rw [hp, composition K F D, factor K F D] at ha
  exact sub_eq_zero.mp ha

end LogicLineages.ModelsAlgebra.Differential.LinearOperator
