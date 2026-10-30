module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicFamilyTargets
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily

open Polynomial

theorem geometric_coeff (R : Type*) [CommRing R] (ℓ k : ℕ) :
    (geometric R ℓ).coeff k = if k < ℓ then 1 else 0 := by
  classical
  simp [geometric, finsetSum_coeff, coeff_X_pow, eq_comm]

theorem geometric_coefficients : Targets.cyclotomicGeometricCoefficients := by
  intro R _ _ ℓ hℓ
  have hc := geometric_coeff R ℓ
  have hd : (geometric R ℓ).natDegree = ℓ - 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      rw [hc, if_neg (by omega)]
    · rw [hc, if_pos (by omega)]
      exact one_ne_zero
  refine ⟨hc, ?_, hd⟩
  change (geometric R ℓ).coeff (geometric R ℓ).natDegree = 1
  rw [hd, hc, if_pos (by omega)]

theorem geometric_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (ℓ : ℕ) : (geometric R ℓ).map φ = geometric S ℓ := by
  simp [geometric, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]

theorem geometric_mul (R : Type*) [CommRing R] (ℓ : ℕ) :
    geometric R ℓ * (X - 1) = X ^ ℓ - 1 := by
  exact geom_sum_mul (X : Polynomial R) ℓ

end LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
