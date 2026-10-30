module

public import LogicLineages.ModelsAlgebra.Differential.CoefficientDescentTargets
public import Mathlib.LinearAlgebra.Finsupp.Defs

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CoefficientDescent

open MvPolynomial

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

private noncomputable def retractCoefficients (g : L →ₗ[K] K) :
    MvPolynomial ι L →ₗ[K] MvPolynomial ι K :=
  Finsupp.mapRange.linearMap g

private theorem retract_coeff (g : L →ₗ[K] K) (p : MvPolynomial ι L) (d : ι →₀ ℕ) :
    coeff d (retractCoefficients g p) = g (coeff d p) := rfl

private theorem retract_map (g : L →ₗ[K] K)
    (hg : ∀ a, g (algebraMap K L a) = a) (p : MvPolynomial ι K) :
    retractCoefficients g (map (algebraMap K L) p) = p := by
  ext d
  rw [retract_coeff, coeff_map, hg]

private theorem retract_map_mul (g : L →ₗ[K] K) (p : MvPolynomial ι K)
    (h : MvPolynomial ι L) :
    retractCoefficients g (map (algebraMap K L) p * h) = p * retractCoefficients g h := by
  classical
  ext d
  rw [retract_coeff, coeff_mul, map_sum, coeff_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [coeff_map, retract_coeff]
  simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
    g.map_smul (coeff s.1 p) (coeff s.2 h)

theorem divisibility_descent : Targets.mvPolynomialDivisibilityDescent := by
  intro K L ι _ _ _ p q
  constructor
  · intro hdvd
    have hf : LinearMap.ker (Algebra.linearMap K L) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K L)
    obtain ⟨g, hg⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective hf
    have hg' (a : K) : g (algebraMap K L a) = a :=
      LinearMap.congr_fun hg a
    obtain ⟨h, hq⟩ := hdvd
    refine ⟨retractCoefficients g h, ?_⟩
    calc
      q = retractCoefficients g (map (algebraMap K L) q) := (retract_map g hg' q).symm
      _ = retractCoefficients g (map (algebraMap K L) p * h) := congrArg _ hq
      _ = p * retractCoefficients g h := retract_map_mul g p h
  · intro hdvd
    exact map_dvd (MvPolynomial.map (algebraMap K L)) hdvd

end LogicLineages.ModelsAlgebra.Differential.CoefficientDescent
