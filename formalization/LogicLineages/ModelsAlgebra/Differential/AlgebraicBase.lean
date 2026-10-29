module

public import LogicLineages.ModelsAlgebra.Differential.AlgebraicBaseTargets
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public import LogicLineages.ModelsAlgebra.Differential.SpectralIndependence
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

/-! Ordinary derivations kill an algebraic rational base, so their actual
additive maps are linear over that base. No scalar-linearity supplier is
assumed. The final specialization uses the constructed splitting field. -/

namespace LogicLineages.ModelsAlgebra.Differential.AlgebraicBase

variable {K F : Type*} [Field K] [CharZero K] [Field F] [CharZero F]
  [Algebra K F] [Algebra.IsAlgebraic ℚ K]

theorem derivation_algebraMap_eq_zero (D : Derivation ℤ F F) (k : K) :
    D (algebraMap K F k) = 0 := by
  apply integerDerivation_eq_zero_of_isAlgebraic D
  exact (Algebra.IsAlgebraic.isAlgebraic k).algebraMap

def toAlgebraicBase (D : Derivation ℤ F F) : Derivation K F F where
  toLinearMap :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := by
        intro k x
        rw [Algebra.smul_def, D.leibniz, derivation_algebraMap_eq_zero D k]
        simp only [smul_eq_mul, mul_zero, add_zero, Algebra.smul_def, RingHom.id_apply] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

@[simp] theorem toAlgebraicBase_apply (D : Derivation ℤ F F) (x : F) :
    toAlgebraicBase (K := K) D x = D x := rfl

theorem algebraicBaseLinearity : Targets.algebraicBaseLinearity := by
  intro K F _ _ _ _ _ _ D
  exact ⟨toAlgebraicBase D, fun _ => rfl⟩

theorem ordinarySpectralIndependence : Targets.ordinarySpectralIndependence := by
  intro K F ι _ _ _ _ _ _ D x μ hx hD hμ
  exact algebraicIndependent_of_rat_independent_eigenvalues
    (toAlgebraicBase D) x μ hx hD hμ

theorem splittingFieldSpectralIndependence : Targets.splittingFieldSpectralIndependence := by
  intro f F ι _ _ _ D x μ hx hD hμ
  letI : Algebra.IsAlgebraic ℚ f.SplittingField :=
    Algebra.IsAlgebraic.of_finite ℚ f.SplittingField
  exact ordinarySpectralIndependence f.SplittingField F ι D x μ hx hD hμ

end LogicLineages.ModelsAlgebra.Differential.AlgebraicBase
