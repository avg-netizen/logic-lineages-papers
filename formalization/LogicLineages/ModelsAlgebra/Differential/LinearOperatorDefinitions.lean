module

public import LogicLineages.ModelsAlgebra.Differential.SpectralIndependence
public import LogicLineages.ModelsAlgebra.Differential.PolynomialDefinitions
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-! Actual polynomial differential operators for paper 15's spectral proof.
Polynomial functional calculus is interpreted in the endomorphism algebra of
the underlying K-vector space. Its literal finite-jet calibration and spectral
coordinate equations are separate proof targets, not correctness fields.
-/
namespace LogicLineages.ModelsAlgebra.Differential.LinearOperator

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def operator (D : Derivation K F F) (p : Polynomial K) : Module.End K F :=
  Polynomial.aeval D.toLinearMap p

noncomputable def applyOperator (D : Derivation K F F) (p : Polynomial K) (a : F) : F :=
  operator D p a

/-- The literal homogeneous differential polynomial f(D)Y, with X k the kth jet. -/
noncomputable def linearEquation (p : Polynomial K) : MvPolynomial ℕ K :=
  ∑ k ∈ p.support, MvPolynomial.C (p.coeff k) * MvPolynomial.X k

noncomputable def coordinate {n : ℕ} (D : Derivation K F F) (root : Fin n → K)
    (i : Fin n) (a : F) : F :=
  applyOperator D (∏ j ∈ (Finset.univ.erase i),
    (Polynomial.X - Polynomial.C (root j))) a

end LogicLineages.ModelsAlgebra.Differential.LinearOperator
