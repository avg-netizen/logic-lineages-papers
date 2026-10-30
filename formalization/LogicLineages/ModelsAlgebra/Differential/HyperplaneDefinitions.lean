module

public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section

/-! Literal restriction to a missing spectral coordinate. -/
namespace LogicLineages.ModelsAlgebra.Differential.Hyperplane

variable {K ι : Type*} [Field K] [DecidableEq ι]

noncomputable def restrictZero (i : ι) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  MvPolynomial.aeval fun j => if j = i then 0 else MvPolynomial.X j

end LogicLineages.ModelsAlgebra.Differential.Hyperplane
