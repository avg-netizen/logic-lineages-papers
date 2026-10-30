module

public import LogicLineages.ModelsAlgebra.Differential.SpectralChangeDefinitions

@[expose] public section

/-! Literal forms L_i and their product R_f over the splitting constant base
from paper 15 equations (vandermonde) and (product). Rational coefficient
descent is a separate obligation, not a field in this data. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralProduct

variable {K : Type*} [Field K]

noncomputable def rawPolynomial {n : ℕ} (root : Fin n → K) (i : Fin n) : Polynomial K :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (root j))

noncomputable def linearForm (n : ℕ) (p : Polynomial K) : MvPolynomial (Fin n) K :=
  ∑ k : Fin n, MvPolynomial.C (p.coeff k.val) * MvPolynomial.X k

noncomputable def obstruction {n : ℕ} (root : Fin n → K) : MvPolynomial (Fin n) K :=
  ∏ i : Fin n, linearForm n (rawPolynomial root i)

noncomputable def scale {n : ℕ} (root : Fin n → K) (i : Fin n) : K :=
  ∏ j ∈ Finset.univ.erase i, (root i - root j)

end LogicLineages.ModelsAlgebra.Differential.SpectralProduct
