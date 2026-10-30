module

public import LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinateDefinitions

@[expose] public section

/-! Literal substitutions between finite jet variables and normalized spectral
variables. Invertibility, calibration to actual derivatives, and independence
are theorem targets; none is a field in this data. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralChange

variable {K : Type*} [Field K]

noncomputable def toCoordinates {n : ℕ} (root : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun k =>
    ∑ i : Fin n, MvPolynomial.C (root i ^ k.val) * MvPolynomial.X i

noncomputable def toJets {n : ℕ} (root : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun i =>
    ∑ k : Fin n, MvPolynomial.C ((Lagrange.basis Finset.univ root i).coeff k.val) * MvPolynomial.X k

end LogicLineages.ModelsAlgebra.Differential.SpectralChange
