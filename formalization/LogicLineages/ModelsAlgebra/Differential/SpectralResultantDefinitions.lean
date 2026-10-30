module

public import LogicLineages.ModelsAlgebra.Differential.SpectralProductDefinitions
public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomialDefinitions
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

@[expose] public section

/-! A coefficientwise form of the source's rational divided difference.
For Y_k its T-coefficient is the literal synthetic-division sum
∑_{j=k+1}^n a_j T^(j-k-1). This is the finite double sum G_f from
paper15, collected by the jet variables. Resultant is Mathlib's actual
Sylvester determinant, not a predicate specifying the desired answer. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultant

noncomputable def generating {R : Type*} [CommRing R] (n : ℕ) (f : Polynomial R) :
    Polynomial (MvPolynomial (Fin n) R) :=
  ∑ k : Fin n, ∑ j ∈ Finset.Icc (k.val + 1) n,
    Polynomial.C (MvPolynomial.C (f.coeff j) * MvPolynomial.X k) *
      Polynomial.X ^ (j - (k.val + 1))

noncomputable def atRoot {K : Type*} [Field K] [Algebra ℚ K]
    (n : ℕ) (f : Polynomial ℚ) (a : K) : MvPolynomial (Fin n) K :=
  Polynomial.eval₂ (MvPolynomial.map (algebraMap ℚ K)) (MvPolynomial.C a) (generating n f)

noncomputable def obstruction (n : ℕ) (f : Polynomial ℚ) : MvPolynomial (Fin n) ℚ :=
  (f.map MvPolynomial.C).resultant (generating n f) n (n - 1)

end LogicLineages.ModelsAlgebra.Differential.SpectralResultant
