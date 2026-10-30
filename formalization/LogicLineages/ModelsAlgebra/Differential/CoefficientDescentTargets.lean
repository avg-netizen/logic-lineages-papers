module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! Paper 15 thm:spectral necessity uses that extending the constant field
does not change divisibility of rational multivariate polynomials. This exact
field-extension theorem has no Galois/descent oracle premise. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v w

def mvPolynomialDivisibilityDescent : Prop :=
  ∀ (K : Type u) (L : Type v) (ι : Type w)
    [Field K] [Field L] [Algebra K L] (p q : MvPolynomial ι K),
    MvPolynomial.map (algebraMap K L) p ∣ MvPolynomial.map (algebraMap K L) q ↔ p ∣ q

end LogicLineages.ModelsAlgebra.Differential.Targets
