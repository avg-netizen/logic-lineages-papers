module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndexDefinitions
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-! Actual multivariate/univariate Kronecker polynomial maps for the existing
spectral decision programme. Substitution is a genuine algebra homomorphism;
its bounded-box injectivity and the inverse decoding are theorem obligations. -/
namespace LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial

variable {K : Type*} [CommRing K]

def Box (B : ℕ) {n : ℕ} (p : MvPolynomial (Fin n) K) : Prop :=
  ∀ d ∈ p.support, KroneckerIndex.Bounded B d

noncomputable def encode (B : ℕ) {n : ℕ} :
    MvPolynomial (Fin n) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun i : Fin n => Polynomial.X ^ (B ^ i.val)

noncomputable def exponent (B n k : ℕ) : Fin n →₀ ℕ :=
  Finsupp.onFinset Finset.univ (KroneckerIndex.digits B n k) (fun i _ => Finset.mem_univ i)

noncomputable def decode (B n : ℕ) (q : Polynomial K) : MvPolynomial (Fin n) K :=
  ∑ k ∈ Finset.range (B ^ n), MvPolynomial.monomial (exponent B n k) (q.coeff k)

end LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial
