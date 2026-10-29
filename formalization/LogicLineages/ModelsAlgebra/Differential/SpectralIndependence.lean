module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Independence from distinct differential weights

The ingredients here are concrete derivations, products and polynomial
evaluation. No algebraic-independence criterion is assumed. The spectral
roots and the Vandermonde coordinate change used by the full constraint
theorem are separate obligations.
-/

namespace LogicLineages.ModelsAlgebra.Differential

open scoped BigOperators

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F]

/-- Eigenvectors of a concrete base derivation with distinct scalar
eigenvalues are linearly independent. -/
theorem derivative_eigenvectors_linearIndependent (D : Derivation K F F)
    (μ : ι → K) (hμ : Function.Injective μ) (v : ι → F)
    (hv : ∀ i, v i ≠ 0) (hD : ∀ i, D (v i) = μ i • v i) :
    LinearIndependent K v := by
  apply Module.End.eigenvectors_linearIndependent' D.toLinearMap μ hμ v
  intro i
  exact ⟨Module.End.mem_eigenspace_iff.mpr (hD i), hv i⟩

/-- The differential weight of a power is its exponent times the
weight of the generator. -/
theorem derivation_pow_eigenvalue (D : Derivation K F F) (x : F) (μ : K)
    (hx : D x = μ • x) (n : ℕ) : D (x ^ n) = ((n : K) * μ) • x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, D.leibniz, ih, hx]
      simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_one,
        map_mul, map_add, map_natCast, map_one, Algebra.algebraMap_self_apply]
      ring

/-- Products add differential weights. -/
theorem derivation_prod_eigenvalue [DecidableEq ι] (D : Derivation K F F)
    (s : Finset ι) (x : ι → F) (μ : ι → K)
    (hx : ∀ i ∈ s, D (x i) = μ i • x i) :
    D (∏ i ∈ s, x i) = (∑ i ∈ s, μ i) • (∏ i ∈ s, x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, D.leibniz, hx a (Finset.mem_insert_self a s)]
      rw [ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]
      simp only [Algebra.smul_def, map_add, Algebra.algebraMap_self_apply]
      ring

/-- Evaluation of an exponent vector as a field monomial. -/
def differentialMonomial (x : ι → F) (d : ι →₀ ℕ) : F :=
  d.prod fun i n => x i ^ n

/-- The scalar eigenvalue attached to a field monomial. -/
def differentialWeight (μ : ι → K) (d : ι →₀ ℕ) : K :=
  d.sum fun i n => (n : K) * μ i

theorem derivation_monomial (D : Derivation K F F) (x : ι → F) (μ : ι → K)
    (hx : ∀ i, D (x i) = μ i • x i) (d : ι →₀ ℕ) :
    D (differentialMonomial x d) = differentialWeight μ d • differentialMonomial x d := by
  classical
  exact derivation_prod_eigenvalue D d.support (fun i => x i ^ d i)
    (fun i => (d i : K) * μ i)
    (fun i _ => derivation_pow_eigenvalue D (x i) (μ i) (hx i) (d i))

theorem differentialMonomial_ne_zero (x : ι → F) (hx : ∀ i, x i ≠ 0)
    (d : ι →₀ ℕ) : differentialMonomial x d ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))

/-- Independent evaluated monomials imply that polynomial evaluation
has trivial kernel. This bridges linear independence to the genuine
Mathlib algebraic-independence predicate. -/
theorem algebraicIndependent_of_monomials_linearIndependent (x : ι → F)
    (h : LinearIndependent K (differentialMonomial x)) : AlgebraicIndependent K x := by
  have hmap : (MvPolynomial.aeval x).toLinearMap =
      Finsupp.linearCombination K (differentialMonomial x) := by
    ext d
    change (MvPolynomial.aeval x) (MvPolynomial.monomial d (1 : K)) =
      (Finsupp.linearCombination K (differentialMonomial x)) (Finsupp.single d 1)
    simp only [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.linearCombination_single, one_smul, differentialMonomial]
  change Function.Injective (MvPolynomial.aeval x)
  change Function.Injective (MvPolynomial.aeval x).toLinearMap
  rw [hmap]
  exact h.finsuppLinearCombination_injective

/-- The distinct-weight argument with every supplier proved above.
Weight injectivity is an explicit arithmetic hypothesis at this general
base; it will be derived from rational spectral independence below. -/
theorem algebraicIndependent_of_injective_differentialWeight
    (D : Derivation K F F) (x : ι → F) (μ : ι → K)
    (hx : ∀ i, x i ≠ 0) (hD : ∀ i, D (x i) = μ i • x i)
    (hweight : Function.Injective (differentialWeight μ)) : AlgebraicIndependent K x := by
  apply algebraicIndependent_of_monomials_linearIndependent x
  exact derivative_eigenvectors_linearIndependent D (differentialWeight μ) hweight
    (differentialMonomial x) (differentialMonomial_ne_zero x hx)
    (derivation_monomial D x μ hD)

/-- Rational independence makes all nonnegative integer monomial weights
distinct. Restricting scalars proves this rather than adding it to the
source hypothesis list. -/
theorem differentialWeight_injective_of_rat_linearIndependent [CharZero K]
    (μ : ι → K) (hμ : LinearIndependent ℚ μ) :
    Function.Injective (differentialWeight μ) := by
  have hnat : LinearIndependent ℕ μ := hμ.restrict_scalars' ℕ
  have hinj := hnat.finsuppLinearCombination_injective
  intro d e hde
  apply hinj
  simpa only [Finsupp.linearCombination_apply, differentialWeight, nsmul_eq_mul] using hde

/-- Paper 15's distinct-weight algebraic-independence argument for a
constant base field. No injectivity-of-weights premise remains. -/
theorem algebraicIndependent_of_rat_independent_eigenvalues [CharZero K]
    (D : Derivation K F F) (x : ι → F) (μ : ι → K)
    (hx : ∀ i, x i ≠ 0) (hD : ∀ i, D (x i) = μ i • x i)
    (hμ : LinearIndependent ℚ μ) : AlgebraicIndependent K x := by
  exact algebraicIndependent_of_injective_differentialWeight D x μ hx hD
    (differentialWeight_injective_of_rat_linearIndependent μ hμ)

end LogicLineages.ModelsAlgebra.Differential
