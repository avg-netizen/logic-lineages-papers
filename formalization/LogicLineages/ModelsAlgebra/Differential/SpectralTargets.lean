module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-! Fixed, implementation-independent statement of the source's
distinct-weight algebraic-independence lemma. -/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v w

/-- Paper 15, Lemma `lem:weights`, in its constant-base-field form.
The inputs contain the stated rational spectral independence and
nonzero eigenfunctions, not a supplied polynomial-independence result. -/
def spectralIndependence : Prop :=
  ∀ (K : Type u) (F : Type v) (ι : Type w)
    [Field K] [CharZero K] [Field F] [Algebra K F]
    (D : Derivation K F F) (x : ι → F) (μ : ι → K),
    (∀ i, x i ≠ 0) →
    (∀ i, D (x i) = μ i • x i) →
    LinearIndependent ℚ μ → AlgebraicIndependent K x

end LogicLineages.ModelsAlgebra.Differential.Targets
