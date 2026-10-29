module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

/-!
Independent targets for the constant-base bridge in paper 15's spectral
coordinates paragraph and Lemma `lem:weights`. The input derivation is an
ordinary integer derivation, not an assumed K-linear derivation. Rational
algebras on characteristic-zero fields are canonical; no additional tower
compatibility hypothesis or differential-base interface is supplied.

The final target uses the actual constructed rational splitting field,
whose finite dimensionality/algebraicity must come from proved Mathlib
suppliers, not a premise. Arbitrary index types strengthen the source's
finite family. These targets do not construct spectral coordinates, prove
rational descent, or decide constrainedness. Written before bridge proofs.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v w

/-- An ordinary derivation is linear over every algebraic rational base. -/
def algebraicBaseLinearity : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [CharZero K] [Field F] [CharZero F]
    [Algebra K F] [Algebra.IsAlgebraic ℚ K] (D : Derivation ℤ F F),
    ∃ E : Derivation K F F, ∀ x, E x = D x

/-- Distinct-weight independence with ordinary, rather than K-linear, D. -/
def ordinarySpectralIndependence : Prop :=
  ∀ (K : Type u) (F : Type v) (ι : Type w)
    [Field K] [CharZero K] [Field F] [CharZero F]
    [Algebra K F] [Algebra.IsAlgebraic ℚ K]
    (D : Derivation ℤ F F) (x : ι → F) (μ : ι → K),
    (∀ i, x i ≠ 0) → (∀ i, D (x i) = μ i • x i) →
    LinearIndependent ℚ μ → AlgebraicIndependent K x

/-- Source specialization to the actual splitting field of a rational polynomial. -/
def splittingFieldSpectralIndependence : Prop :=
  ∀ (f : Polynomial ℚ) (F : Type v) (ι : Type w)
    [Field F] [CharZero F] [Algebra f.SplittingField F]
    (D : Derivation ℤ F F) (x : ι → F) (μ : ι → f.SplittingField),
    (∀ i, x i ≠ 0) → (∀ i, D (x i) = μ i • x i) →
    LinearIndependent ℚ μ → AlgebraicIndependent f.SplittingField x

end LogicLineages.ModelsAlgebra.Differential.Targets
