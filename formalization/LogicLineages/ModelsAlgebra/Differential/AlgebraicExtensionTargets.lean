module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-!
Independent exact targets for paper 15, the algebraic-extension paragraph
following `lem:constants` (paper.tex lines 100–109). These concern arbitrary
algebraic field extensions, not just finite-dimensional extensions. The
input is an ordinary integer derivation; no target differential structure,
extension existence, compatibility supplier, or finite-subfield preservation
property is assumed. Characteristic zero of K follows from the field algebra
over F; it is not an extra premise. The algebraic-closure specialization uses
the actual Mathlib construction, whose algebraicity must be proved upstream.
Written before the external proof candidate. These are algebraic suppliers,
not either full constraint criterion or an effective decision algorithm.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

/-- Unique compatible ordinary derivation on an arbitrary algebraic extension. -/
def algebraicDerivationExtension : Prop :=
  ∀ (F : Type u) (K : Type v) [Field F] [CharZero F] [Field K]
    [Algebra F K] [Algebra.IsAlgebraic F K] (D : Derivation ℤ F F),
    ∃! E : Derivation ℤ K K,
      ∀ x, E (algebraMap F K x) = algebraMap F K (D x)

/-- Actual algebraic-closure specialization, without an algebraicity premise. -/
def algebraicClosureDerivationExtension : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F),
    ∃! E : Derivation ℤ (AlgebraicClosure F) (AlgebraicClosure F),
      ∀ x, E (algebraMap F (AlgebraicClosure F) x) =
        algebraMap F (AlgebraicClosure F) (D x)

end LogicLineages.ModelsAlgebra.Differential.Targets
