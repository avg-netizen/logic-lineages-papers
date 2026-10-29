module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-!
Fixed finite-extension supplier for paper 15, the algebraic-extension
paragraph following Lemma `lem:constants` and the splitting-field step
in Theorem `thm:spectral`. The conclusion constructs the unique extended
ordinary derivation; no differential-algebra instance is a premise.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def finiteDerivationExtension : Prop :=
  ∀ (F : Type u) (K : Type v) [Field F] [CharZero F] [Field K]
    [Algebra F K] [FiniteDimensional F K] (D : Derivation ℤ F F),
    ∃! E : Derivation ℤ K K,
      ∀ x, E (algebraMap F K x) = algebraMap F K (D x)

end LogicLineages.ModelsAlgebra.Differential.Targets
