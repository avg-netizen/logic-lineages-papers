module

public import LogicLineages.Ultrafilters.Definitions
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

namespace LogicLineages.Ultrafilters

/-- The actual finite coordinate support in a rational basis of the reals. -/
noncomputable def supportLength {ι : Type*} (B : Module.Basis ι ℚ ℝ)
    (x : ℝ) : Nat := (B.repr x).support.card

/-- Only the coordinates occurring in x are required to vanish. -/
def coordinateKernel {ι : Type*} (B : Module.Basis ι ℚ ℝ) (x : ℝ) : Set ℝ :=
  {y | ∀ i ∈ (B.repr x).support, B.repr y i = 0}

end LogicLineages.Ultrafilters
