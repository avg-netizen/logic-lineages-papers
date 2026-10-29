module

public import LogicLineages.ModelsAlgebra.Differential.Targets

@[expose] public section

/-! Fixed source statement for an ordinary differential field. Using
an integer derivation avoids silently assuming rational linearity;
the candidate must construct that linearity before using the minpoly
argument over the rational base. -/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def algebraicConstantsOfIntegerDerivation : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F)
    (x : F), IsAlgebraic ℚ x → D x = 0

end LogicLineages.ModelsAlgebra.Differential.Targets
