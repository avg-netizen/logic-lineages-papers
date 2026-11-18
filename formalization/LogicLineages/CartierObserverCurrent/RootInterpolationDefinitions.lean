module
public import LogicLineages.CartierObserverCurrent.SplittingRootsDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RootInterpolation
open SplittingRoots

/-- The monic squarefree product over every distinct root of the literal source. -/
noncomputable def rootProduct (d : Nat) : Polynomial (FieldAt d) :=
  ∏ z ∈ rootSet d, (Polynomial.X - Polynomial.C z)

/-- The actual polynomial obtained by omitting one root factor. -/
noncomputable def omittedProduct (d : Nat) (z : FieldAt d) : Polynomial (FieldAt d) := by
  classical
  exact ∏ a ∈ (rootSet d).erase z, (Polynomial.X - Polynomial.C a)

/-- Actual Lagrange residues of an arbitrary numerator, not supplied coordinates. -/
noncomputable def residues (d : Nat) (U : Polynomial (FieldAt d)) (z : Root d) : FieldAt d :=
  U.eval z.val / (omittedProduct d z.val).eval z.val

noncomputable def interpolate (d : Nat) (U : Polynomial (FieldAt d)) : Polynomial (FieldAt d) := by
  classical
  exact ∑ z ∈ rootSet d,
    Polynomial.C (U.eval z / (omittedProduct d z).eval z) * omittedProduct d z
end LogicLineages.CartierObserverCurrent.RootInterpolation
