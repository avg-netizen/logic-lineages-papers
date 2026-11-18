module
public import LogicLineages.CartierObserverCurrent.ProfileDescentDefinitions
public import LogicLineages.CartierObserverCurrent.PoleContractionDefinitions
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.GeometricState
open SplittingRoots

noncomputable abbrev Closure (d : Nat) := AlgebraicClosure (FieldAt d)

noncomputable def geometricExtension (d : Nat) : RatFunc (FieldAt d) →+* RatFunc (Closure d) :=
  Naturality.rationalMap (algebraMap (FieldAt d) (Closure d))

/-- Actual poles in an algebraically closed field, not only roots visible in the finite field. -/
def supportedSimple (d : Nat) (f : RatFunc (FieldAt d)) : Prop :=
  (∀ z : Closure d, 0 < PoleContraction.poleOrder z (geometricExtension d f) →
    ∃ a : Root d, algebraMap (FieldAt d) (Closure d) a.val = z) ∧
  (∀ z : Closure d, PoleContraction.poleOrder z (geometricExtension d f) ≤ 1)
end LogicLineages.CartierObserverCurrent.GeometricState
