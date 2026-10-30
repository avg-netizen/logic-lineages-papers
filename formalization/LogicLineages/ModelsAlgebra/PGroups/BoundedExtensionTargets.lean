module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Genuine extension existence, in Type0, for all positive exponent bounds.
No injectivity, projection or extension property is an input. -/
def groupBoundedCyclicExtension : Prop :=
  ∀ (n : ℕ) [NeZero n] (G : Type) [AddCommGroup G], (∀ x : G, n • x = 0) →
    ∀ (S : AddSubgroup G) (f : S →+ ZMod n),
      ∃ g : G →+ ZMod n, ∀ x : S, g (x : G) = f x

end LogicLineages.ModelsAlgebra.PGroups.Targets
