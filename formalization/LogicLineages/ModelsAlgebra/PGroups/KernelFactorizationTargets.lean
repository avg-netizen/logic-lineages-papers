module
public import Mathlib.Algebra.Group.Subgroup.Ker
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupKernelFactorization : Prop :=
  ∀ (D S H : Type u) [AddCommGroup D] [AddCommGroup S] [AddCommGroup H]
    (f : D →+ S) (g : D →+ H), Function.Surjective f → f.ker = g.ker →
    ∃ h : S →+ H, Function.Injective h ∧ ∀ d, h (f d) = g d

end LogicLineages.ModelsAlgebra.PGroups.Targets
