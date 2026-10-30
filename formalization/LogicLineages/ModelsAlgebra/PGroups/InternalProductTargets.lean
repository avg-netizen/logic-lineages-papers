module
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Prod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupInternalProductIsomorphism : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (K T H : AddSubgroup G),
    H = K ⊔ T → Disjoint K T →
    ∃ e : (K × T) ≃+ H, ∀ x : K × T, (e x : G) = (x.1 : G) + (x.2 : G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
