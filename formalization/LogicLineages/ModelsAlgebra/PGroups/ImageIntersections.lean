module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationDefinitions
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-!
# The actual limit-stage subgroup identity

For a surjective additive map, its kernel being contained in every
subgroup makes every subgroup saturated under taking preimages of
images. Comap preserves intersections and is injective for a surjection.
This proves the limit-stage identity used in paper 01; it does not
assume the desired transfinite filtration equality.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

variable {G : Type*} {H : Type*} {ι : Sort*}
variable [AddCommGroup G] [AddCommGroup H]

theorem map_iInf_of_ker_le (f : G →+ H) (hf : Function.Surjective f)
    (S : ι → AddSubgroup G) (hker : ∀ i, f.ker ≤ S i) :
    (iInf S).map f = ⨅ i, (S i).map f := by
  apply AddSubgroup.comap_injective hf
  rw [AddSubgroup.comap_map_eq_self (le_iInf hker), AddSubgroup.comap_iInf]
  congr 1
  funext i
  exact (AddSubgroup.comap_map_eq_self (hker i)).symm

end LogicLineages.ModelsAlgebra.PGroups
