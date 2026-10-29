module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups

universe u v

variable {G : Type u} [AddCommGroup G]

theorem quotient_filtration_below (p : ℕ) (T : AddSubgroup G) (δ : Ordinal.{v})
    (hT : T ≤ transfiniteFiltration p δ) :
    ∀ α ≤ δ, (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) =
      (transfiniteFiltration p α : AddSubgroup G).map (QuotientAddGroup.mk' T) := by
  intro α hα
  have hker : (QuotientAddGroup.mk' T).ker ≤ transfiniteFiltration p δ := by
    simpa only [QuotientAddGroup.ker_mk'] using hT
  exact (map_transfiniteFiltration_below p (QuotientAddGroup.mk' T)
    (QuotientAddGroup.mk'_surjective T) δ hker α hα).symm

end LogicLineages.ModelsAlgebra.PGroups
