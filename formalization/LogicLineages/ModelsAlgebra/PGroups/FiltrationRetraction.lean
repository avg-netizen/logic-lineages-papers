module
public import LogicLineages.ModelsAlgebra.PGroups.FiltrationRetractionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem hom_transfinite_filtration : Targets.groupHomTransfiniteFiltration := by
  intro G H _ _ f p α
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · intro x _
    rw [transfiniteFiltration_zero]
    exact AddSubgroup.mem_top _
  · intro x hx
    rw [transfiniteFiltration_add_one] at hx ⊢
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨f y, ih y hy, ?_⟩
    exact (map_nsmul f p y).symm
  · intro x hx
    rw [transfiniteFiltration_limit p hβ] at hx ⊢
    apply AddSubgroup.mem_iInf.mpr
    intro γ
    exact ih γ.val γ.property x (AddSubgroup.mem_iInf.mp hx γ)

theorem retraction_filtration_reflection : Targets.groupRetractionFiltrationReflection := by
  intro G H _ _ i r hr p α x
  constructor
  · intro hx
    simpa only [hr x] using hom_transfinite_filtration H G r p α (i x) hx
  · exact hom_transfinite_filtration G H i p α x

end LogicLineages.ModelsAlgebra.PGroups
