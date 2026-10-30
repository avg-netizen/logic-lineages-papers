module
public import LogicLineages.ModelsAlgebra.PGroups.FiltrationProfileTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem filtration_profile_total : Targets.groupFiltrationProfileTotal.{u,v} := by
  classical
  intro G _ p x y
  by_cases h : ∀ α : Ordinal.{v}, x ∈ (transfiniteFiltration p α : AddSubgroup G) →
      y ∈ (transfiniteFiltration p α : AddSubgroup G)
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨α,hx,hy⟩ := h
    intro β hyβ
    rcases le_total β α with hβα | hαβ
    · exact transfiniteFiltration_antitone p hβα hx
    · exact False.elim (hy (transfiniteFiltration_antitone p hαβ hyβ))

end LogicLineages.ModelsAlgebra.PGroups
