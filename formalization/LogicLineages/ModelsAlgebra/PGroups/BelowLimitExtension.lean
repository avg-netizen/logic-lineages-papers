module
public import LogicLineages.ModelsAlgebra.PGroups.BelowLimitExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.BelowCutSelection
public import LogicLineages.ModelsAlgebra.PGroups.SocleGapExtension
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorExtension
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem below_limit_extension : Targets.groupBelowLimitExtension.{u,v} := by
  intro G H _ _ p _ hG hH B D C _ f δ hδ hBD hnot hcut hpres hRank
  obtain ⟨x,α,hxD,hxB,hpx,hxcut,hαδ,hx,hxnot,hproper,hmax⟩ :=
    below_cut_selection G p hG B D δ hBD hnot hcut
  have hα2 : α+1+1 ≤ δ := (hδ.succ_lt (hδ.succ_lt hαδ)).le
  refine ⟨x,hxD,hxB,hpx,?_⟩
  by_cases hgap : p • x ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup G)
  · exact socle_gap_preserving_extension G H p B C x α δ hG hH hα2 hxB hpx f hpres
      (hRank α hαδ) hx hxnot hgap hproper
  · have hpx1 : p • x ∈ (transfiniteFiltration p (α+1) : AddSubgroup G) := by
      rw [transfiniteFiltration_add_one]
      exact ⟨x,hx,rfl⟩
    let g : B →+ H := C.subtype.comp f.toAddMonoidHom
    have hg : Function.Injective g := Subtype.val_injective.comp f.injective
    exact successor_preserving_extension G H p B x α δ hG hH hα2 hxB hpx g hg hpres
      hx hxnot hpx1 hgap hproper hmax

end LogicLineages.ModelsAlgebra.PGroups
