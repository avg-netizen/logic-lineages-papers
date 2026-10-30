module
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryQuotientTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem p_primary_quotient : Targets.groupPPrimaryQuotient := by
  intro G _ p T hG x
  obtain ⟨y,rfl⟩ := QuotientAddGroup.mk'_surjective T x
  obtain ⟨n,hn⟩ := hG y
  refine ⟨n, ?_⟩
  rw [← map_nsmul, hn, map_zero]

end LogicLineages.ModelsAlgebra.PGroups
