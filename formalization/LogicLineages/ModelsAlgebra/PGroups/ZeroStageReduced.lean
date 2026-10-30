module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReducedTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem p_divisible_in_every_stage : Targets.groupPDivisibleInEveryStage := by
  intro G _ p S hS α
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · rw [transfiniteFiltration_zero]
    exact le_top
  · intro x hx
    rw [transfiniteFiltration_add_one]
    obtain ⟨y,hy⟩ := hS ⟨x,hx⟩
    exact ⟨(y:G), ih y.property, congrArg Subtype.val hy⟩
  · intro x hx
    rw [transfiniteFiltration_limit p hβ]
    exact AddSubgroup.mem_iInf.mpr (fun γ => ih γ.val γ.property hx)

theorem zero_stage_no_p_divisible : Targets.groupZeroStageNoPDivisible := by
  intro G _ p α hzero S hS
  apply le_antisymm
  · exact (p_divisible_in_every_stage G p S hS α).trans hzero.le
  · exact bot_le

theorem zero_stage_reduced : Targets.groupZeroStageReduced := by
  intro G _ p hp α hzero S hS
  exact zero_stage_no_p_divisible G p α hzero S (hS p hp)

end LogicLineages.ModelsAlgebra.PGroups
