module
public import LogicLineages.ModelsAlgebra.PGroups.ExactHeightTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem exact_height_below_cut : Targets.groupExactHeightBelowCut.{u,v} := by
  classical
  intro G _ p δ x
  refine Ordinal.limitRecOn δ ?_ (fun γ ih => ?_) (fun γ hγ ih => ?_)
  · intro hx
    exact False.elim (hx (by rw [transfiniteFiltration_zero]; exact AddSubgroup.mem_top x))
  · intro hx
    by_cases hprev : x ∈ (transfiniteFiltration p γ : AddSubgroup G)
    · exact ⟨γ,Order.lt_succ γ,hprev,hx⟩
    · obtain ⟨α,hαγ,hα,hαnot⟩ := ih hprev
      exact ⟨α,hαγ.trans (Order.lt_succ γ),hα,hαnot⟩
  · intro hx
    rw [transfiniteFiltration_limit p hγ] at hx
    have hex : ∃ β : Set.Iio γ, x ∉ (transfiniteFiltration p β.val : AddSubgroup G) := by
      by_contra h
      apply hx
      apply AddSubgroup.mem_iInf.mpr
      intro β
      by_contra hβ
      exact h ⟨β,hβ⟩
    obtain ⟨β,hβ⟩ := hex
    obtain ⟨α,hαβ,hα,hαnot⟩ := ih β.val β.property hβ
    exact ⟨α,hαβ.trans β.property,hα,hαnot⟩

theorem exact_height_zero_stage : Targets.groupExactHeightZeroStage.{u,v} := by
  intro G _ p δ hzero x hx
  apply exact_height_below_cut G p δ x
  intro hm
  exact hx (hzero.le hm)

end LogicLineages.ModelsAlgebra.PGroups
