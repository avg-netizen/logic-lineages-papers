module
public import LogicLineages.PermittedControl.ActualFiniteOrderBranchesTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesGuardProof
import LogicLineages.PermittedControl.ActualCoordinateRankChartProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteOrderBranches
open ActualCoordinateRankChart (cells size rankOf exactDenseRankChart)

theorem exactActualBranchCoverage : ExactActualBranchCoverage := by
  intro θ names
  have facts := exactDenseRankChart θ names
  let decorate := fun name : Nat => (name,rankOf θ names name)
  have inBranch : actualPattern θ names ∈ patterns names := by
    apply (exactPatternEnumeration names _).mpr
    change size θ names ≤ names.length ∧ (names.map decorate).map Prod.fst = names ∧
      (∀ e ∈ names.map decorate, e.2 < size θ names) ∧
      ∀ j, j < size θ names → ∃ e ∈ names.map decorate, e.2 = j
    refine ⟨?_,?_,?_,?_⟩
    · calc
        size θ names ≤ (names.map θ).length := List.toFinset_card_le _
        _ = names.length := List.length_map θ
    · simp [decorate,List.map_map,Function.comp_def]
    · intro e he
      obtain ⟨name,mem,rfl⟩ := List.mem_map.mp he
      exact (facts.2.1 name mem).1
    · intro j hj
      obtain ⟨name,mem,eq⟩ := facts.2.2.1 j hj
      exact ⟨decorate name,List.mem_map.mpr ⟨name,mem,rfl⟩,eq⟩
  refine ⟨inBranch,(exactOrderGuard θ _).mpr ?_⟩
  intro a ha b hb
  change a ∈ names.map decorate at ha
  change b ∈ names.map decorate at hb
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
  exact ⟨(facts.2.2.2 x hx y hy).1.mp,(facts.2.2.2 x hx y hy).2.mp⟩

end LogicLineages.PermittedControl.ActualFiniteOrderBranches
