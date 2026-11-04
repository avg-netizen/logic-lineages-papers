module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentCompilationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Proof
open SourceMachineConjunctionPlan SourceGroundBinderFragment

theorem tail_fragment (e : Nat) : PlanFragment (tail e) := by
  apply scale_fragment e
  exact ⟨graph_fragment _,graph_fragment _,trivial⟩

theorem actualAggregateFragment : Targets.ActualAggregateFragment := by
  intro b e
  have hp : PlanFragment (plan b e) := by
    apply constructorPreservation.2.1
    apply constructorPreservation.2.1
    apply constructorPreservation.2.1
    exact tail_fragment e
  refine ⟨hp,?_⟩
  apply SourceGroundBinderFragment.Proof.literalAggregate
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  exact compilerPreservation _ _ hp g hg
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Proof
