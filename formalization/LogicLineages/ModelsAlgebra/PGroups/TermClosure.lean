module
public import LogicLineages.ModelsAlgebra.PGroups.TermClosureTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth

theorem term_closure_membership : Targets.groupTermClosureMembership := by
  intro G _ n a t
  induction t with
  | var i => exact AddSubgroup.subset_closure ⟨i,rfl⟩
  | zero => exact (AddSubgroup.closure (Set.range a)).zero_mem
  | neg t ih => exact (AddSubgroup.closure (Set.range a)).neg_mem ih
  | add s t ihs iht => exact (AddSubgroup.closure (Set.range a)).add_mem ihs iht

theorem closure_term_representation : Targets.groupClosureTermRepresentation := by
  intro G _ n a x hx
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i,rfl⟩
    exact ⟨.var i,rfl⟩
  · exact ⟨.zero,rfl⟩
  · intro x y _ _ hx hy
    obtain ⟨s,rfl⟩ := hx
    obtain ⟨t,rfl⟩ := hy
    exact ⟨.add s t,rfl⟩
  · intro x _ hx
    obtain ⟨t,rfl⟩ := hx
    exact ⟨.neg t,rfl⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth
