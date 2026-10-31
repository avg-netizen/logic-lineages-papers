module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v w
/-- The actual embedded direct sum of subgroups, not a stipulated coordinate condition. -/
noncomputable def directSumSubgroup {ι : Type u} {G : ι → Type v}
    [∀ i, AddCommGroup (G i)] (S : ∀ i, AddSubgroup (G i)) :
    AddSubgroup (DirectSum ι G) :=
  (DirectSum.map (fun i => (S i).subtype)).range
end LogicLineages.ModelsAlgebra.PGroups
