module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedScottCompleteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Actual countable reduced primary models, with explicit raw difference endpoint. -/
def AttainedReducedDifference (p:ℕ) (α:Ordinal.{0}) : Prop :=
  ∃ (G:Type) (inst:AddCommGroup G), letI := inst;
    Countable G ∧ (∀x:G,∃k:ℕ,p^k • x=0) ∧ IsReducedAddGroup G ∧ RawDifferenceEndpoint G α
def AttainedInfiniteReducedDifference (p:ℕ) (α:Ordinal.{0}) : Prop :=
  ∃ (G:Type) (inst:AddCommGroup G), letI := inst;
    Countable G ∧ Infinite G ∧ (∀x:G,∃k:ℕ,p^k • x=0) ∧ IsReducedAddGroup G ∧ RawDifferenceEndpoint G α
end LogicLineages.ModelsAlgebra.PGroups
