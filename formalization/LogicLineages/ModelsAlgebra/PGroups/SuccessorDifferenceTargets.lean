module
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorDifferenceDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def successorDifferenceRealization : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (β:Ordinal.{0}), Countable (β+1).ToType →
    ∃ (G:Type) (inst:AddCommGroup G), letI := inst;
      Countable G ∧ (∀x:G,∃k:ℕ,p^k • x=0) ∧ IsReducedAddGroup G ∧
      RawDifferenceEndpoint G (β+1) ∧ (2≤β+1 → Infinite G)
end LogicLineages.ModelsAlgebra.PGroups.Targets
