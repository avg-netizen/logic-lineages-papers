module
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Literal reducedness: no nonzero divisible additive subgroup. -/
def IsReducedAddGroup (G : Type) [AddCommGroup G] : Prop :=
  ∀ S : AddSubgroup G, (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥
end LogicLineages.ModelsAlgebra.PGroups
