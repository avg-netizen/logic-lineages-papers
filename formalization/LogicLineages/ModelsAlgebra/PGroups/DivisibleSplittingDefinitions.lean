module
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ReducedUlmClassificationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- An actual retraction onto a specified subgroup, with its inclusion fixed pointwise. -/
def SubgroupRetraction {G : Type} [AddCommGroup G] (D : AddSubgroup G)
    (r : G →+ D) : Prop := ∀ x : D, r x = x
end LogicLineages.ModelsAlgebra.PGroups
