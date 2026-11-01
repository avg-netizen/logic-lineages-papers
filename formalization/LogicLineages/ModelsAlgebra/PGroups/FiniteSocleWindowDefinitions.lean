module
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.StableStageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- The actual p-power torsion subgroup, with no presentation promise. -/
def powerTorsion (G:Type) [AddCommGroup G] (p n:ℕ) : AddSubgroup G :=
  (nsmulAddMonoidHom (p^n):G→+G).ker
end LogicLineages.ModelsAlgebra.PGroups
