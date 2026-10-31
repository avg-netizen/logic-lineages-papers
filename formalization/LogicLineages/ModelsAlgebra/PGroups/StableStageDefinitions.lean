module
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Equality of two literal consecutive p-filtration subgroups. -/
def StableAt (p : ℕ) (G : Type) [AddCommGroup G] (α : Ordinal.{0}) : Prop :=
  (transfiniteFiltration p α : AddSubgroup G) = transfiniteFiltration p (α+1)
end LogicLineages.ModelsAlgebra.PGroups
