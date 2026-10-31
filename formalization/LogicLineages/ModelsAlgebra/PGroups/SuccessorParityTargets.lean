module
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorParityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def countableSuccessorParity : Prop :=
  ∀ β:Ordinal.{0}, Countable (β+1).ToType →
    ∃ γ:Ordinal.{0}, Countable γ.ToType ∧ (β+1=2*γ+1 ∨ β+1=2*γ+2)
end LogicLineages.ModelsAlgebra.PGroups.Targets
