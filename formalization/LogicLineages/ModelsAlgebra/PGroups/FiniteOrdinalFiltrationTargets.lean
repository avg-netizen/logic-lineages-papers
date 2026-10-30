module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupFiniteOrdinalFiltration : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p n : ℕ),
    (transfiniteFiltration p (n : Ordinal.{v}) : AddSubgroup G) = finiteFiltration p n

end LogicLineages.ModelsAlgebra.PGroups.Targets
