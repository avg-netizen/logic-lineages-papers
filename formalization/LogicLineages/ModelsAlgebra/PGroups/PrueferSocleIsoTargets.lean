module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleIsoDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def prueferSocleIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Nonempty (ZMod p ≃+ pSocle p (⊤ : AddSubgroup (PrueferModel p)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
