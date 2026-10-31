module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferFiniteSocleDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def prueferFiniteSocle : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Finite (pSocle p (⊤ : AddSubgroup (PrueferModel p)))
def finitePrueferPowerSocle : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ),
    Finite (pSocle p (⊤ : AddSubgroup (Fin n → PrueferModel p)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
