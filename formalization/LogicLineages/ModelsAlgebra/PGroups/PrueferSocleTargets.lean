module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def independentPrueferInfiniteSocles : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι G : Type) [Infinite ι] [AddCommGroup G]
    (e : DirectSum ι (fun _ => PrueferModel p) →+ G), Function.Injective e →
    SubgroupDivisible e.range ∧ e.range ≤ divisiblePart G ∧
      Infinite (pSocle p (divisiblePart G)) ∧
      ∀ α : Ordinal.{0}, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
