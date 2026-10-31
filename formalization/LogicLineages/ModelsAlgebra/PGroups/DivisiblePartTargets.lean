module
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def actualDivisiblePart : Prop :=
  ∀ (G : Type) [AddCommGroup G], SubgroupDivisible (divisiblePart G) ∧
    ∀ S : AddSubgroup G, SubgroupDivisible S → S ≤ divisiblePart G

def infiniteDivisibleSocleAtCuts : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ), p ≠ 0 →
    Cardinal.aleph0 ≤ divisibleSocleRank p G →
    ∀ α : Ordinal.{0}, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
