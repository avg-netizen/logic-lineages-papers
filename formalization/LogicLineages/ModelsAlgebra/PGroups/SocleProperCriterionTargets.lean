module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupSocleProperCriterion : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B : AddSubgroup G) (α : Ordinal.{v}),
    ¬Function.Surjective (socleCorrectionClass G p B (transfiniteFiltration p α)) ↔
      ∃ a : G, a ∈ pSocle p (transfiniteFiltration p α) ∧
        a ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) ∧ a ∉ B ∧
        ∀ (b : B) (β : Ordinal.{v}),
          a + b ∈ (transfiniteFiltration p β : AddSubgroup G) →
          a ∈ (transfiniteFiltration p β : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
