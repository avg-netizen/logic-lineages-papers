module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual simultaneous extension of compatible homomorphisms on two actual
subgroups into a divisible group. This pays the correction map used in
divisible finite-subgroup homogeneity; no extension conclusion is assumed. -/
def compatibleDivisibleHomExtension : Prop :=
  ∀ (G E : Type) [AddCommGroup G] [AddCommGroup E], GroupDivisible E →
    ∀ (B S : AddSubgroup G) (f : B →+ E) (u : S →+ E),
      (∀ (x : G) (hB : x ∈ B) (hS : x ∈ S), f ⟨x,hB⟩ = u ⟨x,hS⟩) →
      ∃ F : G →+ E, (∀ x : B, F x = f x) ∧ (∀ x : S, F x = u x)
end LogicLineages.ModelsAlgebra.PGroups.Targets
