module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def divisibleHomExtension : Prop :=
  ∀ (G D : Type) [AddCommGroup G] [AddCommGroup D], GroupDivisible D →
    ∀ (S : AddSubgroup G) (f : S →+ D), ∃ g : G →+ D, ∀ x : S, g x = f x
end LogicLineages.ModelsAlgebra.PGroups.Targets
