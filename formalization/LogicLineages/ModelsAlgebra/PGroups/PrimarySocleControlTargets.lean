module
public import LogicLineages.ModelsAlgebra.PGroups.PrimarySocleControlDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def primarySocleInjectivity : Prop :=
  ∀ (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → ∀ f : G →+ H,
    Function.Injective (fun x : pSocle p (⊤ : AddSubgroup G) => f (x:G)) →
    Function.Injective f
def primaryDivisibleSocleSurjectivity : Prop :=
  ∀ (p : ℕ) (G D : Type) [AddCommGroup G] [AddCommGroup D], p ≠ 0 →
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → GroupDivisible D → ∀ f : D →+ G,
    (∀ x : pSocle p (⊤ : AddSubgroup G), ∃ y : D, f y = (x:G)) →
    Function.Surjective f
end LogicLineages.ModelsAlgebra.PGroups.Targets
