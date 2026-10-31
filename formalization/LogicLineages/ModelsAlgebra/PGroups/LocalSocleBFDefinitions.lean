module
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteDivisibleBFDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ReducedUlmClassificationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

def SoclesInfiniteBelow (p : ℕ) (G : Type) [AddCommGroup G] (δ : Ordinal.{0}) : Prop :=
  ∀ α < δ, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup G))

/-- Literal length-at-least-cut condition, allowing the cut itself to vanish. -/
def StagesNonzeroBelow (p : ℕ) (G : Type) [AddCommGroup G] (δ : Ordinal.{0}) : Prop :=
  ∀ α < δ, (transfiniteFiltration p α : AddSubgroup G) ≠ ⊥

end LogicLineages.ModelsAlgebra.PGroups
