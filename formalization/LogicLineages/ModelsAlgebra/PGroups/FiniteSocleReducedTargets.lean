module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleReducedDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def finiteSocleOmegaStable : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Finite (pSocle p (⊤ : AddSubgroup G))],
    (transfiniteFiltration p ((Ordinal.omega0 : Ordinal.{0})+1) : AddSubgroup G) =
      transfiniteFiltration p (Ordinal.omega0 : Ordinal.{0})

def reducedFiniteSocleFinite : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → IsReducedAddGroup G →
    Finite (pSocle p (⊤ : AddSubgroup G)) → Finite G

def reducedLongLimitInfiniteSocles : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → IsReducedAddGroup G →
    ∀ δ : Ordinal.{0}, Order.IsSuccLimit δ →
    (∀ β < δ, (transfiniteFiltration p β : AddSubgroup G) ≠ ⊥) →
    ∀ α < δ, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
