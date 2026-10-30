module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupPDivisibleInEveryStage : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (S : AddSubgroup G),
    (∀ x : S, ∃ y : S, p • y = x) →
    ∀ α : Ordinal.{v}, S ≤ (transfiniteFiltration p α : AddSubgroup G)

def groupZeroStageNoPDivisible : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (α : Ordinal.{v}),
    (transfiniteFiltration p α : AddSubgroup G) = ⊥ →
    ∀ S : AddSubgroup G, (∀ x : S, ∃ y : S, p • y = x) → S = ⊥

def groupZeroStageReduced : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ), p ≠ 0 → ∀ α : Ordinal.{v},
    (transfiniteFiltration p α : AddSubgroup G) = ⊥ →
    ∀ S : AddSubgroup G, (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥

end LogicLineages.ModelsAlgebra.PGroups.Targets
