module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupTerminalExactLength : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (N : ℕ), 0 < N →
    (∀ x : (transfiniteFiltration p δ : AddSubgroup G), p^N • x = 0) →
    (∃ x : (transfiniteFiltration p δ : AddSubgroup G), p^(N-1) • x ≠ 0) →
    (transfiniteFiltration p (δ+(N : Ordinal.{v})) : AddSubgroup G) = ⊥ ∧
    ∀ α < δ+(N : Ordinal.{v}), (transfiniteFiltration p α : AddSubgroup G) ≠ ⊥

end LogicLineages.ModelsAlgebra.PGroups.Targets
