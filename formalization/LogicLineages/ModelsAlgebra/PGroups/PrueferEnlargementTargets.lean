module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferEnlargementDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def prueferModelCountable : Prop := ∀ p : ℕ, Countable (PrueferModel p)
def prueferEnlargementData : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) →
    Countable (G×PrueferModel p) ∧
    (∀ x:G×PrueferModel p, ∃ k:ℕ, p^k • x=0) ∧
    (∀ (α:Ordinal.{0}) (x:G×PrueferModel p),
      x ∈ (transfiniteFiltration p α : AddSubgroup (G×PrueferModel p)) ↔
      x.1 ∈ (transfiniteFiltration p α : AddSubgroup G)) ∧
    (∀ α:Ordinal.{0},
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (G×PrueferModel p))) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)))
def reducedPrueferEnlargementNoniso : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime],
    IsReducedAddGroup G → ¬ Nonempty (G ≃+ (G×PrueferModel p))
end LogicLineages.ModelsAlgebra.PGroups.Targets
