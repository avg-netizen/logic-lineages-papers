module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroTailDeletionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth

def zeroTailDeletion : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}), 0 < γ → StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ (N : ℕ),
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x = 0) →
    let Q := G ⧸ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G)
    Countable Q ∧ (∀ x : Q, ∃ k : ℕ, p^k • x = 0) ∧ IsReducedAddGroup Q ∧
    UlmRanksAgreeBelow p G Q (Ordinal.omega0*γ) ∧
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup Q) = ⊥ ∧
    StagesNonzeroBelow p Q (Ordinal.omega0*γ) ∧
    BackAndForth (2*γ+1) (Fin.elim0 : Fin 0 → G) (Fin.elim0 : Fin 0 → Q) ∧
    ((transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) ≠ ⊥ → ¬ Nonempty (G ≃+ Q))
end LogicLineages.ModelsAlgebra.PGroups.Targets
