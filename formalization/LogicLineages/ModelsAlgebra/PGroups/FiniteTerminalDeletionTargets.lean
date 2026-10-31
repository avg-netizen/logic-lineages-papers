module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTerminalDeletionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def finiteTerminalDeletion : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (N : ℕ),
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Infinite (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) →
    ∀ (n : ℕ) (a : Fin n → G), ∃ T : AddSubgroup G,
      T ≤ transfiniteFiltration p (Ordinal.omega0*γ) ∧
      Finite (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup (G ⧸ T)) ∧
      ¬ Nonempty (G ≃+ (G ⧸ T)) ∧
      BackAndForth (2*γ+1) a (fun i => QuotientAddGroup.mk' T (a i))
end LogicLineages.ModelsAlgebra.PGroups.Targets
