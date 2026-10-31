module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionCompleteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth

def terminalDeletionSourceLemma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (K T : AddSubgroup G) (N : ℕ),
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) = K ⊔ T →
    Disjoint K T → 0 < N →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x = 0) →
    (∃ x : K, p^(N-1) • x ≠ 0) →
    UlmRanksAgreeBelow p G (G ⧸ T) (Ordinal.omega0*γ) ∧
    Nonempty ((transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup (G ⧸ T)) ≃+ K) ∧
    IsReducedAddGroup (G ⧸ T) ∧
    ((transfiniteFiltration p (Ordinal.omega0*γ+N) : AddSubgroup G) = ⊥ ∧
      (transfiniteFiltration p (Ordinal.omega0*γ+N) : AddSubgroup (G ⧸ T)) = ⊥) ∧
    (∀ α < Ordinal.omega0*γ+N,
      (transfiniteFiltration p α : AddSubgroup G) ≠ ⊥ ∧
      (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) ≠ ⊥) ∧
    (∀ (n : ℕ) (a : Fin n → G),
      AddSubgroup.closure (Set.range a) ⊓ transfiniteFiltration p (Ordinal.omega0*γ) ≤ K →
      BackAndForth (2*γ+1) a (fun i => (QuotientAddGroup.mk' T) (a i))) ∧
    (BackAndForth (2:Ordinal.{0})
      (fun i : Fin 0 => (Fin.elim0 i : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G)))
      (fun i : Fin 0 => (Fin.elim0 i : K)) →
      BackAndForth (2*γ+2)
        (fun i : Fin 0 => (Fin.elim0 i : G))
        (fun i : Fin 0 => (Fin.elim0 i : G ⧸ T)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
