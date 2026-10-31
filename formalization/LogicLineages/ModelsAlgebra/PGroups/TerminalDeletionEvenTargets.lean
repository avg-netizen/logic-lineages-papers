module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionEvenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth

def terminalDeletionEven : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (K T : AddSubgroup G) (N : ℕ),
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) = K ⊔ T →
    Disjoint K T → 0 < N →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x = 0) →
    (∃ x : K, p^(N-1) • x ≠ 0) →
    BackAndForth (2:Ordinal.{0})
      (fun i : Fin 0 => (Fin.elim0 i : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G)))
      (fun i : Fin 0 => (Fin.elim0 i : K)) →
    BackAndForth (2*γ+2)
      (fun i : Fin 0 => (Fin.elim0 i : G))
      (fun i : Fin 0 => (Fin.elim0 i : G ⧸ T))
end LogicLineages.ModelsAlgebra.PGroups.Targets
