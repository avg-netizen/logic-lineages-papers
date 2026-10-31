module
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTerminalDeletionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def twoInfiniteTerminalDeletion : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (N : ℕ) (a b : Fin N), a<b →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0 →
    ∀ (n : ℕ) (x : Fin n → G), ∃ (T : AddSubgroup G) (m : ℕ),
      T ≤ transfiniteFiltration p (Ordinal.omega0*γ) ∧
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*γ+a.val) :
        AddSubgroup (G ⧸ T))) = (m : Cardinal) ∧
      ¬ Nonempty (G ≃+ (G ⧸ T)) ∧
      BackAndForth (2*γ+1) x (fun i => QuotientAddGroup.mk' T (x i)) ∧
      BackAndForth (2*γ+2) (Fin.elim0 : Fin 0 → G) (Fin.elim0 : Fin 0 → (G ⧸ T))
end LogicLineages.ModelsAlgebra.PGroups.Targets
