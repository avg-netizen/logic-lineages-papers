module
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTerminalPointedDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def twoInfiniteTerminalPointed : Prop :=
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
      BackAndForth (2*γ+2) x (fun i => QuotientAddGroup.mk' T (x i))
end LogicLineages.ModelsAlgebra.PGroups.Targets
