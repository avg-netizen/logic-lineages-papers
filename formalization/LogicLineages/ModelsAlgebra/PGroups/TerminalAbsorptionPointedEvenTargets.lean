module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionPointedEvenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def terminalAbsorptionPointedEven : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (K T : AddSubgroup G) (N b : ℕ),
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) = K ⊔ T → Disjoint K T →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b : AddSubgroup K)) = Cardinal.aleph0 →
    (∀ x : T, p^(b+1) • x=0) →
    ∀ (n : ℕ) (a : Fin n → G),
      AddSubgroup.closure (Set.range a) ⊓ transfiniteFiltration p (Ordinal.omega0*γ) ≤ K →
      BackAndForth (2*γ+2) a (fun i => QuotientAddGroup.mk' T (a i))
end LogicLineages.ModelsAlgebra.PGroups.Targets
