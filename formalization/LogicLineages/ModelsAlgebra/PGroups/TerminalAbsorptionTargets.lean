module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary

def terminalAbsorptionComparison : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (K T : AddSubgroup G) (N b : ℕ),
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) = K ⊔ T → Disjoint K T →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b : AddSubgroup K)) = Cardinal.aleph0 →
    (∀ x : T, p^(b+1) • x=0) →
    Nonempty ((transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup (G ⧸ T)) ≃+ K) ∧
    BackAndForth (2*γ+2) (Fin.elim0 : Fin 0 → G) (Fin.elim0 : Fin 0 → (G ⧸ T)) ∧
    (∀ j : ℕ,
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
        AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) ≠
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup K)) →
      ¬ Nonempty (G ≃+ (G ⧸ T)))

def terminalAbsorptionNoPi : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (K T : AddSubgroup G) (N b j : ℕ),
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) = K ⊔ T → Disjoint K T →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b : AddSubgroup K)) = Cardinal.aleph0 →
    (∀ x : T, p^(b+1) • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) ≠
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup K)) →
    ∀ φ : Formula 0, Complexity .pi (2*γ+2) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
