module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalTwoEvenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth

def terminalTwoEvenComparison : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ x : H, ∃ k : ℕ, p^k • x = 0) →
    IsReducedAddGroup G → IsReducedAddGroup H →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C) (γ : Ordinal.{0}),
    StagesNonzeroBelow p G (Ordinal.omega0*γ) → StagesNonzeroBelow p H (Ordinal.omega0*γ) →
    UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) → MapCutsExact p f (Ordinal.omega0*γ) →
    ∀ (n : ℕ) (b : Fin n → (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))
      (a : Fin n → (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup H))
      (hb : ∀ i, (b i:G) ∈ B),
    (∀ x : G, x ∈ B → x ∈ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) →
      ∃ i, (b i:G)=x) →
    (∀ i, (a i:H) = (f ⟨b i,hb i⟩:H)) → BackAndForth (2:Ordinal.{0}) a b →
    SubgroupComparison f (2*γ+2)
end LogicLineages.ModelsAlgebra.PGroups.Targets
