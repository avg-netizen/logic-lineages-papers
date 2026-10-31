module
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteDivisibleBFDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def infiniteDivisibleRankBackForth : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    Cardinal.aleph0 ≤ divisibleSocleRank p G → Cardinal.aleph0 ≤ divisibleSocleRank p H →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C),
    (∀ γ : Ordinal.{0}, UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
      MapCutsExact p f (Ordinal.omega0*γ) →
      MapCutsForward p f (Ordinal.omega0*γ+Ordinal.omega0) →
      SubgroupComparison f (2*γ+1)) ∧
    (∀ γ : Ordinal.{0}, UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
      UlmRanksLeInterval p G H (Ordinal.omega0*γ) (Ordinal.omega0*γ+Ordinal.omega0) →
      MapCutsExact p f (Ordinal.omega0*γ+Ordinal.omega0) →
      SubgroupComparison f (2*γ+2)) ∧
    (∀ η : Ordinal.{0}, Order.IsSuccLimit η →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*η) → MapCutsExact p f (Ordinal.omega0*η) →
      SubgroupComparison f η)

/-- Source tuple-induced-map form, with no finite subgroup, independent-family,
cut-socle, extension-system or comparison oracle added as a premise. -/
def infiniteDivisibleRankSource : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    Cardinal.aleph0 ≤ divisibleSocleRank p G → Cardinal.aleph0 ≤ divisibleSocleRank p H →
    ∀ (n : ℕ) (b : Fin n → G) (a : Fin n → H)
      (f : AddSubgroup.closure (Set.range b) ≃+ AddSubgroup.closure (Set.range a)),
    (∀ i, (f ⟨b i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩:H) = a i) →
    (∀ γ : Ordinal.{0}, UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
      MapCutsExact p f (Ordinal.omega0*γ) →
      MapCutsForward p f (Ordinal.omega0*γ+Ordinal.omega0) →
      GroupBackAndForth.BackAndForth (2*γ+1) a b) ∧
    (∀ γ : Ordinal.{0}, UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
      UlmRanksLeInterval p G H (Ordinal.omega0*γ) (Ordinal.omega0*γ+Ordinal.omega0) →
      MapCutsExact p f (Ordinal.omega0*γ+Ordinal.omega0) →
      GroupBackAndForth.BackAndForth (2*γ+2) a b) ∧
    (∀ η : Ordinal.{0}, Order.IsSuccLimit η →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*η) → MapCutsExact p f (Ordinal.omega0*η) →
      GroupBackAndForth.BackAndForth η a b)

end LogicLineages.ModelsAlgebra.PGroups.Targets
