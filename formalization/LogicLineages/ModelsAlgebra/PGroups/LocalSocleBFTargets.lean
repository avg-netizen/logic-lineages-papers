module
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def localSocleBackForth : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C),
    (∀ γ : Ordinal.{0},
      SoclesInfiniteBelow p G (Ordinal.omega0*γ) →
      SoclesInfiniteBelow p H (Ordinal.omega0*γ+Ordinal.omega0) →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) → MapCutsExact p f (Ordinal.omega0*γ) →
      MapCutsForward p f (Ordinal.omega0*γ+Ordinal.omega0) → SubgroupComparison f (2*γ+1)) ∧
    (∀ γ : Ordinal.{0},
      SoclesInfiniteBelow p G (Ordinal.omega0*γ+Ordinal.omega0) →
      SoclesInfiniteBelow p H (Ordinal.omega0*γ+Ordinal.omega0) →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
      UlmRanksLeInterval p G H (Ordinal.omega0*γ) (Ordinal.omega0*γ+Ordinal.omega0) →
      MapCutsExact p f (Ordinal.omega0*γ+Ordinal.omega0) → SubgroupComparison f (2*γ+2)) ∧
    (∀ η : Ordinal.{0}, Order.IsSuccLimit η →
      SoclesInfiniteBelow p G (Ordinal.omega0*η) → SoclesInfiniteBelow p H (Ordinal.omega0*η) →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*η) → MapCutsExact p f (Ordinal.omega0*η) →
      SubgroupComparison f η)

def reducedLongBackForth : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    IsReducedAddGroup G → IsReducedAddGroup H →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C),
    (∀ γ : Ordinal.{0},
      StagesNonzeroBelow p G (Ordinal.omega0*γ) →
      StagesNonzeroBelow p H (Ordinal.omega0*γ+Ordinal.omega0) →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) → MapCutsExact p f (Ordinal.omega0*γ) →
      MapCutsForward p f (Ordinal.omega0*γ+Ordinal.omega0) → SubgroupComparison f (2*γ+1)) ∧
    (∀ γ : Ordinal.{0},
      StagesNonzeroBelow p G (Ordinal.omega0*γ+Ordinal.omega0) →
      StagesNonzeroBelow p H (Ordinal.omega0*γ+Ordinal.omega0) →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
      UlmRanksLeInterval p G H (Ordinal.omega0*γ) (Ordinal.omega0*γ+Ordinal.omega0) →
      MapCutsExact p f (Ordinal.omega0*γ+Ordinal.omega0) → SubgroupComparison f (2*γ+2)) ∧
    (∀ η : Ordinal.{0}, Order.IsSuccLimit η →
      StagesNonzeroBelow p G (Ordinal.omega0*η) → StagesNonzeroBelow p H (Ordinal.omega0*η) →
      UlmRanksAgreeBelow p G H (Ordinal.omega0*η) → MapCutsExact p f (Ordinal.omega0*η) →
      SubgroupComparison f η)

/-- The exact limit-cut comparison used at source630–645; the cut may vanish. -/
def reducedLimitCutComparison : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    IsReducedAddGroup G → IsReducedAddGroup H →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C) (γ : Ordinal.{0}),
    StagesNonzeroBelow p G (Ordinal.omega0*γ) → StagesNonzeroBelow p H (Ordinal.omega0*γ) →
    UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) → MapCutsExact p f (Ordinal.omega0*γ) →
    SubgroupComparison f (2*γ)

end LogicLineages.ModelsAlgebra.PGroups.Targets
