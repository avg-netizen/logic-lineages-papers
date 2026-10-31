module
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteTerminalSigmaDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def infiniteTerminalNoSigma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (N : ℕ),
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Infinite (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+2) φ → ¬ GroupScottSentence G φ

def infiniteTerminalNoRawSigma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (N : ℕ),
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Infinite (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+2) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
