module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailLowerDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def finiteTailNoPi : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}), 0<γ →
    Finite (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) →
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) ≠ ⊥ →
    ∀ φ : Formula 0, Complexity .pi (2*γ+1) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
