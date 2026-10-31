module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroCutScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Genuine unrestricted Scott upper bound, not exact Scott complexity.
Neither reducedness nor a classification/zero-cut oracle is added. -/
def zeroCutScottUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) = ⊥ →
    ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
