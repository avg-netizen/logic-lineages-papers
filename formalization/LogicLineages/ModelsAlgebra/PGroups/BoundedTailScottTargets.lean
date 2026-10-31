module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def boundedTailScottUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (N : ℕ),
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x = 0) →
    ∃ φ : Formula 0, Complexity .pi (2*γ+3) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
