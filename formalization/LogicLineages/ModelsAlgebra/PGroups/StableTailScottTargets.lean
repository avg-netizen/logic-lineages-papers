module
public import LogicLineages.ModelsAlgebra.PGroups.StableTailScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def stableTailScottUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (N : ℕ),
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    StableAt p (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) (N:Ordinal.{0}) →
    ∃ φ : Formula 0, Complexity .pi (2*γ+3) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
