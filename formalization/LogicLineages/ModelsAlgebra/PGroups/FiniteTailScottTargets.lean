module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def finiteTailScottUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) →
    Finite (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) →
    ∃ d : DifferenceFormula 0, d.AtLevel (2*γ+1) ∧
      RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
