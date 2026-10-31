module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def walkerScottEndpoints : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (γ:Ordinal.{0}) [Countable γ.ToType] (r:ℕ), 0<r →
    RawDifferenceEndpoint (WalkerOdd p (walkerGammaCut γ) r) (2*γ+1) ∧
    RawDifferenceEndpoint (WalkerEven p (walkerGammaCut γ) r) (2*γ+2) ∧
    Infinite (WalkerEven p (walkerGammaCut γ) r) ∧
    (0<γ → Infinite (WalkerOdd p (walkerGammaCut γ) r))
end LogicLineages.ModelsAlgebra.PGroups.Targets
