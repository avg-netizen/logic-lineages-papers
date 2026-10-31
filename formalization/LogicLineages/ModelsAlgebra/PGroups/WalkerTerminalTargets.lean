module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def walkerSourceTerminal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    Nonempty ((transfiniteFiltration p ξ : AddSubgroup (WalkerSourceGroup p ξ)) ≃+ ZMod p) ∧
      (transfiniteFiltration p (ξ+1) : AddSubgroup (WalkerSourceGroup p ξ)) = ⊥

/-- Final p² conclusion, with countability on the actual source index δ+1. -/
def walkerSourceDoubleTerminal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable (δ+1).ToType],
    Nonempty ((transfiniteFiltration p δ : AddSubgroup (WalkerSourceGroup p (δ+1))) ≃+ ZMod (p^2))

end LogicLineages.ModelsAlgebra.PGroups.Targets
