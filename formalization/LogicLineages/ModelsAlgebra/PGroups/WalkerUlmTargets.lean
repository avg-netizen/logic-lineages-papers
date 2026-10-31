module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Every original Walker group contributes one dimension at its own height. -/
def walkerTerminalUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p ξ : AddSubgroup (WalkerSourceGroup p ξ))) = 1
/-- Source lower reservoir invariant display, including all later zero stages. -/
def walkerReservoirUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType], ∀ α : Ordinal.{0},
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerLowerReservoir p δ))) =
      if α < δ then Cardinal.aleph0 else 0
end LogicLineages.ModelsAlgebra.PGroups.Targets
