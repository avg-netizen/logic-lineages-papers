module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamilyUlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Complete original odd/even invariant table, for every countable δ and all r.
No length, classification or Scott-complexity conclusion is assumed or asserted. -/
def walkerFamilyUlmTable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType], ∀ r : ℕ, ∀ α : Ordinal.{0},
    (Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerOdd p δ r))) =
      if α < δ then Cardinal.aleph0 else if α = δ then (r : Cardinal) else 0) ∧
    (Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerEven p δ r))) =
      if α < δ then Cardinal.aleph0 else if α = δ then (r : Cardinal)
      else if α = δ+1 then Cardinal.aleph0 else 0)
end LogicLineages.ModelsAlgebra.PGroups.Targets
