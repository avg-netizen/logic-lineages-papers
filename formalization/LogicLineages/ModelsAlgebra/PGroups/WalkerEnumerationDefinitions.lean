module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeDefinitions
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.Finset.Sort
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Exact ancestor-before-child enumeration of all actual source nodes. -/
def WalkerAncestorEnumeration (ξ : Ordinal.{0}) (I : Type) [LT I]
    (e : I ≃ WalkerOrdinalNode ξ) : Prop :=
  ∀ i j : I, walkerOrdinalParent ξ (e i) = some (e j) → j < i

end LogicLineages.ModelsAlgebra.PGroups
