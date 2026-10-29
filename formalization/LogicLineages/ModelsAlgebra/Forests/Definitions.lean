module

public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

/-! The actual source definition of an order forest: predecessors of
any one point form a chain. No finite-tree representation is assumed. -/

namespace LogicLineages.ModelsAlgebra.Forests

def IsOrderForest (α : Type*) [PartialOrder α] : Prop :=
  ∀ ⦃x y z : α⦄, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x

end LogicLineages.ModelsAlgebra.Forests
