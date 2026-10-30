module

public import LogicLineages.ModelsAlgebra.Forests.AgeDefinitions
public import Mathlib.ModelTheory.Order

/-! Literal single-≤ relational presentation for the age construction. Neither
partial-order laws nor foresthood are assumed on arbitrary bundled structures. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeConstruction

open FirstOrder

abbrev OrderModel := CategoryTheory.Bundled.{0} Language.order.Structure

def orderModel (α : Type) [LE α] : OrderModel :=
  ⟨α, Language.orderStructure α⟩

def ForestModelClass (K : FiniteOrderForest → Prop) : Set OrderModel :=
  { M | ∃ F, K F ∧ Nonempty (orderModel F.Carrier ≃[Language.order] M) }

end LogicLineages.ModelsAlgebra.Forests.AgeConstruction
