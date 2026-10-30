module

public import LogicLineages.ModelsAlgebra.Forests.AgeModelDefinitions

/-! Exact actual-order/relational calibration. The pullback target constructs
foresthood for arbitrary relational structures, rather than assuming it. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open FirstOrder AgeConstruction

def OrderModelEmbeddingCalibration : Prop :=
  ∀ (α β : Type) [PartialOrder α] [PartialOrder β],
    Nonempty (α ↪o β) ↔
      Nonempty (orderModel α ↪[Language.order] orderModel β)

def OrderModelIsoCalibration : Prop :=
  ∀ (α β : Type) [PartialOrder α] [PartialOrder β],
    Nonempty (α ≃o β) ↔
      Nonempty (orderModel α ≃[Language.order] orderModel β)

def RelationalFiniteForestPullback : Prop :=
  ∀ (M : OrderModel) (F : FiniteOrderForest),
    Nonempty (M ↪[Language.order] orderModel F.Carrier) →
      ∃ G : FiniteOrderForest,
        Nonempty (G.Carrier ↪o F.Carrier) ∧
        Nonempty (orderModel G.Carrier ≃[Language.order] M)

end LogicLineages.ModelsAlgebra.Forests.Targets
