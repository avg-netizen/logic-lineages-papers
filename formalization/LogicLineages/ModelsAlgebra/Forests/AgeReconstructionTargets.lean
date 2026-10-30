module

public import LogicLineages.ModelsAlgebra.Forests.AgeReconstructionDefinitions

/-! All finite forest patches force the actual global order/forest laws.
Relational age equality supplies the patches, rather than assuming them. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open FirstOrder AgeConstruction

def FinitePatchesForestOrder : Prop :=
  ∀ (α : Type) (R : α → α → Prop), HasFiniteForestPatches α R →
    ∃ po : PartialOrder α, @IsOrderForest α po ∧
      ∀ x y, @LE.le α po.toLE x y ↔ R x y

def ForestModelAgeFinitePatches : Prop :=
  ∀ K (M : OrderModel), Language.order.age M = ForestModelClass K →
    HasFiniteForestPatches M (modelLE M)

def CountableForestModelReconstruction : Prop :=
  ∀ K (M : OrderModel), Countable M →
    Language.order.age M = ForestModelClass K →
    ∃ A : CountableOrderForest,
      Nonempty (orderModel A.Carrier ≃[Language.order] M)

end LogicLineages.ModelsAlgebra.Forests.Targets
