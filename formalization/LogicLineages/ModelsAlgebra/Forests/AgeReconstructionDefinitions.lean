module

public import LogicLineages.ModelsAlgebra.Forests.AgeModelDefinitions

/-! Finite patches of a literal binary relation, without order axioms as data. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeConstruction

open FirstOrder

def HasFiniteForestPatches (α : Type) (R : α → α → Prop) : Prop :=
  ∀ s : Finset α, ∃ F : FiniteOrderForest,
    ∃ f : { x : α // x ∈ s } ↪ F.Carrier,
      ∀ x y, f x ≤ f y ↔ R x.val y.val

def modelLE (M : OrderModel) (x y : M) : Prop :=
  Language.Structure.RelMap (L := Language.order) Language.orderRel.le ![x, y]

end LogicLineages.ModelsAlgebra.Forests.AgeConstruction
