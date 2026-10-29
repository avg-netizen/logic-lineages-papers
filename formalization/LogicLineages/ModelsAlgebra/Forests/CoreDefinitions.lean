module

@[expose] public section

/-!
# Relational definitions for finite-order-forest reasoning

These definitions use only Lean core. The predecessor-chain condition
is the condition in the paper's definition of an order forest. The
elementary facts proved separately need no additional partial-order law.
This module does not define the full graph-class or JEP decision target.
-/

namespace LogicLineages.ModelsAlgebra.Forests.Core

universe u v

def PredChain {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ ⦃x y z : α⦄, r x z → r y z → r x y ∨ r y x

def Incomparable {α : Type u} (r : α → α → Prop) (x y : α) : Prop :=
  ¬ r x y ∧ ¬ r y x

def ComparableAdj {α : Type u} (r : α → α → Prop) (x y : α) : Prop :=
  x ≠ y ∧ (r x y ∨ r y x)

def InducedEmbedding {α : Type u} {β : Type v}
    (r : α → α → Prop) (s : β → β → Prop) (f : α → β) : Prop :=
  Function.Injective f ∧ ∀ x y, s (f x) (f y) ↔ r x y

end LogicLineages.ModelsAlgebra.Forests.Core
