module

public import LogicLineages.ModelsAlgebra.Forests.WidthDefinitions

@[expose] public section

/-!
Fixed source obligations for paper 03, the width paragraph preceding
Theorem `thm:width`. The full JEP classification is a separate unfinished
target. No maximal-extension, antichain-injection or cardinal-bound
supplier is among the hypotheses below.
-/

namespace LogicLineages.ModelsAlgebra.Forests.Targets

universe u

def everyVertexBelowLeaf : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] (x : α),
    ∃ y, x ≤ y ∧ IsMax y

def widthBoundIffLeafBound : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α], IsOrderForest α →
    ∀ m, WidthAtMost α m ↔ (leafFinset α).card ≤ m

end LogicLineages.ModelsAlgebra.Forests.Targets
