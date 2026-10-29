module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.Hom.Basic
public import LogicLineages.ModelsAlgebra.Forests.Definitions

@[expose] public section

/-!
# Order forests and their comparability graphs

The forest predicate is exactly the predecessor-chain condition in
paper 03. Order and graph embeddings are the standard Mathlib objects.
The reverse graph-to-order embedding-existence theorem and Carter's
algorithm are not assumed by this module.
-/

namespace LogicLineages.ModelsAlgebra.Forests

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- Foresthood is hereditary under order embeddings. -/
theorem isOrderForest_of_orderEmbedding (f : α ↪o β)
    (h : IsOrderForest β) : IsOrderForest α := by
  intro x y z hxz hyz
  rcases h (f.monotone hxz) (f.monotone hyz) with hxy | hyx
  · exact Or.inl (f.le_iff_le.mp hxy)
  · exact Or.inr (f.le_iff_le.mp hyx)

/-- The induced comparability graph retains all positive and negative
comparability facts. -/
def comparabilityGraph (α : Type*) [PartialOrder α] : SimpleGraph α where
  Adj x y := x ≠ y ∧ (x ≤ y ∨ y ≤ x)
  symm := by
    intro x y h
    exact ⟨Ne.symm h.1, h.2.symm⟩
  loopless := by simp

/-- An order embedding induces an induced graph embedding. This is
the forward implication of paper 03's bridge lemma. -/
def comparabilityEmbedding (f : α ↪o β) :
    comparabilityGraph α ↪g comparabilityGraph β where
  toEmbedding := f.toEmbedding
  map_rel_iff' := by
    intro x y
    change (f x ≠ f y ∧ (f x ≤ f y ∨ f y ≤ f x)) ↔
      (x ≠ y ∧ (x ≤ y ∨ y ≤ x))
    simp only [ne_eq, f.injective.eq_iff, f.le_iff_le]

end LogicLineages.ModelsAlgebra.Forests
