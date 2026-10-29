module

public import LogicLineages.ModelsAlgebra.Forests.CoreDefinitions

@[expose] public section

/-! Fixed comparison statements, independent of the proof module.
These are elementary dependencies of paper 03, not its full JEP theorem. -/

namespace LogicLineages.ModelsAlgebra.Forests.CoreTargets

open Core

universe u v

def incomparableNoCommonUpper : Prop :=
  ∀ (α : Type u) (r : α → α → Prop), PredChain r →
    ∀ x y, Incomparable r x y → ¬ ∃ z, r x z ∧ r y z

def embeddingPreservesForest : Prop :=
  ∀ (α : Type u) (β : Type v) (r : α → α → Prop) (s : β → β → Prop)
    (f : α → β), InducedEmbedding r s f → PredChain s → PredChain r

def embeddingPreservesComparabilityGraph : Prop :=
  ∀ (α : Type u) (β : Type v) (r : α → α → Prop) (s : β → β → Prop)
    (f : α → β), InducedEmbedding r s f →
    InducedEmbedding (ComparableAdj r) (ComparableAdj s) f

end LogicLineages.ModelsAlgebra.Forests.CoreTargets
