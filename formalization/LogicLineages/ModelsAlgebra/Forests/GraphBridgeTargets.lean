module

public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeDefinitions

/-! Exact components of paper03 lem:bridge, independent of Carter's theorem.
The reverse construction and uniqueness are full obligations, not fields
assumed by the embedding theorem. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def ComparabilityForbiddenGraphs : Prop :=
  ∀ F : FiniteOrderForest,
    ¬ Nonempty (fourPath ↪g comparabilityGraph F) ∧
    ¬ Nonempty (fourCycle ↪g comparabilityGraph F)

def ComparabilityGraphRepresentation : Prop :=
  ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    ¬ Nonempty (fourPath ↪g G) → ¬ Nonempty (fourCycle ↪g G) →
    ∃ F : FiniteOrderForest, Nonempty (G ≃g comparabilityGraph F)

def ComparabilityOrderUniqueness : Prop :=
  ∀ F G : FiniteOrderForest,
    Nonempty (comparabilityGraph F ≃g comparabilityGraph G) →
    Nonempty (F.Carrier ≃o G.Carrier)

def ComparabilityEmbeddings : Prop :=
  ∀ F G : FiniteOrderForest,
    Nonempty (F.Carrier ↪o G.Carrier) ↔
    Nonempty (comparabilityGraph F ↪g comparabilityGraph G)

def FullComparabilityBridge : Prop :=
  ComparabilityForbiddenGraphs ∧ ComparabilityGraphRepresentation ∧
    ComparabilityOrderUniqueness ∧ ComparabilityEmbeddings

end LogicLineages.ModelsAlgebra.Forests.Targets
