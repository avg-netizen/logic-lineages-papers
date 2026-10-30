module

public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeTargets

/-! Final actual-embedding and complete-bridge contracts for paper 03
`lem:bridge`. The reverse direction asserts existence of an order embedding,
not that the supplied graph map preserves order. No root/meet condition occurs.
No Carter/JEP/decision conclusion is asserted here. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def OrderEmbeddingGivesGraphEmbedding : Prop :=
  ∀ F G : FiniteOrderForest,
    Nonempty (F.Carrier ↪o G.Carrier) → Nonempty (comparabilityGraph F ↪g comparabilityGraph G)

def GraphEmbeddingGivesOrderEmbedding : Prop :=
  ∀ F G : FiniteOrderForest,
    Nonempty (comparabilityGraph F ↪g comparabilityGraph G) → Nonempty (F.Carrier ↪o G.Carrier)

def FullComparabilityEmbeddings : Prop := ComparabilityEmbeddings

def CompleteComparabilityBridge : Prop := FullComparabilityBridge

end LogicLineages.ModelsAlgebra.Forests.Targets
