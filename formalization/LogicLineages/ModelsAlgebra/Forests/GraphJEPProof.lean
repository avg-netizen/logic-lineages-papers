module

public import LogicLineages.ModelsAlgebra.Forests.GraphJEPTargets
public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeCompletionProof

/-! Semantic JEP reduction only, paper 03 `thm:decision`. All graph/forest
representation and embedding suppliers are proved dependencies. No decision
algorithm or Carter theorem is assumed or concluded. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphJEPProof

open GraphBridge GraphBridgeCompletionProof

private theorem avoidance_of_iso (U : List FiniteOrderForest) (G H : FiniteSimpleGraph)
    (e : G.graph ≃g H.graph) (h : GraphAvoidsForbidden U G) : GraphAvoidsForbidden U H := by
  have transfer {α : Type} (B : SimpleGraph α) (hb : ¬ Nonempty (B ↪g G.graph)) :
      ¬ Nonempty (B ↪g H.graph) := by
    rintro ⟨f⟩
    exact hb ⟨f.trans e.symm.toEmbedding⟩
  exact ⟨transfer fourPath h.1, transfer fourCycle h.2.1,
    fun B hB => transfer (comparabilityGraph B) (h.2.2 B hB)⟩

theorem graphAvoidanceIsoInvariant : Targets.GraphAvoidanceIsoInvariant := by
  intro U G H e
  exact ⟨avoidance_of_iso U G H e, avoidance_of_iso U H G e.symm⟩

theorem comparabilityAvoidance : Targets.ComparabilityAvoidance := by
  intro U F
  constructor
  · intro h B hB he
    exact h.2.2 B hB (orderEmbeddingGivesGraphEmbedding B F he)
  · intro h
    have hex := GraphExclusionProof.comparabilityForbiddenGraphs F
    exact ⟨hex.1, hex.2, fun B hB he => h B hB (graphEmbeddingGivesOrderEmbedding B F he)⟩

theorem forbiddenGraphRepresented : Targets.ForbiddenGraphRepresented := by
  intro U G h
  obtain ⟨F, ⟨e⟩⟩ := CanonicalOrderProof.canonicalGraphRepresentation
    G.Carrier G.graph h.1 h.2.1
  refine ⟨F, ?_, ⟨e⟩⟩
  exact (comparabilityAvoidance U F).mp
    ((graphAvoidanceIsoInvariant U G (finiteComparabilityGraph F) e).mp h)

theorem forbiddenFamilyJEPEquivalence : Targets.ForbiddenFamilyJEPEquivalence := by
  intro U
  constructor
  · intro hj G H hG hH
    obtain ⟨F, hF, ⟨eG⟩⟩ := forbiddenGraphRepresented U G hG
    obtain ⟨P, hP, ⟨eH⟩⟩ := forbiddenGraphRepresented U H hH
    obtain ⟨K, hK, hf, hg⟩ := hj F P hF hP
    obtain ⟨f⟩ := orderEmbeddingGivesGraphEmbedding F K hf
    obtain ⟨g⟩ := orderEmbeddingGivesGraphEmbedding P K hg
    exact ⟨finiteComparabilityGraph K, (comparabilityAvoidance U K).mpr hK,
      ⟨eG.toEmbedding.trans f⟩, ⟨eH.toEmbedding.trans g⟩⟩
  · intro hj F P hF hP
    obtain ⟨K, hK, ⟨f⟩, ⟨g⟩⟩ := hj (finiteComparabilityGraph F) (finiteComparabilityGraph P)
      ((comparabilityAvoidance U F).mpr hF) ((comparabilityAvoidance U P).mpr hP)
    obtain ⟨H, hH, ⟨e⟩⟩ := forbiddenGraphRepresented U K hK
    exact ⟨H, hH, graphEmbeddingGivesOrderEmbedding F H ⟨f.trans e.toEmbedding⟩,
      graphEmbeddingGivesOrderEmbedding P H ⟨g.trans e.toEmbedding⟩⟩

end LogicLineages.ModelsAlgebra.Forests.GraphJEPProof
