module

public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeCompletionTargets
public import LogicLineages.ModelsAlgebra.Forests.GraphExclusionProof
public import LogicLineages.ModelsAlgebra.Forests.CanonicalOrderProof
public import LogicLineages.ModelsAlgebra.Forests.TwinIsoProof

/-! The complete finite comparability bridge, paper 03 `lem:bridge`.
The reverse embedding uses the literal induced range suborder, then the proved
order uniqueness theorem; the original graph map need not preserve order. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphBridgeCompletionProof

open GraphBridge

theorem orderEmbeddingGivesGraphEmbedding : Targets.OrderEmbeddingGivesGraphEmbedding := by
  intro F G h
  obtain ⟨e⟩ := h
  refine ⟨⟨e.toEmbedding, ?_⟩⟩
  intro x y
  change (e x ≠ e y ∧ (e x ≤ e y ∨ e y ≤ e x)) ↔
    (x ≠ y ∧ (x ≤ y ∨ y ≤ x))
  constructor
  · rintro ⟨hne, hxy | hyx⟩
    · exact ⟨fun h => hne (congrArg e h), Or.inl (e.le_iff_le.mp hxy)⟩
    · exact ⟨fun h => hne (congrArg e h), Or.inr (e.le_iff_le.mp hyx)⟩
  · rintro ⟨hne, hxy | hyx⟩
    · exact ⟨fun h => hne (e.injective h), Or.inl (e.le_iff_le.mpr hxy)⟩
    · exact ⟨fun h => hne (e.injective h), Or.inr (e.le_iff_le.mpr hyx)⟩

theorem graphEmbeddingGivesOrderEmbedding : Targets.GraphEmbeddingGivesOrderEmbedding := by
  classical
  intro F G h
  obtain ⟨e⟩ := h
  let H : FiniteOrderForest := {
    Carrier := Set.range e
    carrierFintype := Fintype.ofFinite _
    carrierPartialOrder := inferInstance
    forest := fun {x y z} hx hy => G.forest hx hy }
  let t : comparabilityGraph F ≃g comparabilityGraph H := {
    toEquiv := Equiv.ofInjective e e.injective
    map_rel_iff' := by
      intro x y
      constructor
      · rintro ⟨hne, hcmp⟩
        apply e.map_rel_iff.mp
        exact ⟨fun heq => hne (Subtype.ext heq), hcmp⟩
      · intro hxy
        have hg := e.map_rel_iff.mpr hxy
        exact ⟨fun heq => hg.1 (congrArg Subtype.val heq), hg.2⟩ }
  obtain ⟨o⟩ := TwinIsoProof.twinClassOrderUniqueness F H ⟨t⟩
  exact ⟨o.toOrderEmbedding.trans (OrderEmbedding.subtype (Set.range e))⟩

theorem fullComparabilityEmbeddings : Targets.FullComparabilityEmbeddings := by
  intro F G
  exact ⟨orderEmbeddingGivesGraphEmbedding F G, graphEmbeddingGivesOrderEmbedding F G⟩

theorem completeComparabilityBridge : Targets.CompleteComparabilityBridge :=
  ⟨GraphExclusionProof.comparabilityForbiddenGraphs,
    CanonicalOrderProof.canonicalGraphRepresentation,
    TwinIsoProof.twinClassOrderUniqueness, fullComparabilityEmbeddings⟩

end LogicLineages.ModelsAlgebra.Forests.GraphBridgeCompletionProof
