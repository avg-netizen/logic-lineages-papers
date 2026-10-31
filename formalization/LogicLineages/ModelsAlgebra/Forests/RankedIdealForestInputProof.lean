module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInputTargets
public import LogicLineages.ModelsAlgebra.Forests.GraphJEPStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput.Proof
open ProfileAutomatonEncoding ProfileSourceRegular GraphBridge RankedGraphImage ForestParseRepresentation

theorem encodedGraphExact : Targets.EncodedGraphExact := by
  intro c hc
  ext i j
  change (i ≠ j ∧ (decide (FiniteCode.Rel c i.val j.val) = true ∨
    decide (FiniteCode.Rel c j.val i.val) = true)) ↔
    (i ≠ j ∧ (FiniteCode.Rel c i.val j.val ∨ FiniteCode.Rel c j.val i.val))
  simp only [decide_eq_true_eq]

theorem avoidanceExact : Targets.AvoidanceExact := by
  intro U hU G
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro H hH
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hH
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hA
    have hf : FiniteCode.toForest c (hU c hc) ∈ FiniteCode.toFamily U hU := by
      apply List.mem_map.mpr
      exact ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩
    change ¬ Nonempty (rawGraph (encodeOne c) ↪g G.graph)
    rw [encodedGraphExact c (hU c hc)]
    exact h.2.2 _ hf
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro F hF
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hF
    have hm : rawFinite (encodeOne c.val) ∈ (encode U).map rawFinite := by
      exact List.mem_map.mpr ⟨encodeOne c.val,
        List.mem_map.mpr ⟨c.val, c.property, rfl⟩, rfl⟩
    have hn := h.2.2 _ hm
    change ¬ Nonempty (rawGraph (encodeOne c.val) ↪g G.graph) at hn
    rw [encodedGraphExact c.val (hU c.val c.property)] at hn
    exact hn

theorem forestJEPExact : Targets.ForestJEPExact := by
  intro U hU
  rw [LogicLineages.ModelsAlgebra.Forests.StatementChecks.forbiddenFamilyJEPEquivalence
    (FiniteCode.toFamily U hU)]
  constructor
  · intro hj G H hG hH
    have hG' := (avoidanceExact U hU (bridgeGraph G)).mpr hG
    have hH' := (avoidanceExact U hU (bridgeGraph H)).mpr hH
    obtain ⟨K, hK, hGK, hHK⟩ := hj (bridgeGraph G) (bridgeGraph H) hG' hH'
    exact ⟨pack K, (avoidanceExact U hU K).mp hK, hGK, hHK⟩
  · intro hj G H hG hH
    obtain ⟨K, hK, hGK, hHK⟩ := hj (pack G) (pack H)
      ((avoidanceExact U hU G).mp hG) ((avoidanceExact U hU H).mp hH)
    exact ⟨bridgeGraph K, (avoidanceExact U hU (bridgeGraph K)).mpr hK, hGK, hHK⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput.Proof
