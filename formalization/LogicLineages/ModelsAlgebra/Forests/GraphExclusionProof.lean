module

public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeTargets

/-! The forbidden-graph direction of paper03 lem:bridge.
The middle vertex of a comparable two-edge path with incomparable endpoints
must lie below both endpoints. Two consecutive such forks would force the
middle vertices equal, excluding both induced P4 and induced C4. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphExclusionProof

open GraphBridge

theorem incomparable_fork_bottom (F : FiniteOrderForest) (a b c : F.Carrier)
    (hab : a ≤ b ∨ b ≤ a) (hbc : b ≤ c ∨ c ≤ b)
    (hac : ¬ a ≤ c) (hca : ¬ c ≤ a) : b ≤ a ∧ b ≤ c := by
  rcases hab with hab | hba
  · rcases hbc with hbc | hcb
    · exact False.elim (hac (le_trans hab hbc))
    · rcases F.forest hab hcb with hac' | hca'
      · exact False.elim (hac hac')
      · exact False.elim (hca hca')
  · rcases hbc with hbc | hcb
    · exact ⟨hba, hbc⟩
    · exact False.elim (hca (le_trans hcb hba))

theorem nonadjacent_incomparable (F : FiniteOrderForest) (a c : F.Carrier)
    (hne : a ≠ c) (hnot : ¬ (comparabilityGraph F).Adj a c) :
    ¬ a ≤ c ∧ ¬ c ≤ a := by
  constructor
  · intro hac
    exact hnot ⟨hne, Or.inl hac⟩
  · intro hca
    exact hnot ⟨hne, Or.inr hca⟩

theorem no_four_pattern (F : FiniteOrderForest) (H : SimpleGraph (Fin 4))
    (h01 : H.Adj 0 1) (h12 : H.Adj 1 2) (h23 : H.Adj 2 3)
    (h02 : ¬ H.Adj 0 2) (h13 : ¬ H.Adj 1 3) :
    ¬ Nonempty (H ↪g comparabilityGraph F) := by
  rintro ⟨e⟩
  have h01' : (comparabilityGraph F).Adj (e 0) (e 1) := e.map_rel_iff.mpr h01
  have h12' : (comparabilityGraph F).Adj (e 1) (e 2) := e.map_rel_iff.mpr h12
  have h23' : (comparabilityGraph F).Adj (e 2) (e 3) := e.map_rel_iff.mpr h23
  have hn02 : ¬ (comparabilityGraph F).Adj (e 0) (e 2) :=
    fun h => h02 (e.map_rel_iff.mp h)
  have hn13 : ¬ (comparabilityGraph F).Adj (e 1) (e 3) :=
    fun h => h13 (e.map_rel_iff.mp h)
  have hi02 := nonadjacent_incomparable F (e 0) (e 2)
    (fun h => (by decide : (0 : Fin 4) ≠ 2) (e.injective h)) hn02
  have hi13 := nonadjacent_incomparable F (e 1) (e 3)
    (fun h => (by decide : (1 : Fin 4) ≠ 3) (e.injective h)) hn13
  have hb := incomparable_fork_bottom F (e 0) (e 1) (e 2)
    h01'.2 h12'.2 hi02.1 hi02.2
  have hc := incomparable_fork_bottom F (e 1) (e 2) (e 3)
    h12'.2 h23'.2 hi13.1 hi13.2
  have he : e 1 = e 2 := le_antisymm hb.2 hc.1
  exact (by decide : (1 : Fin 4) ≠ 2) (e.injective he)

theorem comparabilityForbiddenGraphs : Targets.ComparabilityForbiddenGraphs := by
  intro F
  constructor
  · apply no_four_pattern F fourPath <;> (unfold fourPath; decide)
  · apply no_four_pattern F fourCycle <;> (unfold fourCycle; decide)

end LogicLineages.ModelsAlgebra.Forests.GraphExclusionProof
