module
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorDifferenceTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerScottProof
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorParityProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
theorem successor_difference_realization : Targets.successorDifferenceRealization := by
  intro p _ β hc
  obtain ⟨γ,hγ,heq⟩ := countable_successor_parity β hc
  letI : Countable γ.ToType := hγ
  have h := walker_scott_endpoints p γ 1 (by decide)
  have hn := walker_gamma_source_construction p γ 1 (by decide)
  rcases heq with heq|heq
  · refine ⟨WalkerOdd p (walkerGammaCut γ) 1,inferInstance,hn.1.1,hn.1.2.1,hn.1.2.2,?_,?_⟩
    · rw [heq]; exact h.1
    · intro htwo
      have hpos : 0<γ := by
        apply lt_of_le_of_ne zero_le
        intro hz
        have he : β+1=1 := by simpa only [←hz,mul_zero,zero_add] using heq
        rw [he] at htwo
        exact (not_le_of_gt (one_lt_two : (1:Ordinal.{0})<2)) htwo
      exact h.2.2.2 hpos
  · refine ⟨WalkerEven p (walkerGammaCut γ) 1,inferInstance,hn.2.1.1,hn.2.1.2.1,hn.2.1.2.2,?_,fun _=>h.2.2.1⟩
    rw [heq]; exact h.2.1
end LogicLineages.ModelsAlgebra.PGroups
