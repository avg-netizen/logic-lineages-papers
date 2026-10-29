module
public import LogicLineages.OrdinalComparison.ActualCollapseBoundsTargets
public import LogicLineages.OrdinalComparison.ActualCollapse
public import LogicLineages.OrdinalComparison.FiniteTail

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualFiniteTailClosureNorm : Targets.ActualFiniteTailClosureNorm := by
  intro a ha k
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  have ht := (finiteTailCorrect r k).1
  rw [hr] at ht
  constructor
  · rw [← ht]
    exact normalRepresentationSound (finiteTail r k)
  · rw [← ht, actualOrdinalNorm_notationCorrespondence (finiteTail r k),
      (finiteTailCorrect r k).2, ← actualOrdinalNorm_notationCorrespondence r, hr]

theorem actualCollapseDominatesNorm : Targets.ActualCollapseDominatesNorm := by
  intro a ha
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  rw [← hr, actualOrdinalNorm_notationCorrespondence r, actualCollapse_notationCorrespondence r]
  exact collapseDominatesNorm r

theorem actualCollapseFiniteTailBound : Targets.ActualCollapseFiniteTailBound := by
  intro a ha k
  have ht := actualFiniteTailClosureNorm a ha k
  have hb := actualCollapseDominatesNorm _ ht.1
  rw [ht.2] at hb
  exact (Nat.le_add_left k (actualOrdinalNorm a)).trans hb

end LogicLineages.OrdinalComparison
