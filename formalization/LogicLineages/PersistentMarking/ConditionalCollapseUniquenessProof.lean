module

public import LogicLineages.PersistentMarking.ConditionalCollapseUniquenessTargets

public section

namespace LogicLineages.PersistentMarking.ConditionalCollapseUniqueness
open ConditionalTowerCofinality

universe u v

theorem characterizationDeterminesCollapse : CharacterizationDeterminesCollapse.{u,v} := by
  intro I O _ _ _ D D' hn hc hP hP'
  funext ξ
  refine WellFoundedLT.induction (motive := fun ξ => D.psi ξ = D'.psi ξ) ξ ?_
  intro ξ ih
  apply le_antisymm
  · apply (hP ξ).2.2 (D'.psi ξ)
    · rw [hc]
      exact (hP' ξ).1
    · intro η hη hnorm
      rw [ih η hη]
      have hnorm' : D'.norm η < D'.psi ξ := by
        rw [← hn]
        exact hnorm
      exact (hP' ξ).2.1 η hη hnorm'
  · apply (hP' ξ).2.2 (D.psi ξ)
    · rw [← hc]
      exact (hP ξ).1
    · intro η hη hnorm
      rw [← ih η hη]
      have hnorm' : D.norm η < D.psi ξ := by
        rw [hn]
        exact hnorm
      exact (hP ξ).2.1 η hη hnorm'

#print axioms characterizationDeterminesCollapse
end LogicLineages.PersistentMarking.ConditionalCollapseUniqueness
