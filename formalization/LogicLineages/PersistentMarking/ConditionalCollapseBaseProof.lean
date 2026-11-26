module

public import LogicLineages.PersistentMarking.ConditionalCollapseBaseTargets

public section

namespace LogicLineages.PersistentMarking.ConditionalCollapseBase
open ConditionalTowerCofinality

universe u v

theorem collapseAtMinimalIndex : CollapseAtMinimalIndex.{u,v} := by
  intro I O _ _ D hP ξ hmin
  refine ⟨(hP ξ).1,?_⟩
  intro θ hθ
  exact (hP ξ).2.2 θ hθ (fun η hη _ => absurd hη (hmin η))

theorem collapseAboveMinimalValue : CollapseAboveMinimalValue.{u,v} := by
  intro I O _ _ D hP ξ₀ hmin ξ
  exact (collapseAtMinimalIndex I O D hP ξ₀ hmin).2 (D.psi ξ) (hP ξ).1

theorem collapseIncreasingOnSmallNorm : CollapseIncreasingOnSmallNorm.{u,v} := by
  intro I O _ _ D hP ξ₀ hmin η ξ hη hnorm
  exact (hP ξ).2.1 η hη (lt_of_lt_of_le hnorm (collapseAboveMinimalValue I O D hP ξ₀ hmin ξ))

#print axioms collapseAtMinimalIndex
#print axioms collapseAboveMinimalValue
#print axioms collapseIncreasingOnSmallNorm
end LogicLineages.PersistentMarking.ConditionalCollapseBase
