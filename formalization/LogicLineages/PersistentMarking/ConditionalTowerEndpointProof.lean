module

public import LogicLineages.PersistentMarking.ConditionalTowerEndpointTargets
import LogicLineages.PersistentMarking.ConditionalTowerCofinalityProof

public section

namespace LogicLineages.PersistentMarking.ConditionalTowerEndpoint
open ConditionalTowerCofinality

universe u v

theorem towerEndpointIsSupremum : TowerEndpointIsSupremum.{u,v} := by
  intro I O _ _ D h
  constructor
  · rintro _ ⟨n,rfl⟩
    exact le_of_lt (h.below n)
  · intro b hb
    by_contra hlt
    obtain ⟨n,hn⟩ := h.cofinal b (lt_of_not_ge hlt)
    exact absurd (hb ⟨n,rfl⟩) (not_le_of_gt hn)

theorem towerValuesBelowEndpoint : TowerValuesBelowEndpoint.{u,v} := by
  intro I O _ _ D h n
  exact (h.characterization D.endpoint).2.1 (D.a n) (h.below n)
    (lt_of_le_of_lt (h.normBound n)
      (h.criticalAboveOne _ (h.characterization D.endpoint).1))

theorem towerSupremumNotAttained : TowerSupremumNotAttained.{u,v} := by
  intro I O _ _ D h θ hθ n
  have mono := conditionalTowerIncreasing I O D h
  exact lt_of_lt_of_le (mono (Nat.lt_succ_self n)) (hθ.1 ⟨n + 1,rfl⟩)

#print axioms towerEndpointIsSupremum
#print axioms towerValuesBelowEndpoint
#print axioms towerSupremumNotAttained
end LogicLineages.PersistentMarking.ConditionalTowerEndpoint
