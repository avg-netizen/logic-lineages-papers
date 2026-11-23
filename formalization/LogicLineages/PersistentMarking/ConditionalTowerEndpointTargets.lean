module

public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalTowerEndpoint
open ConditionalTowerCofinality

universe u v

/-- The endpoint is the supremum of the tower arguments (`Λ = sup a_n`),
from "below" and "cofinal" alone. -/
def TowerEndpointIsSupremum : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    TowerHypotheses D → IsLUB (Set.range D.a) D.endpoint

/-- Every collapse value along the tower lies strictly below the collapse
at the endpoint. -/
def TowerValuesBelowEndpoint : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    TowerHypotheses D → ∀ n, D.psi (D.a n) < D.psi D.endpoint

/-- The supremum of the collapse values along the tower is not attained:
no tower term's value equals it. (The printed remark after `thm:height`:
"No individual term has been assigned rank BH", at the level of the tower
values.) -/
def TowerSupremumNotAttained : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    TowerHypotheses D →
    ∀ θ, IsLUB (Set.range (fun n => D.psi (D.a n))) θ → ∀ n, D.psi (D.a n) < θ

end LogicLineages.PersistentMarking.ConditionalTowerEndpoint
