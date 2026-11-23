import Mathlib.Order.Bounds.Basic

namespace LogicLineages.PersistentMarking.PrintedTowerCofinalityOrderProof

open Set

variable {X Y : Type*} [LinearOrder X] [LinearOrder Y]

/-- The printed clause (P), separated from criticality and from leastness. -/
def ControlsBelow (norm collapse : X → Y) (index : X) (candidate : Y) : Prop :=
  ∀ η, η < index → norm η < candidate → collapse η < candidate

/-- Actual inputs to the printed order inference. Neither monotonicity of
collapse on all indices nor the target cofinality equality is assumed. -/
structure TowerInputs (tower : Nat → X) (norm collapse : X → Y) (critical : Y → Prop)
    (floor : Y) (endpoint : X) (limitValue : Y) : Prop where
  indexIncreasing : StrictMono tower
  indexLub : IsLUB (Set.range tower) endpoint
  collapsedLub : IsLUB (Set.range (fun n => collapse (tower n))) limitValue
  normCap : ∀ n, norm (tower n) ≤ floor
  floorBelowTower : ∀ n, floor < collapse (tower n)
  floorBelowEndpoint : floor < collapse endpoint
  atTower : ∀ n, critical (collapse (tower n)) ∧ ControlsBelow norm collapse (tower n) (collapse (tower n))
  atEndpointLeast : IsLeast {y | critical y ∧ ControlsBelow norm collapse endpoint y} (collapse endpoint)
  increasingCriticalClosure : ∀ (s : Nat → Y) (y : Y), StrictMono s →
    (∀ n, critical (s n)) → IsLUB (Set.range s) y → critical y

theorem exact_PrintedTowerCollapseIncreasing {tower : Nat → X} {norm collapse : X → Y}
    {critical : Y → Prop} {floor : Y} {endpoint : X} {limitValue : Y}
    (given : TowerInputs tower norm collapse critical floor endpoint limitValue) :
    StrictMono (fun n => collapse (tower n)) := by
  intro n m below
  exact (given.atTower m).2 (tower n) (given.indexIncreasing below)
    (lt_of_le_of_lt (given.normCap n) (given.floorBelowTower m))

/-- Both strict inequalities can be paid at the very same natural index. -/
theorem exact_MatchedIncreasingLubIndex {a : Nat → X} {b : Nat → Y}
    {endpoint : X} {limitValue : Y} {x : X} {y : Y}
    (aLub : IsLUB (Set.range a) endpoint) (bLub : IsLUB (Set.range b) limitValue)
    (aMono : Monotone a) (bMono : Monotone b)
    (xBelow : x < endpoint) (yBelow : y < limitValue) :
    ∃ n, x < a n ∧ y < b n := by
  obtain ⟨_,⟨i,rfl⟩,left⟩ := (lt_isLUB_iff aLub).1 xBelow
  obtain ⟨_,⟨j,rfl⟩,right⟩ := (lt_isLUB_iff bLub).1 yBelow
  exact ⟨max i j,lt_of_lt_of_le left (aMono (Nat.le_max_left i j)),
    lt_of_lt_of_le right (bMono (Nat.le_max_right i j))⟩

/-- The inference in the printed Tower Cofinality proof, conditional on the
true norm, criticality, least collapse, and actual least upper bounds. -/
theorem exact_PrintedTowerCofinalityOrderInference {tower : Nat → X} {norm collapse : X → Y}
    {critical : Y → Prop} {floor : Y} {endpoint : X} {limitValue : Y}
    (given : TowerInputs tower norm collapse critical floor endpoint limitValue) :
    limitValue = collapse endpoint := by
  have collapsedIncreasing := exact_PrintedTowerCollapseIncreasing given
  have limitCritical : critical limitValue :=
    given.increasingCriticalClosure (fun n => collapse (tower n)) limitValue collapsedIncreasing
      (fun n => (given.atTower n).1) given.collapsedLub
  have limitControls : ControlsBelow norm collapse endpoint limitValue := by
    intro η below normBelow
    obtain ⟨n,before,smallNorm⟩ := exact_MatchedIncreasingLubIndex given.indexLub given.collapsedLub
      given.indexIncreasing.monotone collapsedIncreasing.monotone below normBelow
    have collapsedBelow := (given.atTower n).2 η before smallNorm
    exact lt_of_lt_of_le collapsedBelow (given.collapsedLub.1 ⟨n,rfl⟩)
  have endpointLe : collapse endpoint ≤ limitValue :=
    given.atEndpointLeast.2 (show limitValue ∈ {y | critical y ∧ ControlsBelow norm collapse endpoint y}
      from ⟨limitCritical,limitControls⟩)
  have limitLe : limitValue ≤ collapse endpoint := by
    apply given.collapsedLub.2
    rintro value ⟨n,rfl⟩
    have indexStrict : tower n < endpoint :=
      lt_of_lt_of_le (given.indexIncreasing (Nat.lt_succ_self n)) (given.indexLub.1 ⟨n+1,rfl⟩)
    have normStrict : norm (tower n) < collapse endpoint :=
      lt_of_le_of_lt (given.normCap n) given.floorBelowEndpoint
    exact le_of_lt (given.atEndpointLeast.1.2 (tower n) indexStrict normStrict)
  exact le_antisymm limitLe endpointLe

theorem exact_PrintedTowerEndpointIsLub {tower : Nat → X} {norm collapse : X → Y}
    {critical : Y → Prop} {floor : Y} {endpoint : X} {limitValue : Y}
    (given : TowerInputs tower norm collapse critical floor endpoint limitValue) :
    IsLUB (Set.range (fun n => collapse (tower n))) (collapse endpoint) := by
  rw [← exact_PrintedTowerCofinalityOrderInference given]
  exact given.collapsedLub

#print axioms exact_PrintedTowerCollapseIncreasing
#print axioms exact_MatchedIncreasingLubIndex
#print axioms exact_PrintedTowerCofinalityOrderInference
#print axioms exact_PrintedTowerEndpointIsLub

end LogicLineages.PersistentMarking.PrintedTowerCofinalityOrderProof
