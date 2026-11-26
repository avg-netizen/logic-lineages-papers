module
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteGlobalTail
open PreparedProjection MixedSameRankResidue
open ActualZeroClassCommonTail ActualNodeTailSupply

private theorem finiteMax_le {α : Type} (cost : α → Nat) (items : List α) (bound : Nat)
    (one : ∀ a ∈ items, cost a ≤ bound) : finiteMax cost items ≤ bound := by
  induction items with
  | nil => exact Nat.zero_le _
  | cons a items ih =>
      change max (cost a) (finiteMax cost items) ≤ bound
      exact max_le (one a List.mem_cons_self) (ih (fun b hit => one b (List.mem_cons_of_mem _ hit)))

private theorem leFiniteMax {α : Type} (cost : α → Nat) (items : List α) (a : α)
    (member : a ∈ items) : cost a ≤ finiteMax cost items := by
  induction items with
  | nil => cases member
  | cons head rest ih =>
      change cost a ≤ max (cost head) (finiteMax cost rest)
      rcases List.mem_cons.mp member with eq | tail
      · subst a
        exact Nat.le_max_left _ _
      · exact (ih tail).trans (Nat.le_max_right _ _)

private theorem finiteMaxSubset {α : Type} (cost : α → Nat) (left right : List α)
    (subset : ∀ a ∈ left, a ∈ right) : finiteMax cost left ≤ finiteMax cost right :=
  finiteMax_le cost left _ (fun a ha => leFiniteMax cost right a (subset a ha))

private theorem termLabelIgnoresWeight (t : WeightedOperand) :
    prefixLabel t = prefixLabel (1,t.2) := by
  obtain ⟨w,op⟩ := t
  cases op <;> rfl

private theorem prefixSubset (terms : List WeightedOperand) (alphabet : List LowerOperand)
    (covers : ∀ t ∈ terms, t.2 ∈ alphabet) :
    ∀ p ∈ prefixLabels terms, p ∈ prefixLabels (unitTerms alphabet) := by
  intro p member
  obtain ⟨t,present,label⟩ := List.mem_filterMap.mp member
  have unit : ((1,t.2) : WeightedOperand) ∈ unitTerms alphabet :=
    List.mem_map.mpr ⟨t.2,covers t present,rfl⟩
  exact List.mem_filterMap.mpr ⟨(1,t.2),unit,(termLabelIgnoresWeight t).symm.trans label⟩

private theorem annotationDominance (terms : List WeightedOperand) (alphabet : List LowerOperand)
    (covers : ∀ t ∈ terms, t.2 ∈ alphabet) :
    annotationTail terms ≤ annotationTail (unitTerms alphabet) := by
  let cost := fun w : WeightedCode => annotationBoundCode w.2
  change finiteMax cost (terms.map encodeWeighted) ≤ finiteMax cost ((unitTerms alphabet).map encodeWeighted)
  apply finiteMax_le
  intro w member
  obtain ⟨t,present,encoded⟩ := List.mem_map.mp member
  subst w
  have unit : ((1,t.2) : WeightedOperand) ∈ unitTerms alphabet :=
    List.mem_map.mpr ⟨t.2,covers t present,rfl⟩
  have code : encodeWeighted (1,t.2) ∈ (unitTerms alphabet).map encodeWeighted :=
    List.mem_map.mpr ⟨(1,t.2),unit,rfl⟩
  exact leFiniteMax cost ((unitTerms alphabet).map encodeWeighted) (encodeWeighted (1,t.2)) code

private theorem commonDominance (B : Nat) (terms : List WeightedOperand) (alphabet : List LowerOperand)
    (covers : ∀ t ∈ terms, t.2 ∈ alphabet) :
    commonTail B terms ≤ commonTail B (unitTerms alphabet) := by
  let labels := prefixLabels terms
  let all := prefixLabels (unitTerms alphabet)
  have subset : ∀ p ∈ labels, p ∈ all := prefixSubset terms alphabet covers
  change max (finiteMax (prefixAffordability B) labels)
      (finiteMax (fun anchor => finiteMax (labelPairTail B anchor) labels) labels) ≤
    max (finiteMax (prefixAffordability B) all)
      (finiteMax (fun anchor => finiteMax (labelPairTail B anchor) all) all)
  apply max_le_max (finiteMaxSubset (prefixAffordability B) labels all subset)
  apply finiteMax_le
  intro anchor member
  exact (finiteMaxSubset (labelPairTail B anchor) labels all subset).trans
    (leFiniteMax (fun a => finiteMax (labelPairTail B a) all) all anchor (subset anchor member))

theorem exactAlphabetTailDominance : ExactAlphabetTailDominance := by
  intro B terms alphabet covers
  exact max_le_max (annotationDominance terms alphabet covers)
    (commonDominance B terms alphabet covers)

end LogicLineages.PermittedControl.ActualFiniteGlobalTail
