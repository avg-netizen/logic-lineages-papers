module
public import LogicLineages.PermittedControl.ActualZeroClassCommonTailTargets
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassCommonTail
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open SelectedCountOnlyClass (prefixTarget)

private theorem leFiniteMax {α : Type} (cost : α → Nat) (xs : List α) (a : α)
    (member : a ∈ xs) : cost a ≤ finiteMax cost xs := by
  induction xs with
  | nil => cases member
  | cons head tail ih =>
      change cost a ≤ max (cost head) (finiteMax cost tail)
      rcases List.mem_cons.mp member with equal | rest
      · subst a
        exact Nat.le_max_left _ _
      · exact (ih rest).trans (Nat.le_max_right _ _)

private theorem headLabel (f : Nat → Nat) (C : Nat) (term : WeightedOperand)
    (ann : Annotation) (p : SurvivingPrefix) (found : survivingPrefix f C term ann = some p) :
    prefixLabel term = some (survivorLabel p) := by
  obtain ⟨w, op⟩ := term
  cases ann with
  | zeroWeight => cases found
  | linear => cases found
  | ordinary q => cases found
  | count i q κ =>
      cases op with
      | coordinate rank => cases found
      | ordinary rank F => cases found
      | count rank lam mu =>
          by_cases keep : f q = C ∧ i ≠ 0 ∧ shortGapLength lam (prefixTarget mu) = 0
          · simp only [survivingPrefix, if_pos keep, Option.some.injEq] at found
            subst p
            rfl
          · simp only [survivingPrefix, if_neg keep] at found
            cases found

theorem exactCohortLabelProvenance : ExactCohortLabelProvenance := by
  intro f C terms annotations
  induction terms generalizing annotations with
  | nil => simp [cohort]
  | cons term terms ih =>
      cases annotations with
      | nil => simp [cohort]
      | cons ann anns =>
          intro p member
          change p ∈ (survivingPrefix f C term ann).toList ++ cohort f C terms anns at member
          rcases List.mem_append.mp member with front | back
          · exact List.mem_filterMap.mpr ⟨term, List.mem_cons_self,
              headLabel f C term ann p (Option.mem_toList.mp front)⟩
          · obtain ⟨prior, inTail, label⟩ := List.mem_filterMap.mp (ih anns p back)
            exact List.mem_filterMap.mpr ⟨prior, List.mem_cons_of_mem _ inTail, label⟩

private theorem headReady (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (t : WeightedOperand) (ann : Annotation)
    (paid : ∀ label, prefixLabel t = some label → prefixAffordability B label ≤ ρ label.rank) :
    PrefixTailReady f B ρ C t ann := by
  obtain ⟨w, op⟩ := t
  cases ann with
  | zeroWeight => trivial
  | linear => trivial
  | ordinary q => trivial
  | count i q κ =>
      cases op with
      | coordinate rank => trivial
      | ordinary rank F => trivial
      | count rank lam mu =>
          intro _ _ _
          exact paid ⟨rank,lam,prefixTarget mu⟩ rfl

private theorem readyOfLabels (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    {terms : List WeightedOperand} {values : List Nat} {anns : List Annotation}
    (aligned : AlignedAnnotations f ρ terms values anns)
    (paid : ∀ label ∈ prefixLabels terms, prefixAffordability B label ≤ ρ label.rank) :
    Ready f B ρ C terms anns := by
  induction aligned with
  | nil => exact True.intro
  | @cons t terms v values a anns _ _ _ _ ih =>
      constructor
      · exact headReady f B ρ C t a (fun l tagged =>
          paid l (List.mem_filterMap.mpr ⟨t, List.mem_cons_self, tagged⟩))
      · apply ih
        intro l member
        obtain ⟨prior, inTail, tagged⟩ := List.mem_filterMap.mp member
        exact paid l (List.mem_filterMap.mpr ⟨prior, List.mem_cons_of_mem _ inTail, tagged⟩)

theorem exactCommonTailGuards : ExactCommonTailGuards := by
  intro f B ρ C terms values anns aligned paid
  let labels := prefixLabels terms
  have prefixBound (l : PrefixLabel) (member : l ∈ labels) :
      prefixAffordability B l ≤ commonTail B terms :=
    (leFiniteMax (prefixAffordability B) labels l member).trans (Nat.le_max_left _ _)
  have pairBound (a p : PrefixLabel) (am : a ∈ labels) (pm : p ∈ labels) :
      labelPairTail B a p ≤ commonTail B terms :=
    (leFiniteMax (labelPairTail B a) labels p pm).trans
      ((leFiniteMax (fun q => finiteMax (labelPairTail B q) labels) labels a am).trans
        (Nat.le_max_right _ _))
  refine ⟨readyOfLabels f B ρ C aligned (fun l lm => (prefixBound l lm).trans (paid l lm)), ?_⟩
  intro a chosen p member _
  have am : survivorLabel a ∈ labels :=
    exactCohortLabelProvenance f C terms anns a (exactLeastPrefix.2 _ a chosen).1
  have pm : survivorLabel p ∈ labels := exactCohortLabelProvenance f C terms anns p member
  have hab := pairBound (survivorLabel a) (survivorLabel p) am pm
  exact ⟨hab.trans (paid (survivorLabel a) am), hab.trans (paid (survivorLabel p) pm)⟩

theorem fullActualZeroClassCommonTail : FullActualZeroClassCommonTail :=
  ⟨exactCohortLabelProvenance, exactCommonTailGuards⟩

end LogicLineages.PermittedControl.ActualZeroClassCommonTail
