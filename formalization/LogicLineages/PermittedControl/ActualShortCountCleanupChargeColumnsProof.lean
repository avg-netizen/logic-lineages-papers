module
public import LogicLineages.PermittedControl.ActualShortCountCleanupChargeTargets
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace LogicLineages.PermittedControl.ActualShortCountCleanupCharge
open scoped Classical
open ActualZeroClassReplacement ActualWeightedReadNormalization ActualRankedRowColumns
open InnerTerminationTargets ActualShortCountCleanup
open SelectedNonlinearImageBounds (NonlinearField)

theorem exactCleanupGroupedCoefficients : ExactCleanupGroupedCoefficients := by
  intro before op
  induction before with
  | nil =>
      by_cases test : shortLength op = 0 <;> simp [retained,groupedWeights,test]
  | cons rd xs ih =>
      by_cases keep : shortLength rd.1.2 = 0
      · have listEq : retained (rd::xs) = rd :: retained xs := by simp [retained,keep]
        rw [listEq]
        by_cases test : shortLength op = 0
        · simp only [groupedWeights,Finsupp.add_apply,ih,if_pos test]
        · have ne : rd.1.2 ≠ op := by
            intro eq
            apply test
            rw [← eq]
            exact keep
          simp only [groupedWeights,Finsupp.add_apply,ih,if_neg test,Finsupp.single_apply,
            if_neg ne,add_zero]
      · have listEq : retained (rd::xs) = retained xs := by simp [retained,keep]
        rw [listEq,ih]
        by_cases test : shortLength op = 0
        · have ne : rd.1.2 ≠ op := by
            intro eq
            apply keep
            rw [eq]
            exact test
          simp only [groupedWeights,Finsupp.add_apply,if_pos test,Finsupp.single_apply,
            if_neg ne,zero_add]
        · simp only [if_neg test]

theorem exactCleanupCharge : ExactCleanupCharge := by
  intro r constant before
  dsimp only
  let src := rankedRow r constant before
  let out := rankedRow r (constant + shortShift before) (retained before)
  have srcCoeff := exactRankedCoefficients r constant before
  have outCoeff := exactRankedCoefficients r (constant + shortShift before) (retained before)
  have valEq : out.value = src.value := by
    apply Finsupp.ext
    intro k
    by_cases nonlin : NonlinearField k.2
    · have keep : shortLength (valueOperand r k) = 0 := rfl
      rw [outCoeff.2.2.1 k nonlin,srcCoeff.2.2.1 k nonlin,
        exactCleanupGroupedCoefficients before (valueOperand r k),if_pos keep]
    · rw [outCoeff.2.2.2.1 k nonlin,srcCoeff.2.2.2.1 k nonlin]
  have cntEq : out.count = src.count.filter (fun k => shortLength (countOperand r k) = 0) := by
    apply Finsupp.ext
    intro k
    rw [outCoeff.2.1 k,Finsupp.filter_apply,srcCoeff.2.1 k,
      exactCleanupGroupedCoefficients before (countOperand r k)]
  have subset : out.count.support ⊆ src.count.support := by
    rw [cntEq,Finsupp.support_filter]
    exact Finset.filter_subset _ _
  have weak : countCharge out ≤ countCharge src :=
    Finset.sum_le_sum_of_subset subset
  have same : valueCount out = valueCount src := by
    unfold valueCount
    rw [valEq]
  exact ⟨valEq,cntEq,subset,weak,same⟩

end LogicLineages.PermittedControl.ActualShortCountCleanupCharge
