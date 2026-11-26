module
public import LogicLineages.PermittedControl.ActualZeroClassReplacementTargets
import LogicLineages.PermittedControl.ActualZeroClassReplacementTermProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumRowProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassReplacement
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum

private theorem liftedAppend (f : Nat → Nat) (ρ : Nat → Nat) (xs ys : List Read)
    (left : liftedReads f ρ xs) (right : liftedReads f ρ ys) :
    liftedReads f ρ (xs ++ ys) := by
  induction xs with
  | nil => exact right
  | cons head xs next =>
      obtain ⟨actual,encoded,tail⟩ := left
      exact ⟨actual,encoded,next tail⟩

private theorem readSumAppend (xs ys : List Read) :
    readSum (xs ++ ys) = readSum xs + readSum ys := by
  induction xs with
  | nil => simp [readSum,actualSum]
  | cons head xs next =>
      change head.1.1 * (head.2 : Int) + readSum (xs ++ ys) =
        (head.1.1 * (head.2 : Int) + readSum xs) + readSum ys
      rw [next,add_assoc]

theorem exactRetainedRemainder : ExactRetainedRemainder := by
  intro f B selected ρ C terms values annotations aligned ready
  induction aligned with
  | nil => exact ⟨True.intro,rfl⟩
  | @cons t terms v values ann annotations actual encoded annotation _ next =>
      obtain ⟨headReady,tailReady⟩ := ready
      obtain ⟨headReads,headValue⟩ :=
        exactOccurrenceReplacement f B selected ρ C t v ann actual encoded annotation headReady
      obtain ⟨tailReads,tailValue⟩ := next tailReady
      let head := replaceOccurrence f C t v ann
      let tail := replaceRow f C terms values annotations
      change liftedReads f ρ (head.1.toList ++ tail.1) ∧
        (head.2 + tail.2) + readSum (head.1.toList ++ tail.1) =
          (contribution f C t v ann).2 + (rowParts f C terms values annotations).2
      refine ⟨liftedAppend f ρ _ _ headReads tailReads,?_⟩
      change head.2 + readSum head.1.toList = (contribution f C t v ann).2 at headValue
      change tail.2 + readSum tail.1 = (rowParts f C terms values annotations).2 at tailValue
      rw [readSumAppend,← headValue,← tailValue]
      ac_rfl

theorem exactZeroClassReplacement : ExactZeroClassReplacement := by
  intro f B selected ρ z C c terms values annotations aligned ready raw member largest dominates zero
  obtain ⟨reads,remainder⟩ := exactRetainedRemainder f B selected ρ C terms values annotations aligned ready
  obtain ⟨doubled,_⟩ := exactSignedDecomposition f B selected ρ z C c terms values annotations
    aligned raw member largest dominates
  let out := replaceRow f C terms values annotations
  let parts := rowParts f C terms values annotations
  change 2 * (c + actualSum terms values) = parts.1 * (C : Int) + 2 * (c + parts.2) at doubled
  change parts.1 = 0 at zero
  rw [zero,zero_mul,zero_add] at doubled
  change out.2 + readSum out.1 = parts.2 at remainder
  refine ⟨reads,?_⟩
  change c + actualSum terms values = (c + out.2) + readSum out.1
  omega

end LogicLineages.PermittedControl.ActualZeroClassReplacement
