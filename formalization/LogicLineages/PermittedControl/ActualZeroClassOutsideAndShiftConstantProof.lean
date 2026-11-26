module
public import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftTargets
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftStepProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutsideAndShift
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualRankedZeroClass
open ActualCountOriginDispositions

private theorem countOriginsCons (f : Nat → Nat) (C : Nat) (rd : Read) (xs : List Read)
    (ann : Annotation) (annotations : List Annotation) :
    countOrigins f C (rd::xs) (ann::annotations) =
      if fullValue f ann = some C ∧ isCountAnnotation ann = true then
        (rd,ann) :: countOrigins f C xs annotations
      else countOrigins f C xs annotations := by
  by_cases full : fullValue f ann = some C <;> by_cases count : isCountAnnotation ann = true <;>
    simp [countOrigins,classLedger,full,count]

theorem exactOriginShift : ExactOriginShift := by
  intro f ρ C xs annotations anchor ledger out aligned disposed
  induction xs generalizing annotations ledger out with
  | nil =>
      cases aligned
      change DisposedOrigins f ρ anchor [] ledger out at disposed
      cases disposed
      rfl
  | cons rd xs next =>
      cases annotations with
      | nil => cases aligned
      | cons ann annotations =>
          change AlignedAnnotations f ρ (rd.1 :: xs.map Prod.fst) (rd.2 :: xs.map Prod.snd)
            (ann::annotations) at aligned
          cases aligned with
          | cons _ _ actual rest =>
              by_cases kept : fullValue f ann = some C ∧ isCountAnnotation ann = true
              · rw [countOriginsCons,if_pos kept] at disposed
                cases disposed with
                | cons head remaining =>
                    have localShift := initialShiftAtCount f ρ C rd ann anchor _ _
                      actual kept.1 kept.2 head
                    have tailShift := next annotations _ _ rest remaining
                    change (replaceOccurrence f C rd.1 rd.2 ann).2 +
                      (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 = _
                    rw [localShift,tailShift]
                    rfl
              · rw [countOriginsCons,if_neg kept] at disposed
                have tailShift := next annotations ledger out rest disposed
                change (replaceOccurrence f C rd.1 rd.2 ann).2 +
                  (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 = _
                rw [noUnselectedShift f C rd ann kept,zero_add,tailShift]

end LogicLineages.PermittedControl.ActualZeroClassOutsideAndShift
