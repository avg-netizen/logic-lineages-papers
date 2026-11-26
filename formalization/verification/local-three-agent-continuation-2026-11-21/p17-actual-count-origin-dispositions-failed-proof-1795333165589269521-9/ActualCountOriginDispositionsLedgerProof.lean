module
public import LogicLineages.PermittedControl.ActualCountOriginDispositionsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountOriginDispositions
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open ActualRankedZeroClass

theorem originSurvivorsCons (f : Nat → Nat) (C : Nat) (entry : Origin) (entries : List Origin) :
    originSurvivors f C (entry::entries) =
      (survivingPrefix f C entry.1.1 entry.2).toList ++ originSurvivors f C entries := by
  cases found : survivingPrefix f C entry.1.1 entry.2 <;> simp [originSurvivors,found]

private theorem countOriginsCons (f : Nat → Nat) (C : Nat) (rd : Read) (xs : List Read)
    (ann : Annotation) (annotations : List Annotation) :
    countOrigins f C (rd::xs) (ann::annotations) =
      if fullValue f ann = some C ∧ isCountAnnotation ann = true then
        (rd,ann) :: countOrigins f C xs annotations
      else countOrigins f C xs annotations := by
  by_cases full : fullValue f ann = some C <;> by_cases count : isCountAnnotation ann = true <;>
    simp [countOrigins,classLedger,full,count]

private theorem notSelectedMiss (f : Nat → Nat) (C : Nat) (rd : Read) (ann : Annotation)
    (outside : ¬ (fullValue f ann = some C ∧ isCountAnnotation ann = true)) :
    survivingPrefix f C rd.1 ann = none := by
  cases ann with
  | zeroWeight => rfl
  | linear => rfl
  | ordinary q => rfl
  | count i q κ =>
      have different : f q ≠ C := by
        intro same
        exact outside ⟨by simp [fullValue,same],rfl⟩
      cases shape : rd.1.2 <;> simp [survivingPrefix,shape,different]

theorem exactCountOrigins : ExactCountOrigins := by
  intro f B ρ C xs annotations aligned ready
  induction xs generalizing annotations with
  | nil =>
      cases aligned
      simp [countOrigins,classLedger,originSurvivors,cohort]
  | cons rd xs next =>
      cases annotations with
      | nil => cases aligned
      | cons ann annotations =>
          change AlignedAnnotations f ρ (rd.1 :: xs.map Prod.fst) (rd.2 :: xs.map Prod.snd)
            (ann::annotations) at aligned
          cases aligned with
          | cons actual read annotation rest =>
              obtain ⟨headReady,restReady⟩ := ready
              obtain ⟨tailPaid,tailEqual⟩ := next annotations rest restReady
              dsimp only
              by_cases kept : fullValue f ann = some C ∧ isCountAnnotation ann = true
              · rw [countOriginsCons,if_pos kept]
                refine ⟨?_,?_⟩
                · intro entry member
                  rcases List.mem_cons.mp member with equal | tail
                  · subst entry
                    exact ⟨actual,read,annotation,kept.1,headReady,kept.2⟩
                  · exact tailPaid entry tail
                · rw [originSurvivorsCons,tailEqual]
                  rfl
              · rw [countOriginsCons,if_neg kept]
                refine ⟨tailPaid,?_⟩
                rw [tailEqual]
                change cohort f C (xs.map Prod.fst) annotations =
                  (survivingPrefix f C rd.1 ann).toList ++ cohort f C (xs.map Prod.fst) annotations
                rw [notSelectedMiss f C rd ann kept,Option.toList_none,List.nil_append]

end LogicLineages.PermittedControl.ActualCountOriginDispositions
