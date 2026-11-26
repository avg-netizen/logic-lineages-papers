module
public import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
open PreparedProjection
open ActualZeroSuccessorPrefixPlan (erase)
open ActualZeroClassReplacement (Read)
open ActualZeroClassCohortTransfer (SurvivingPrefix MovedPrefixes anchorRead subtractRead)
open ActualCountOriginDispositions (MovedAt)
open ActualShortCountCleanup (shortLength retained shortShift)

private theorem someMoves (f ρ : Nat → Nat) (a : SurvivingPrefix) (ps : List SurvivingPrefix)
    (moved : List Read) (run : MovedPrefixes f ρ a ps moved) :
    moved.map Prod.fst = (ps.map erase).flatMap (moveOne (erase a)) := by
  induction run with
  | nil => rfl
  | @same p ps tail rank _ _ ih =>
      simp only [List.map_cons,List.flatMap_cons,moveOne,erase,if_pos rank,anchorTerm,
        List.cons_append,List.nil_append,anchorRead,ih]
  | @higher p ps tail i above _ _ _ ih =>
      have different : p.rank ≠ a.rank := ne_of_gt above
      simp only [List.map_cons,List.flatMap_cons,moveOne,erase,if_neg different,anchorTerm,movedTerm,
        List.cons_append,List.nil_append,anchorRead,subtractRead,ih]

theorem exactMovedAndCleanupSyntax : ExactMovedAndCleanupSyntax := by
  constructor
  · intro f ρ anchor ps moved actual
    cases anchor with
    | none =>
        obtain ⟨rfl,rfl⟩ := actual
        rfl
    | some a => exact someMoves f ρ a ps moved actual
  · intro before
    induction before with
    | nil => exact ⟨rfl,rfl⟩
    | cons rd rest ih =>
        refine ⟨?_,?_⟩
        · have tail := ih.1
          simp only [retained,cleanSyntax] at tail
          by_cases keep : shortLength rd.1.2 = 0 <;>
            simp [retained,cleanSyntax,keep,tail]
        · change rd.1.1 * (shortLength rd.1.2 : Int) + shortShift rest =
            rd.1.1 * (shortLength rd.1.2 : Int) + cleanupShift (rest.map Prod.fst)
          rw [ih.2]

end LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
