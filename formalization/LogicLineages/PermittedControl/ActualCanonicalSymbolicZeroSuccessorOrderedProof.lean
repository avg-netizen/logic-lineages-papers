module
public import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorTargets
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataProof
import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassAlignmentProof
import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanCohortProof
import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorMovedProof
import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorOutsideProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessor
open ActualZeroClassReplacement ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow
open ActualFullValueLabels ActualFullValueMaximalMetadata ActualZeroSuccessorMarkedClass
open ActualZeroSuccessorPrefixPlan ActualSymbolicZeroSuccessor ActualShortCountCleanup

theorem exactOrderedSuccessorErasure : ExactOrderedSuccessorErasure := by
  intro f B chosen ρ C constant xs anns a moved
  dsimp only
  intro aligned paid active matching maximum zero moves
  let terms := xs.map Prod.fst
  let vals := xs.map Prod.snd
  let ps := cohort f C terms anns
  let ms := actualMarked f C terms anns
  let before := outsideCohort f C terms vals anns ++ moved
  let shift := (replaceRow f C terms vals anns).2
  obtain ⟨D,maxValue,flags,_,_⟩ :=
    exactActualMaximalMetadata f B chosen ρ terms vals anns aligned paid active a matching
  have same : D = C := Option.some.inj (maxValue.symm.trans maximum)
  subst D
  have marks : decorate terms (classFlags (labels terms) a) = some ms := by
    rw [flags]
    exact exactActualDecoration f B chosen ρ terms vals anns aligned paid C
  obtain ⟨kept,delta⟩ :=
    exactOutsideAndOriginShiftSyntax f B chosen ρ C terms vals anns aligned paid
  obtain ⟨cohortExact,anchorExact⟩ :=
    exactSelectedCohortSyntax f B chosen ρ C terms vals anns aligned paid
  have moving := exactMovedAndCleanupSyntax.1 f ρ (leastPrefix ps) ps moved moves
  have frames : before.map Prod.fst =
      outsideSyntax ms ++ movedSyntax (leastSyntax (cohortSyntax ms)) (cohortSyntax ms) := by
    change (outsideCohort f C terms vals anns ++ moved).map Prod.fst = _
    rw [List.map_append,← kept,moving,anchorExact,cohortExact]
  have cleanup := exactMovedAndCleanupSyntax.2 before
  have literal : successorFromMarks constant ms =
      some ⟨constant + shift + shortShift before,(retained before).map Prod.fst⟩ := by
    unfold successorFromMarks
    rw [delta]
    change some (SyntaxState.mk
      (constant+shift+cleanupShift (outsideSyntax ms ++ movedSyntax (leastSyntax (cohortSyntax ms)) (cohortSyntax ms)))
      (cleanSyntax (outsideSyntax ms ++ movedSyntax (leastSyntax (cohortSyntax ms)) (cohortSyntax ms)))) = _
    rw [← frames,← cleanup.1,← cleanup.2]
  change orderedSuccessor constant terms a = _
  rw [orderedSuccessor,if_pos zero]
  simp only [marks,Option.bind_some]
  exact literal

end LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessor
