module
public import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorTargets
import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorMovedProof
import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorOutsideProof
import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassAlignmentProof
import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanCohortProof
import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchSupportProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxSkeletonProof
import LogicLineages.PermittedControl.ActualFullValueLabelsProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataVectorProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataFlagsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroSuccessorMarkedClass (Marked decorate actualMarked exactActualDecoration)
open ActualZeroSuccessorPrefixPlan (erase cohortSyntax leastSyntax exactSelectedCohortSyntax)
open ActualZeroClassCohortTransfer (cohort leastPrefix)
open ActualZeroClassReplacement (Read replaceRow)
open ActualZeroClassRecombinedRow (outsideCohort)
open ActualReadChargeIteration (ReadState)
open ActualShortCountCleanup (retained shortShift)
open ActualFullValueLabels (labels exactFullValueLabels)
open ActualFiniteFullValueGuards (Matches pairs)
open ActualFullValueMaximalMetadata (classFlags exactMatchedNumericVector exactNumericMaximumFlags)
open ActualFiniteSignedNodeBranch (nodeLabels nodeCoefficient chosenCoefficient)
open ActualMixedRowLeadingAnnotations (fullValues)
open ActualRankedNormalizationSyntax (normalizedTerms exactNormalizedTermSkeleton)

private theorem sameLength {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

private theorem assembleMarked (constant shift outConst : Int) (ms : List Marked)
    (before out : List Read)
    (delta : originShifts ms = some shift)
    (beforeEq : before.map Prod.fst =
      outsideSyntax ms ++ movedSyntax (leastSyntax (cohortSyntax ms)) (cohortSyntax ms))
    (shiftEq : outConst = constant + shift + shortShift before)
    (readEq : out = retained before) :
    successorFromMarks constant ms = some ⟨outConst,out.map Prod.fst⟩ := by
  let terms := outsideSyntax ms ++ movedSyntax (leastSyntax (cohortSyntax ms)) (cohortSyntax ms)
  have clean := exactMovedAndCleanupSyntax.2 before
  have K : constant + shift + cleanupShift terms = outConst := by
    rw [show terms = before.map Prod.fst from beforeEq.symm,← clean.2]
    exact shiftEq.symm
  have termsExact : cleanSyntax terms = out.map Prod.fst := by
    rw [show terms = before.map Prod.fst from beforeEq.symm,← clean.1,readEq]
  unfold successorFromMarks
  rw [delta]
  change some (SyntaxState.mk (constant+shift+cleanupShift terms) (cleanSyntax terms)) = _
  exact congrArg some (congrArg₂ SyntaxState.mk K termsExact)

theorem exactActualSymbolicZeroSuccessor : ExactActualSymbolicZeroSuccessor := by
  intro f B hf θ r top source out raw a rawEq edge matched
  obtain ⟨xs,anns,C,moved,ledger,x₀,q,normal,_,guards,chosen,
    ready,transfer,zero,moving,movedLive,anchor,dispositions,equations,replacement,cleanup,outK,outRs⟩ :=
      edge.actual
  let terms := xs.map Prod.fst
  let vals := xs.map Prod.snd
  let ms := actualMarked f C terms anns
  let ps := cohort f C terms anns
  let prior := outsideCohort f C terms vals anns
  let before := prior ++ moved
  let shift := (replaceRow f C terms vals anns).2
  have frames : terms = normalizedTerms raw :=
    (exactNormalizedTermSkeleton.1 f θ source.reads xs normal).trans (congrArg normalizedTerms rawEq)
  have staticReady : ActualFiniteSignedNodeBranch.StaticGuards B θ raw := by
    simpa only [ActualReadChargeIteration.NodeGuards,terms,frames,
      ActualFiniteSignedNodeBranch.StaticGuards] using guards
  have actualCoef := chosenCoefficient f B hf θ top raw a xs frames staticReady matched anns C chosen
  have staticZero : nodeCoefficient raw a = 0 := actualCoef.trans zero
  have tape := exactFullValueLabels f B hf θ terms vals anns chosen.1 guards.1
  have matchTerms : Matches f θ (pairs (labels terms)) a := by
    simpa only [nodeLabels,frames] using matched
  have vector := (exactMatchedNumericVector f θ (labels terms) (fullValues f anns) tape a).mp matchTerms
  have flags : classFlags (labels terms) a = (fullValues f anns).map (fun v => decide (v = C)) := by
    rw [vector]
    exact exactNumericMaximumFlags _ _ (sameLength tape).symm C chosen.2.1
  have decorateExact : decorate (normalizedTerms raw) (classFlags (nodeLabels raw) a) = some ms := by
    change decorate (normalizedTerms raw) (classFlags (labels (normalizedTerms raw)) a) = some ms
    rw [← frames,flags]
    exact exactActualDecoration f B hf θ terms vals anns chosen.1 guards.1 C
  obtain ⟨kept,δ⟩ := exactOutsideAndOriginShiftSyntax f B hf θ C terms vals anns chosen.1 guards.1
  obtain ⟨cohortExact,anchorExact⟩ := exactSelectedCohortSyntax f B hf θ C terms vals anns chosen.1 guards.1
  have moveExact := exactMovedAndCleanupSyntax.1 f θ (leastPrefix ps) ps moved moving
  have beforeExact : before.map Prod.fst =
      outsideSyntax ms ++ movedSyntax (leastSyntax (cohortSyntax ms)) (cohortSyntax ms) := by
    change (prior ++ moved).map Prod.fst = _
    rw [List.map_append,← kept,moveExact,anchorExact,cohortExact]
  have literal : successorFromMarks source.constant ms =
      some ⟨out.constant,out.reads.map Prod.fst⟩ :=
    assembleMarked source.constant shift out.constant ms before out.reads δ beforeExact outK outRs
  rw [successor,if_pos staticZero]
  simp only [decorateExact,Option.bind_some]
  exact literal

end LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
