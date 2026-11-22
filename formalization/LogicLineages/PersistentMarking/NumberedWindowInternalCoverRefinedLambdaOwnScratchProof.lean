module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalLambdaOwnContinuationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedOwnScratchTargets (ChildOwnInputs)
open NumberedWindowInternalCoverChildOwnScopeProof (moveLocal)
open NumberedWindowInternalCoverRefinedLambdaSyntaxProof (exact_OpenCoverRefinedLambdaSyntaxParent)
open NumberedWindowInternalCoverSharedLambdaMeasureProof (exact_OpenCoverSharedLambdaMeasureParent)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverLocalLambdaOwnContinuationProof (exact_OpenCoverLocalLambdaOwnContinuation)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent moveTypeMember)
open NumberedWindowInternalCoverLocalOwnContinuationTargets

theorem exact_OpenCoverRefinedLambdaOwnScratch : ExactOpenCoverRefinedLambdaOwnScratch := by
  intro V TV M W s body α Γ p vertices ctx bodyTy ty q parent typed ih member
  let Q := refinedSyntax V TV
  let R := sharedMeasureUpdate M
  obtain ⟨bits⟩ := exact_OpenCoverRefinedLambdaSyntaxParent V TV body α Γ ty q parent.valid
  have localChild : ChildOwnInputs Q R W s body Γ ctx bodyTy q :=
    ⟨⟨Derivation.conjunctionRight bits⟩,typed,ih⟩
  apply exact_OpenCoverSharedLambdaMeasureParent M body α Γ ty q p _ parent.measured
  intro β j Δ old mc d b keep row
  rw [graphRename,lambdaRename]
  have parent' := moveParent Q R s j keep parent
  rw [lambdaRename] at parent'
  have local' := moveLocal Q R W s j keep localChild
  have member' := moveTypeMember s j keep member
  exact exact_OpenCoverLocalLambdaOwnContinuation Q R W s body β Δ
    (p.relabel j) (vertices.relabel j) (ctx.relabel j) (bodyTy.relabel j) (ty.relabel j) (q.relabel j) mc d b
    parent' local' row.child row.parentPair member'

#print axioms exact_OpenCoverRefinedLambdaOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaOwnScratchProof
