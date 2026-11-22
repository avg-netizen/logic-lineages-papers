module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalLambdaOwnContinuationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof (exact_OpenSelectedGrammarLambdaMeasuredScratch)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (specializeIH)
open NumberedWindowInternalCoverChildOwnScopeProof (moveLocal)
open NumberedWindowInternalCoverSharedMeasureChildCasesProof (moveMeasuredChild)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent moveTypeMember)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverLocalOwnContinuationTargets

theorem exact_OpenCoverLocalLambdaOwnContinuation : ExactOpenCoverLocalLambdaOwnContinuation := by
  intro V R W s body α Γ p vertices ctx bodyTy ty q mc d b parent child observed pair member
  apply observationCases d (headsTerm s α) (typesTerm s α) b _
  intro β j Δ state terms args keep scope
  rw [graphRename,lambdaRename]
  simp only [headsTerm,typesTerm,numeralRename] at scope
  have parent' := moveParent V R s j keep parent
  rw [lambdaRename] at parent'
  have child' := moveLocal V R W s j keep child
  have observed' := moveMeasuredChild R j Δ keep observed
  have pair' := renameInto pair j Δ keep
  rw [pairRename,sucRelabel] at pair'
  have member' := moveTypeMember s j keep member
  have ih := specializeIH W (selectedCover V (selectedMeasure R)) s
    (ctx.relabel j) (bodyTy.relabel j) (q.relabel j) terms child'.ih
  exact exact_OpenSelectedGrammarLambdaMeasuredScratch V (selectedMeasure R) W s
    body β Δ (p.relabel j) (mc.relabel j) (d.relabel j) (b.relabel j) state terms args
    (vertices.relabel j) (ctx.relabel j) (bodyTy.relabel j) (ty.relabel j) (q.relabel j)
    child'.typed ih scope child'.valid observed'.selected observed'.coordinates
    member' parent'.valid parent'.measured pair' parent'.held

#print axioms exact_OpenCoverLocalLambdaOwnContinuation

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalLambdaOwnContinuationProof
