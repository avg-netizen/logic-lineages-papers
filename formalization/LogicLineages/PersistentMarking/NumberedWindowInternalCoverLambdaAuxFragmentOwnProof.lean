module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (ownBelowRename)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedMeasureBase)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverRefinedOwnEarlierProof (exact_OpenCoverRefinedLambdaOwnEarlier)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof (exact_OpenCoverLambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverAuxFragmentInductionProof (exact_OpenCoverAuxFragmentWindowForward)
open NumberedWindowInternalCoverLambdaAuxFragmentOwnTargets

theorem exact_OpenCoverLambdaAuxFragmentOwnScratch : ExactOpenCoverLambdaAuxFragmentOwnScratch := by
  intro V TV M A B T s body α Γ dom q p vertices ctx result row guard
  let P := lexicalFittedPrograms s V TV M A B T
  let W := lambdaLexicalWindow s B T
  let C := fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)
  apply exact_OpenCoverLambdaLexicalWindow s B T body α Γ ctx dom q result _ row.typed
  intro β j Δ childTy keep paid
  let dom' := dom.relabel j
  let pushed := rawCons dom' (ctx.relabel j)
  have valid := renameInto guard j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid
  have typed := exact_OpenCoverAuxFragmentWindowForward s B T body β Δ pushed (q.relabel j)
    childTy valid paid.pastWindow
  have parent := moveParent P.V P.R s j keep row.parent
  have below := renameInto row.branchBelow j Δ keep
  simp only [lambdaRename] at parent
  simp only [ownBelowRename,lambdaRename] at below
  simp only [graphRename,lambdaRename]
  exact exact_OpenCoverRefinedLambdaOwnEarlier V TV C W s body β Δ (p.relabel j) (vertices.relabel j)
    pushed childTy dom' (q.relabel j) parent below typed paid.domain

#print axioms exact_OpenCoverLambdaAuxFragmentOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnProof
