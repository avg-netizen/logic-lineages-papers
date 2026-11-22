module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardAuxResultProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (ownBelowRename)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedMeasureBase)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverRefinedOwnEarlierProof (exact_OpenCoverRefinedLambdaOwnEarlier)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof (exact_OpenCoverLambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaWindowForwardAuxResultProof (exact_OpenCoverLambdaWindowForwardAuxResult)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverLambdaAuxBodyOwnTargets

theorem exact_OpenCoverLambdaAuxBodyOwnScratch : ExactOpenCoverLambdaAuxBodyOwnScratch := by
  intro V TV M A B T s body α Γ dom adom acod fp ap p vertices ctx result row fnLam fnAux argLam argAux
  let P := lexicalFittedPrograms s V TV M A B T
  let W := lambdaLexicalWindow s B T
  let C := fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)
  let key := auxiliaryTerm adom acod (suc fp) (suc ap)
  apply exact_OpenCoverLambdaLexicalWindow s B T body α Γ ctx dom key result _ row.typed
  intro β j Δ childTy keep paid
  let dom' := dom.relabel j
  let ctx' := ctx.relabel j
  let funcPrior := fp.relabel j
  let argPrior := ap.relabel j
  let bodyKey := auxiliaryTerm (adom.relabel j) (acod.relabel j) (suc funcPrior) (suc argPrior)
  have old := paid.pastWindow
  simp only [key,auxiliaryRename,sucRelabel] at old
  have fl := renameInto fnLam j Δ keep
  have fa := renameInto fnAux j Δ keep
  have al := renameInto argLam j Δ keep
  have aa := renameInto argAux j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at fl fa al aa
  have typed := exact_OpenCoverLambdaWindowForwardAuxResult s B T body β Δ (rawCons dom' ctx')
    (adom.relabel j) (acod.relabel j) funcPrior argPrior childTy fl fa al aa old
  have parent := moveParent P.V P.R s j keep row.parent
  have below := renameInto row.branchBelow j Δ keep
  simp only [lambdaRename,auxiliaryRename,sucRelabel] at parent
  simp only [ownBelowRename,lambdaRename,auxiliaryRename,sucRelabel] at below
  simp only [graphRename,lambdaRename,auxiliaryRename,sucRelabel]
  exact exact_OpenCoverRefinedLambdaOwnEarlier V TV C W s body β Δ (p.relabel j) (vertices.relabel j)
    (rawCons dom' ctx') childTy dom' bodyKey parent below typed paid.domain

#print axioms exact_OpenCoverLambdaAuxBodyOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnProof
