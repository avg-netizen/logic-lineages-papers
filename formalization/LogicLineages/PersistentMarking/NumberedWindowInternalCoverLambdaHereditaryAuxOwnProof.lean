module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTreeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaHereditaryAuxOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
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
open NumberedWindowInternalCoverHereditaryAuxTreeProof (treeRenameInto)
open NumberedWindowInternalCoverHereditaryAuxWindowProof (exact_OpenCoverHereditaryAuxWindowForward)
open NumberedWindowInternalCoverHereditaryAuxTargets

theorem exact_OpenCoverLambdaHereditaryAuxOwnScratch : ExactOpenCoverLambdaHereditaryAuxOwnScratch := by
  intro V TV M A B T s body α Γ dom q p vertices ctx result row tree
  let P := lexicalFittedPrograms s V TV M A B T
  let W := lambdaLexicalWindow s B T
  let C := fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)
  apply exact_OpenCoverLambdaLexicalWindow s B T body α Γ ctx dom q result _ row.typed
  intro β j Δ childTy keep paid
  let dom' := dom.relabel j
  let pushed := rawCons dom' (ctx.relabel j)
  have tree' := treeRenameInto j Δ keep tree
  have typed := exact_OpenCoverHereditaryAuxWindowForward s B T body β Δ pushed (q.relabel j)
    tree' childTy paid.pastWindow
  have parent := moveParent P.V P.R s j keep row.parent
  have below := renameInto row.branchBelow j Δ keep
  simp only [lambdaRename] at parent
  simp only [ownBelowRename,lambdaRename] at below
  simp only [graphRename,lambdaRename]
  exact exact_OpenCoverRefinedLambdaOwnEarlier V TV C W s body β Δ (p.relabel j) (vertices.relabel j)
    pushed childTy dom' (q.relabel j) parent below typed paid.domain

#print axioms exact_OpenCoverLambdaHereditaryAuxOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaHereditaryAuxOwnProof
