module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
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
open NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
  (exact_OpenCoverLambdaWindowForwardNonRecursive)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets

theorem exact_OpenCoverLambdaNonRecursiveOwnScratch : ExactOpenCoverLambdaNonRecursiveOwnScratch := by
  intro V TV M A B T s body α Γ dom prior p vertices ctx result row lam aux
  let P := lexicalFittedPrograms s V TV M A B T
  let W := lambdaLexicalWindow s B T
  let C := fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)
  apply exact_OpenCoverLambdaLexicalWindow s B T body α Γ ctx dom (suc prior) result _ row.typed
  intro β j Δ childTy keep paid
  let dom' := dom.relabel j
  let ctx' := ctx.relabel j
  let k := prior.relabel j
  have old := paid.pastWindow
  rw [sucRelabel] at old
  have noLam := renameInto lam j Δ keep
  have noAux := renameInto aux j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at noLam noAux
  have typed := exact_OpenCoverLambdaWindowForwardNonRecursive s B T body β Δ
    (rawCons dom' ctx') k childTy noLam noAux old
  have parent := moveParent P.V P.R s j keep row.parent
  have below := renameInto row.branchBelow j Δ keep
  simp only [lambdaRename,sucRelabel] at parent
  simp only [ownBelowRename,lambdaRename,sucRelabel] at below
  simp only [graphRename,lambdaRename,sucRelabel]
  exact exact_OpenCoverRefinedLambdaOwnEarlier V TV C W s body β Δ (p.relabel j) (vertices.relabel j)
    (rawCons dom' ctx') childTy dom' (suc k) parent below typed paid.domain

#print axioms exact_OpenCoverLambdaNonRecursiveOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnProof
