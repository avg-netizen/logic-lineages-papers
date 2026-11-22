module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundZeroOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (ownBelowRename)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedMeasureBase)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverRefinedOwnEarlierProof (exact_OpenCoverRefinedLambdaOwnEarlier)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof (exact_OpenCoverLambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaBoundCoherenceProof (exact_OpenCoverLambdaBoundCoherence)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets

theorem exact_OpenCoverLambdaBoundZeroOwnScratch : ExactOpenCoverLambdaBoundZeroOwnScratch := by
  intro V TV M A B T s body α Γ dom annotation p vertices ctx result row
  let P := lexicalFittedPrograms s V TV M A B T
  let W := lambdaLexicalWindow s B T
  let C := fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)
  let q := namedTerm 1 annotation z
  apply exact_OpenCoverLambdaLexicalWindow s B T body α Γ ctx dom q result _ row.typed
  intro β j Δ childTy keep paid
  let dom' := dom.relabel j
  let ann' := annotation.relabel j
  let ctx' := ctx.relabel j
  let q' := namedTerm 1 ann' z
  have old := paid.pastWindow
  simp only [q,namedRename,zRelabel] at old
  have typed := exact_OpenCoverLambdaBoundCoherence s B T body β Δ
    (rawCons dom' ctx') ann' z childTy old
  have parent := moveParent P.V P.R s j keep row.parent
  simp only [boundZeroLambda,lambdaRename,namedRename,zRelabel] at parent
  have below := renameInto row.branchBelow j Δ keep
  simp only [ownBelowRename,boundZeroLambda,lambdaRename,namedRename,zRelabel] at below
  simp only [graphRename,boundZeroLambda,lambdaRename,namedRename,zRelabel]
  exact exact_OpenCoverRefinedLambdaOwnEarlier V TV C W s body β Δ (p.relabel j) (vertices.relabel j)
    (rawCons dom' ctx') childTy dom' q' parent below typed paid.domain

#print axioms exact_OpenCoverLambdaBoundZeroOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundZeroOwnScratchProof
