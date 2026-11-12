module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryWithConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalSourceInversionSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (refl)
open OriginalLambdaErasureExactCaseDefinitions
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem exactChildIHRename {beta : Type} (leaf : Program 4) (source : Program 2)
 (oldS oldT rootCert rootParam codomain erasedType cutoff context before after : OTerm alpha) (j : alpha → beta)
 (h : ExactChildIH body leaf source oldS oldT rootCert rootParam codomain erasedType cutoff context before after) :
 ExactChildIH body leaf source (oldS.relabel j) (oldT.relabel j) (rootCert.relabel j) (rootParam.relabel j) (codomain.relabel j)
   (erasedType.relabel j) (cutoff.relabel j) (context.relabel j) (before.relabel j) (after.relabel j) := by
 intro gamma k
 simpa only [Term.relabel_relabel] using h gamma (k ∘ j)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseSupportProof
