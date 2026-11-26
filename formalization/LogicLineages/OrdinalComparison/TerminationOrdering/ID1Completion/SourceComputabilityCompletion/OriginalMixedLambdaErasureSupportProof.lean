module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryWithConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureSupportProof
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
open OriginalMixedLambdaErasureDefinitions
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem contextChildIHRename {beta : Type} (leaf : Program 4) (source : Program 2)
 (oldS oldT rootCert rootParam codomain erasedType cutoff context : OTerm alpha)
 (j : alpha → beta) (Theta : List (Formula beta))
 (hj : ∀ f ∈ Delta, f.relabel j ∈ Theta)
 (h : ContextChildIH body Delta leaf source oldS oldT rootCert rootParam codomain erasedType cutoff context) :
 ContextChildIH body Theta leaf source (oldS.relabel j) (oldT.relabel j) (rootCert.relabel j) (rootParam.relabel j) (codomain.relabel j)
   (erasedType.relabel j) (cutoff.relabel j) (context.relabel j) := by
 intro gamma k Xi hk
 have hc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (f.relabel j) (hj f hf)
 simpa only [Term.relabel_relabel] using h gamma (k ∘ j) Xi hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureSupportProof
