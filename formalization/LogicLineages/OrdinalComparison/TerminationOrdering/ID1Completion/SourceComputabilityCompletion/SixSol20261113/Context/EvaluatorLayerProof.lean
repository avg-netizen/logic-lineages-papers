module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Runtime SixSol20261113.Erasure
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem actual : EvaluatorLayerTargets.ActualSourceUnfolding := by
 intro R H G M W body alpha Delta packed parameter out hsource
 apply SourceLayerQueries.sourceCases H G M W packed parameter _ hsource
 intro beta j Theta typ raw c gamma rawJob typed job B weight hi hp hparameter hr ht hj hweight haccept hadm hjob hjobGraph
 simp only [OriginalTypedDecoderTransportLogicalProof.iffRename,graph2Rename]
 exact SourceLayerRootProof.fromRoot R H M W (packed.relabel j) typ raw (parameter.relabel j) c gamma job typed rawJob B weight (out.relabel j)
   hp hparameter hj ht hr haccept hadm hjob hjobGraph hweight
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
