module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open GuardedSourceSyntaxProof (numeralRename)
open OriginalVariableObjectSyntaxProof (bottomGraphRename)
open OriginalVariableErasureCertificateSyntaxProof (originalRankDropRename)
open OriginalErasureCertificateContinuation

theorem shapeRename {alpha beta : Type} (tau : Ty)
    (source gamma extended packed raw domain index : OTerm alpha) (j : alpha → beta) :
    (Shape tau source gamma extended packed raw domain index).relabel j =
      Shape tau (source.relabel j) (gamma.relabel j) (extended.relabel j)
        (packed.relabel j) (raw.relabel j) (domain.relabel j) (index.relabel j) := by
  simp only [Shape,conjunctionRename,graph1Rename,graph2Rename,numeralRename]

theorem endpointRename {alpha beta : Type} (tau : Ty)
    (source target extended : OTerm alpha) (j : alpha → beta) :
    (EndpointResult tau source target extended).relabel j =
      EndpointResult tau (source.relabel j) (target.relabel j) (extended.relabel j) := by
  simp only [EndpointResult,conjunctionRename,bottomGraphRename,numeralRename,originalRankDropRename]

theorem survivorRename {alpha beta : Type} (tau : Ty)
    (source target gamma extended index erasedSource erasedTarget : OTerm alpha) (j : alpha → beta) :
    (SurvivorResult tau source target gamma extended index erasedSource erasedTarget).relabel j =
      SurvivorResult tau (source.relabel j) (target.relabel j) (gamma.relabel j)
        (extended.relabel j) (index.relabel j) (erasedSource.relabel j) (erasedTarget.relabel j) := by
  simp only [SurvivorResult,conjunctionRename,endpointRename,graph3Rename,
    bottomGraphRename,numeralRename,originalRankDropRename]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSyntaxProof
