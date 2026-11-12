module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalControlGraphSupportProof
open InternalSourceInversionSupportProof (onEquality)
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalVariableObjectSyntaxProof (bottomGraphRename)
open OriginalVariableErasureCertificate

theorem internalEqualRename {alpha beta : Type} (source target : OTerm alpha)
    (j : alpha → beta) :
    (InternalControlGraph.equal source target).relabel j =
      InternalControlGraph.equal (source.relabel j) (target.relabel j) := by
  simpa only [InternalControlGraph.equal,onEquality,InternalTagArithmeticSyntaxProof.eqn]
    using (eqnRelabel source target j)

theorem topVariableShapeRename {alpha beta : Type} (tau : Ty)
    (source gamma extended packed raw : OTerm alpha) (j : alpha → beta) :
    (TopVariableShape tau source gamma extended packed raw).relabel j =
      TopVariableShape tau (source.relabel j) (gamma.relabel j)
        (extended.relabel j) (packed.relabel j) (raw.relabel j) := by
  simp only [TopVariableShape,conjunctionRename,graph1Rename,graph2Rename,numeralRename]

theorem originalRankDropRename {alpha beta : Type}
    (source target : OTerm alpha) (j : alpha → beta) :
    (OriginalRankDrop source target).relabel j =
      OriginalRankDrop (source.relabel j) (target.relabel j) := by
  simp only [OriginalRankDrop,conjunctionRename,graph1Rename,numeralRename,
    InternalLessThan.strictLess,orderRename]

theorem rawResultRename {alpha beta : Type} (tau : Ty)
    (source target gamma extended erasedSource erasedTarget : OTerm alpha) (j : alpha → beta) :
    (RawResult tau source target gamma extended erasedSource erasedTarget).relabel j =
      RawResult tau (source.relabel j) (target.relabel j) (gamma.relabel j)
        (extended.relabel j) (erasedSource.relabel j) (erasedTarget.relabel j) := by
  simp only [RawResult,conjunctionRename,bottomGraphRename,numeralRename,
    internalEqualRename,originalRankDropRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSyntaxProof
