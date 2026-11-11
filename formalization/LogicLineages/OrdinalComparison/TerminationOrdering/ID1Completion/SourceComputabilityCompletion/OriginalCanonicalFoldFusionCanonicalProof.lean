module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionCanonicalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open OriginalCanonicalFoldFusionLeafProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Fusion of the unchanged selected full canonical fold. Its original
application combiner leaf and both smaller-payload child calls remain in
the proof. The leaf supplier is a separate theorem obligation, not a
modification of any frozen final target or arithmetic source premise. -/
theorem canonicalIffFromLeaf (data rawData : Data) (window : Program 1)
    (leafLaw : LeafLaw (OriginalApplicationSidecar.selectedData data window) window
      (InternalParameterizedCanonicalResultFold.leaf (OriginalApplicationSidecar.selectedData data window))
      (OriginalLambdaTraversalSelection.canonical rawData window))
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph window input parameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises
          (OriginalApplicationSidecar.selectedData data window) input typ parameter))) :
    Nonempty (Derivation body Delta
      ((InternalParameterizedCanonicalResultFold.foldGraph
          (OriginalApplicationSidecar.selectedData data window) out input parameter).iff
        (graph2 (OriginalLambdaTraversalSelection.canonical rawData window) out input parameter))) :=
  OriginalCanonicalFoldFusionProof.iffAtInput
    (OriginalApplicationSidecar.selectedData data window) window
    (InternalParameterizedCanonicalResultFold.foldN (OriginalApplicationSidecar.selectedData data window))
    (OriginalLambdaTraversalSelection.canonical rawData window)
    (closedLaw _ window _ _
      (InternalParameterizedCanonicalResultFold.combine (OriginalApplicationSidecar.selectedData data window)) leafLaw)
    (OriginalCanonicalFoldFusionApplicationProof.canonicalApplicationLaw data rawData window)
    out input typ parameter hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionCanonicalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionCanonicalProof
