module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalFinalGuardProof
open OriginalLambdaTraversalFinalIterationProof OriginalApplicationSidecarTransitionGraphProof
open OriginalLambdaTraversalFinalOutputFactsProof OriginalLambdaTraversalFinalInnerIdentityProof
open OriginalLambdaTraversalFinalInnerTransitionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Full original value+1 descent and source-gated fallback collapse to C.
C-idempotence here is a theorem consequence of the actual output packet. -/
theorem innerLeafValue (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf
        (OriginalApplicationSidecar.originalData (preparedData rawData window) window)) out input parameter)) := by
  have ho := outputFacts rawData window out input typ parameter hp hc
  have hpo := outputPremises rawData window out input typ parameter hp ho
  have ht := innerTransitionValue rawData window observers out input typ parameter hp hc
  have hf := innerTransitionValue rawData window observers out out typ parameter hpo
    (andRight (andRight (andRight ho)))
  have hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        InternalOriginalStepGuard.one input parameter)) := andLeft (andRight hp)
  rw [← innerValidity] at hv
  exact selectedAtFixedOutput _ _ out input parameter hv ht hf

/-- The selected inner leaf and C agree on arbitrary requested outputs;
totality binds the common actual output inside the object-language proof. -/
theorem innerLeafIff (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (InternalParameterizedCanonicalResultFold.leaf
          (OriginalApplicationSidecar.originalData (preparedData rawData window) window)) out input parameter).iff
        (graph2 (canonical rawData window) out input parameter))) := by
  apply programCases (canonical rawData window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hv
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact commonOutputIff _ _ value (out.relabel j) (input.relabel j) (parameter.relabel j)
    (innerLeafValue rawData window observers value (input.relabel j) (typ.relabel j)
      (parameter.relabel j) hp' hv) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerLeafProof
