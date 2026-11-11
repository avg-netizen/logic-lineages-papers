module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalFinalGuardProof
open OriginalLambdaTraversalFinalInnerIdentityProof OriginalLambdaTraversalFinalOutputFactsProof
open OriginalLambdaTraversalFinalSelectedTransitionProof OriginalLambdaTraversalFinalIterationProof
open OriginalApplicationSidecarTransitionGraphProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both the original final bounded normalizer and its exact-one source
fallback are paid; C-idempotence comes from the accepted actual output law. -/
theorem selectedLeafValue (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf
        (OriginalApplicationSidecar.selectedData (preparedData rawData window) window)) out input parameter)) := by
  have ho := outputFacts rawData window out input typ parameter hp hc
  have hpo := outputPremises rawData window out input typ parameter hp ho
  have ht := selectedTransitionValue rawData window observers out input typ parameter hp hc
  have hf := selectedTransitionValue rawData window observers out out typ parameter hpo
    (andRight (andRight (andRight ho)))
  have hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        InternalOriginalStepGuard.one input parameter)) := andLeft (andRight hp)
  rw [← selectedValidity] at hv
  exact selectedAtFixedOutput _ _ out input parameter hv ht hf

/-- The eventual selected leaf's whole actual graph equals C under the
unchanged source/window/type premises; no leaf fixedness is supplied. -/
theorem selectedLeafIff (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (InternalParameterizedCanonicalResultFold.leaf
        (OriginalApplicationSidecar.selectedData (preparedData rawData window) window)) out input parameter).iff
        (graph2 (canonical rawData window) out input parameter))) := by
  apply programCases (canonical rawData window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hv
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact commonOutputIff _ _ value (out.relabel j) (input.relabel j) (parameter.relabel j)
    (selectedLeafValue rawData window observers value (input.relabel j) (typ.relabel j)
      (parameter.relabel j) hp' hv) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedLeafProof
