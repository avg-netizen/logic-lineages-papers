module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSidecarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedTransitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalFinalGuardProof
open OriginalLambdaTraversalFinalInnerIdentityProof OriginalLambdaTraversalFinalOutputFactsProof
open OriginalApplicationSidecarTransitionGraphProof
open OriginalLambdaTraversalSelectionFieldProof OriginalLambdaTraversalFinalSourceProof
open OriginalLambdaTraversalFinalPipelineIdentityProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal same-validity transport into the accepted sidecar transition
consumer. The inner and eventual representatives remain distinct. -/
theorem selectedSourceHyp (rawData : Data) (window : Program 1)
    (input typ parameter : OTerm alpha) :
    OriginalApplicationSidecarTransitionPipelineDefinitions.sourceHyp
      (preparedData rawData window) window input typ parameter =
    premises rawData window input typ parameter := by
  unfold OriginalApplicationSidecarTransitionPipelineDefinitions.sourceHyp premises
  rw [innerSourcePremises]

/-- The original final transition guard is paid by the accepted sidecar
transition theorem after genuine internal fold fusion. -/
theorem selectedTransitionValue (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph
        (OriginalApplicationSidecar.selectedData (preparedData rawData window) window).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity
          (OriginalApplicationSidecar.selectedData (preparedData rawData window) window))
        out input parameter)) := by
  have hs := hp
  rw [← selectedSourceHyp] at hs
  exact OriginalApplicationSidecarTransitionValueProof.transitionAtSidecarOutput
    (preparedData rawData window) window out input typ parameter hs
    (OriginalCanonicalFoldFusionSidecarProof.sidecarValue rawData window observers
      out input typ parameter hp hc)

/-- Both directions at arbitrary actual outputs follow from graph
functionality, not a selected representative substituted for the transition. -/
theorem selectedTransitionIff (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((InternalParameterizedBoundedDescentNormalizer.transitionGraph
        (OriginalApplicationSidecar.selectedData (preparedData rawData window) window).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity
          (OriginalApplicationSidecar.selectedData (preparedData rawData window) window))
        out input parameter).iff
        (graph2 (canonical rawData window) out input parameter))) := by
  apply programCases (canonical rawData window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  change Nonempty (Derivation body Theta
    (((graph2 (InternalParameterizedBoundedDescentNormalizer.transition _ _)
      out input parameter).iff (graph2 (canonical rawData window) out input parameter)).relabel j))
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hv
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact commonOutputIff _ _ value (out.relabel j) (input.relabel j) (parameter.relabel j)
    (selectedTransitionValue rawData window observers value (input.relabel j) (typ.relabel j)
      (parameter.relabel j) hp' hv) hv

/-- This conditional packaging visibly retains only the exact frozen
ObserverLaws supplier. The final exact theorem will instantiate that supplier. -/
theorem finalTransition (p : GlobalSourcePackage.Inputs)
    (observers : ObserverLaws p.base p.window) : FinalTransitionLaw p := by
  intro body alpha Delta out input typ parameter
  let P := OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
    InternalParameterizedCanonicalResultFold.sourcePremises (finalData p) input typ parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp' : Nonempty (Derivation body (P :: Delta) (premises p.base p.window input typ parameter)) := by
    change Nonempty (Derivation body (P :: Delta)
      (OriginalFunctionNeutrality.windowGraph p.window input parameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises (leafData p.base p.window) input typ parameter))
    simpa only [P, finalWindow, finalSourcePremises] using hp
  obtain ⟨h⟩ := selectedTransitionIff p.base p.window observers out input typ parameter hp'
  rw [← finalSelectedData] at h
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedTransitionProof
