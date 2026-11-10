module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalApplicationSidecarTransitionPipelineDefinitions OriginalApplicationSidecarTransitionPipelineProof
open OriginalApplicationSidecarTransitionGraphProof

/-- Specialize the paid arbitrary-value iff in its input-to-output direction. -/
theorem neutralValue (data : Data) (window : Program 1)
    (candidate input typ parameter value : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter)))
    (hi : Nonempty (Derivation body Delta (graph1 OriginalFunctionNeutrality.mark value input))) :
    Nonempty (Derivation body Delta (graph1 OriginalFunctionNeutrality.mark value candidate)) := by
  obtain ⟨law⟩ := OriginalApplicationSidecarNeutralityProof.actualOriginalApplicationSidecarNeutrality
    body data window alpha Delta candidate input typ parameter value
  obtain ⟨premise⟩ := andIntro (andLeft hp) (andIntro (andRight hp) hc)
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law premise)) hi⟩

/-- Specialize the paid arbitrary-value iff in its input-to-output direction. -/
theorem shapeValue (data : Data) (window : Program 1)
    (candidate input typ parameter value : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter)))
    (hi : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark value input))) :
    Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark value candidate)) := by
  obtain ⟨law⟩ := OriginalApplicationSidecarRootMarkProof.actualOriginalApplicationSidecarRootMark
    body data window alpha Delta candidate input typ parameter value
  obtain ⟨premise⟩ := andIntro (andLeft hp) (andIntro (andRight hp) hc)
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law premise)) hi⟩

/-- Specialize the paid arbitrary-value iff in its input-to-output direction. -/
theorem variableValue (data : Data) (window : Program 1)
    (candidate input typ parameter value : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter)))
    (hi : Nonempty (Derivation body Delta (graph1 OriginalVariableRepresentative.variableMark value input))) :
    Nonempty (Derivation body Delta (graph1 OriginalVariableRepresentative.variableMark value candidate)) := by
  obtain ⟨law⟩ := OriginalApplicationSidecarVariableMarkProof.actualOriginalApplicationSidecarVariableMark
    body data window alpha Delta candidate input typ parameter value
  obtain ⟨premise⟩ := andIntro (andLeft hp) (andIntro (andRight hp) hc)
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law premise)) hi⟩

/-- Specialize the paid arbitrary-value iff in its input-to-output direction. -/
theorem spineValue (data : Data) (window : Program 1)
    (candidate input typ parameter value : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter)))
    (hi : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure value input))) :
    Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure value candidate)) := by
  obtain ⟨law⟩ := OriginalApplicationSidecarSpineProof.actualOriginalApplicationSidecarSpine
    body data window alpha Delta candidate input typ parameter value
  obtain ⟨premise⟩ := andIntro (andLeft hp) (andIntro (andRight hp) hc)
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law premise)) hi⟩

/-- Specialize the paid arbitrary-value iff in its input-to-output direction. -/
theorem bottomValue (data : Data) (window : Program 1)
    (candidate input typ parameter value : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter)))
    (hi : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomTest value input))) :
    Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomTest value candidate)) := by
  obtain ⟨law⟩ := OriginalApplicationSidecarBottomTestProof.actualOriginalApplicationSidecarBottomTest
    body data window alpha Delta candidate input typ parameter value
  obtain ⟨premise⟩ := andIntro (andLeft hp) (andIntro (andRight hp) hc)
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law premise)) hi⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionObserverProof
