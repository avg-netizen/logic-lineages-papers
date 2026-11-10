module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionInactiveProof
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

/-- Inactivity keeps the WHOLE preceding representative at every output. -/
theorem inactiveValue (data : Data) (window : Program 1)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (hz : Nonempty (Derivation body Delta (graph2 (OriginalFunctionNeutrality.active data window) z input parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 (representative data window) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 ((selectedData data window).oldRepresentative) out input parameter)) := by
  have hneutral : Nonempty (Derivation body Delta (graph2 (neutral data window) out input parameter)) :=
    observedZeroValue (OriginalFunctionNeutrality.active data window) OriginalFunctionNeutrality.mark (representative data window) out input parameter hz hr
  have hshape : Nonempty (Derivation body Delta (graph2 (shape data window) out input parameter)) :=
    observedZeroValue (OriginalFunctionNeutrality.active data window) OriginalConstructorShape.mark (neutral data window) out input parameter hz hneutral
  have hvariable : Nonempty (Derivation body Delta (graph2 (variableStage data window) out input parameter)) :=
    observedZeroValue (OriginalFunctionNeutrality.active data window) OriginalVariableRepresentative.variableMark (shape data window) out input parameter hz hshape
  have hspine : Nonempty (Derivation body Delta (graph2 (spine data window) out input parameter)) :=
    observedZeroValue (OriginalFunctionNeutrality.active data window) BottomSpineMeasure.measure (variableStage data window) out input parameter hz hvariable
  have hbottom : Nonempty (Derivation body Delta (graph2 (bottom data window) out input parameter)) :=
    observedZeroValue (OriginalFunctionNeutrality.active data window) BottomRepresentative.bottomTest (spine data window) out input parameter hz hspine
  rw [selectedOldRepresentative]
  exact hbottom

/-- Inactivity keeps the WHOLE preceding representative at every output. -/
theorem inactiveRecover (data : Data) (window : Program 1)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (hz : Nonempty (Derivation body Delta (graph2 (OriginalFunctionNeutrality.active data window) z input parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 ((selectedData data window).oldRepresentative) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (representative data window) out input parameter)) := by
  rw [selectedOldRepresentative] at hr
  have hbottom : Nonempty (Derivation body Delta (graph2 (spine data window) out input parameter)) :=
    observedZeroRecover (OriginalFunctionNeutrality.active data window) BottomRepresentative.bottomTest (spine data window) out input parameter hz hr
  have hspine : Nonempty (Derivation body Delta (graph2 (variableStage data window) out input parameter)) :=
    observedZeroRecover (OriginalFunctionNeutrality.active data window) BottomSpineMeasure.measure (variableStage data window) out input parameter hz hbottom
  have hvariable : Nonempty (Derivation body Delta (graph2 (shape data window) out input parameter)) :=
    observedZeroRecover (OriginalFunctionNeutrality.active data window) OriginalVariableRepresentative.variableMark (shape data window) out input parameter hz hspine
  have hshape : Nonempty (Derivation body Delta (graph2 (neutral data window) out input parameter)) :=
    observedZeroRecover (OriginalFunctionNeutrality.active data window) OriginalConstructorShape.mark (neutral data window) out input parameter hz hvariable
  have hneutral : Nonempty (Derivation body Delta (graph2 (representative data window) out input parameter)) :=
    observedZeroRecover (OriginalFunctionNeutrality.active data window) OriginalFunctionNeutrality.mark (representative data window) out input parameter hz hshape
  exact hneutral

theorem inactiveIff (data : Data) (window : Program 1)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (hz : Nonempty (Derivation body Delta (graph2 (OriginalFunctionNeutrality.active data window) z input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (selectedData data window).oldRepresentative out input parameter).iff
        (graph2 (representative data window) out input parameter))) := by
  obtain ⟨forward⟩ := inactiveRecover (body := body)
    (Delta := graph2 (selectedData data window).oldRepresentative out input parameter :: Delta)
    data window out input parameter (withHyp hz _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := inactiveValue (body := body)
    (Delta := graph2 (representative data window) out input parameter :: Delta)
    data window out input parameter (withHyp hz _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionInactiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionInactiveProof
