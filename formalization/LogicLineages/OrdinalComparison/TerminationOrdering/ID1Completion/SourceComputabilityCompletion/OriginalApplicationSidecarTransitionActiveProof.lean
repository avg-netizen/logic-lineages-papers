module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionObserverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionActiveProof
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

/-- All five observer guards retain the SAME actual sidecar output. -/
theorem atMarks (data : Data) (window : Program 1)
    (candidate input typ parameter nmark smark vmark pmark bmark : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter)))
    (hnmark : Nonempty (Derivation body Delta (graph1 OriginalFunctionNeutrality.mark nmark input)))
    (hsmark : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark smark input)))
    (hvmark : Nonempty (Derivation body Delta (graph1 OriginalVariableRepresentative.variableMark vmark input)))
    (hpmark : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure pmark input)))
    (hbmark : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomTest bmark input)))
    : Nonempty (Derivation body Delta (graph2 (selectedData data window).oldRepresentative candidate input parameter)) := by
  have ha := activeOfSource data window input typ parameter hp
  have hr := refinedValue data window candidate input parameter ha hc
  have hneutral : Nonempty (Derivation body Delta (graph2 (neutral data window) candidate input parameter)) :=
    observedValue (OriginalFunctionNeutrality.active data window) OriginalFunctionNeutrality.mark (representative data window)
      candidate input parameter nmark ha hr
      (OriginalApplicationSidecarTransitionObserverProof.neutralValue data window candidate input typ parameter nmark hp hc hnmark) hnmark
  have hshape : Nonempty (Derivation body Delta (graph2 (shape data window) candidate input parameter)) :=
    observedValue (OriginalFunctionNeutrality.active data window) OriginalConstructorShape.mark (neutral data window)
      candidate input parameter smark ha hneutral
      (OriginalApplicationSidecarTransitionObserverProof.shapeValue data window candidate input typ parameter smark hp hc hsmark) hsmark
  have hvariable : Nonempty (Derivation body Delta (graph2 (variableStage data window) candidate input parameter)) :=
    observedValue (OriginalFunctionNeutrality.active data window) OriginalVariableRepresentative.variableMark (shape data window)
      candidate input parameter vmark ha hshape
      (OriginalApplicationSidecarTransitionObserverProof.variableValue data window candidate input typ parameter vmark hp hc hvmark) hvmark
  have hspine : Nonempty (Derivation body Delta (graph2 (spine data window) candidate input parameter)) :=
    observedValue (OriginalFunctionNeutrality.active data window) BottomSpineMeasure.measure (variableStage data window)
      candidate input parameter pmark ha hvariable
      (OriginalApplicationSidecarTransitionObserverProof.spineValue data window candidate input typ parameter pmark hp hc hpmark) hpmark
  have hbottom : Nonempty (Derivation body Delta (graph2 (bottom data window) candidate input parameter)) :=
    observedValue (OriginalFunctionNeutrality.active data window) BottomRepresentative.bottomTest (spine data window)
      candidate input parameter bmark ha hspine
      (OriginalApplicationSidecarTransitionObserverProof.bottomValue data window candidate input typ parameter bmark hp hc hbmark) hbmark
  rw [selectedOldRepresentative]
  exact hbottom

/-- Bind actual input-observer values using original Program totality. -/
theorem activeValue (data : Data) (window : Program 1)
    (candidate input typ parameter : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (selectedData data window).oldRepresentative candidate input parameter)) := by
  let marks : Fin 5 → Program 1 := ![OriginalFunctionNeutrality.mark, OriginalConstructorShape.mark,
    OriginalVariableRepresentative.variableMark, BottomSpineMeasure.measure, BottomRepresentative.bottomTest]
  let qs : Fin 5 → Program 2 := fun i => .composition (marks i) (fun _ : Fin 1 => .projection 0)
  apply InternalApplicationStepPeelSupportProof.queryCases qs
    (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j ys Theta hj hys
  rw [graph2Rename]
  simp only [consTermRename, emptyRename] at hys
  have hp' := renameInto hp j Theta hj
  rw [sourceHypRename] at hp'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  let xs : Fin 2 → OrdinaryArithmetic.Term beta :=
    Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have h0 : Nonempty (Derivation body Theta (graph1 OriginalFunctionNeutrality.mark (ys 0) (input.relabel j))) :=
    InternalApplicationCertificateConstructorsSupportProof.unaryRecover OriginalFunctionNeutrality.mark (.projection 0)
      (ys 0) (input.relabel j) xs (hys 0) (projectionValue 0 xs)
  have h1 : Nonempty (Derivation body Theta (graph1 OriginalConstructorShape.mark (ys 1) (input.relabel j))) :=
    InternalApplicationCertificateConstructorsSupportProof.unaryRecover OriginalConstructorShape.mark (.projection 0)
      (ys 1) (input.relabel j) xs (hys 1) (projectionValue 0 xs)
  have h2 : Nonempty (Derivation body Theta (graph1 OriginalVariableRepresentative.variableMark (ys 2) (input.relabel j))) :=
    InternalApplicationCertificateConstructorsSupportProof.unaryRecover OriginalVariableRepresentative.variableMark (.projection 0)
      (ys 2) (input.relabel j) xs (hys 2) (projectionValue 0 xs)
  have h3 : Nonempty (Derivation body Theta (graph1 BottomSpineMeasure.measure (ys 3) (input.relabel j))) :=
    InternalApplicationCertificateConstructorsSupportProof.unaryRecover BottomSpineMeasure.measure (.projection 0)
      (ys 3) (input.relabel j) xs (hys 3) (projectionValue 0 xs)
  have h4 : Nonempty (Derivation body Theta (graph1 BottomRepresentative.bottomTest (ys 4) (input.relabel j))) :=
    InternalApplicationCertificateConstructorsSupportProof.unaryRecover BottomRepresentative.bottomTest (.projection 0)
      (ys 4) (input.relabel j) xs (hys 4) (projectionValue 0 xs)
  exact atMarks data window (candidate.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hp' hc' h0 h1 h2 h3 h4

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionActiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionActiveProof
