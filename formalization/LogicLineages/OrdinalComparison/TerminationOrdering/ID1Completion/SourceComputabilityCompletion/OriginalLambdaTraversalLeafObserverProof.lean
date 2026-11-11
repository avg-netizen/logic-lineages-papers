module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralitySelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeFieldSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Each theorem consumes the actual acyclic selected leaf, after its original
sidecar refinement. No C graph, equality, or observer law is assumed. -/
theorem rootMark (rawData : Data) (window : Program 1)
    (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalConstructorShape.mark mark out).iff (graph1 OriginalConstructorShape.mark mark input))) :=
  OriginalApplicationSidecarRootMarkLeafProof.leafMarkIff
    (OriginalApplicationSidecar.baseData (transparentData rawData) window) window out input parameter mark hw hv hl

theorem variableMark (rawData : Data) (window : Program 1)
    (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalVariableRepresentative.variableMark mark out).iff
        (graph1 OriginalVariableRepresentative.variableMark mark input))) :=
  OriginalApplicationSidecarVariableMarkLeafProof.leafMarkIff
    (OriginalApplicationSidecar.baseData (transparentData rawData) window) window out input parameter mark hw hv hl

theorem spineMark (rawData : Data) (window : Program 1)
    (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 BottomSpineMeasure.measure mark out).iff (graph1 BottomSpineMeasure.measure mark input))) :=
  OriginalApplicationSidecarSpineLeafProof.leafSpineIff
    (OriginalApplicationSidecar.baseData (transparentData rawData) window) window out input parameter mark hw hv hl

theorem bottomMark (rawData : Data) (window : Program 1)
    (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 BottomRepresentative.bottomTest mark out).iff (graph1 BottomRepresentative.bottomTest mark input))) :=
  OriginalApplicationSidecarBottomTestLeafProof.leafBottomIff
    (OriginalApplicationSidecar.baseData (transparentData rawData) window) window out input parameter mark hw hv hl

theorem neutralityMark (rawData : Data) (window : Program 1)
    (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalFunctionNeutrality.mark mark out).iff (graph1 OriginalFunctionNeutrality.mark mark input))) := by
  obtain ⟨law⟩ := OriginalFunctionNeutralitySelectedProof.selectedMarkPreservation
    (OriginalApplicationSidecar.baseData (transparentData rawData) window)
      window body alpha Delta out input parameter mark
  obtain ⟨hp⟩ := andIntro hw (andIntro hv hl)
  exact ⟨Derivation.implicationElimination law hp⟩

/-- Internally bind the common original mark and recover its actual tag.
This preserves every symbolic raw tag, rather than only a typed case split. -/
theorem rawTag (rawData : Data) (window : Program 1)
    (out input parameter tag : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag tag input))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag tag out)) := by
  apply programCases OriginalConstructorShape.mark (Fin.cons input Fin.elim0) _
  intro beta j Theta mark hj hm
  rw [graph1Rename]
  have hw' := renameInto hw j Theta hj
  have hv' := renameInto hv j Theta hj
  have hl' := renameInto hl j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [graph2Rename] at hl'
  rw [graph1Rename] at ht'
  simp only [consTermRename,emptyRename] at hm
  obtain ⟨hi⟩ := rootMark rawData window (out.relabel j) (input.relabel j)
    (parameter.relabel j) mark hw' hv' hl'
  obtain ⟨hm⟩ := hm
  have ho : Nonempty (Derivation body Theta
      (graph1 OriginalConstructorShape.mark mark (out.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hm⟩
  exact OriginalConstructorShapeRootFieldsProof.sharedTag mark (input.relabel j) (out.relabel j)
    (tag.relabel j) ⟨hm⟩ ho ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafObserverProof
