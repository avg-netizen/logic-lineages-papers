module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection
open OriginalApplicationSidecarTransitionGraphProof
open OriginalApplicationSidecarTransitionPipelineDefinitions (observed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual once-normalized active test has the acyclic leaf validator. -/
theorem activeLeaf (rawData : Data) (window : Program 1) :
    OriginalFunctionNeutrality.active (transparentData rawData) window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) := by
  change OriginalFunctionNeutrality.active (transparentData rawData) window =
    InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
      (InternalOriginalUniformDescentSelection.validity
        (OriginalApplicationSidecar.selectedData (transparentData rawData) window))
  rw [OriginalApplicationSidecarIdentityProgramsProof.activeOriginal,
    OriginalApplicationSidecarIdentityProgramsProof.sameValidity]

def premises {alpha : Type} (rawData : Data) (window : Program 1)
    (input typ parameter : OTerm alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) input typ parameter

theorem premisesRename {beta : Type} (rawData : Data) (window : Program 1)
    (input typ parameter : OTerm alpha) (j : alpha → beta) :
    (premises rawData window input typ parameter).relabel j =
      premises rawData window (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  simp only [premises, conjunctionRename, OriginalFunctionNeutrality.windowGraph,
    OriginalVariableRepresentative.windowGraph, graph2Rename,
    InternalOriginalStepGuard.one, sucRelabel, zRelabel,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename]

theorem activeOfPremises (rawData : Data) (window : Program 1)
    (input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active (transparentData rawData) window)
        InternalOriginalStepGuard.one input parameter)) := by
  rw [activeLeaf]
  exact InternalAcceptanceConjunctionProof.conjunctionAccept _ _
    (Fin.cons input (Fin.cons parameter Fin.elim0)) (andLeft hp) (andLeft (andRight hp))

/-- The active branch is the literal C Program, not a reflected native value. -/
theorem preparedValue (rawData : Data) (window : Program 1)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (representative rawData window) out input parameter)) :=
  InternalAcceptanceBranchProof.successorBranchIntro _ _ _ out z
    (Fin.cons input (Fin.cons parameter Fin.elim0))
    (activeOfPremises rawData window input typ parameter hp) hc

/-- A single literal observer wrapper retains the actual C output whenever
its exact frozen observer theorem supplies the common observed value. -/
theorem observedCanonicalValue (rawData : Data) (window mark : Program 1)
    (law : PreservesObserver rawData window mark) (previous : Program 2)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 previous out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (observed (OriginalFunctionNeutrality.active (transparentData rawData) window)
        mark previous) out input parameter)) := by
  apply InternalAcceptanceSupportProof.programCases mark (Fin.cons input Fin.elim0) _
  intro beta j Theta value hj hv
  rw [graph2Rename]
  simp only [consTermRename, emptyRename] at hv
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  obtain ⟨hl⟩ := law body beta Theta (out.relabel j) (input.relabel j)
    (typ.relabel j) (parameter.relabel j) value
  obtain ⟨harg⟩ := andIntro (andLeft hp') (andIntro (andRight hp') hc')
  obtain ⟨hv0⟩ := hv
  have hout := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination hl harg)) hv0
  exact observedValue _ mark previous (out.relabel j) (input.relabel j)
    (parameter.relabel j) value
    (activeOfPremises rawData window (input.relabel j) (typ.relabel j) (parameter.relabel j) hp')
    hr' ⟨hout⟩ ⟨hv0⟩

/-- This helper names the unchanged five-guard AST, in its original order. -/
def guards (active : Program 2) (previous : Program 2) : Program 2 :=
  observed active BottomRepresentative.bottomTest
    (observed active BottomSpineMeasure.measure
      (observed active OriginalVariableRepresentative.variableMark
        (observed active OriginalConstructorShape.mark
          (observed active OriginalFunctionNeutrality.mark previous))))

theorem originalPreparedRepresentative (rawData : Data) (window : Program 1) :
    (OriginalApplicationSidecar.originalData (preparedData rawData window) window).oldRepresentative =
      guards (OriginalFunctionNeutrality.active (transparentData rawData) window)
        (representative rawData window) := rfl

/-- No guards are deleted or replaced. Each guard is paid by the relevant
frozen observer supplier; only its internal graph output is simplified. -/
theorem guardsValue (rawData : Data) (window : Program 1)
    (laws : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalApplicationSidecar.originalData (preparedData rawData window) window).oldRepresentative
        out input parameter)) := by
  have h0 := preparedValue rawData window out input typ parameter hp hc
  have hn := observedCanonicalValue rawData window OriginalFunctionNeutrality.mark
    laws.2.2.1 _ out input typ parameter hp hc h0
  have hs := observedCanonicalValue rawData window OriginalConstructorShape.mark
    laws.1 _ out input typ parameter hp hc hn
  have hv := observedCanonicalValue rawData window OriginalVariableRepresentative.variableMark
    laws.2.1 _ out input typ parameter hp hc hs
  have hm := observedCanonicalValue rawData window BottomSpineMeasure.measure
    laws.2.2.2.1 _ out input typ parameter hp hc hv
  have hb := observedCanonicalValue rawData window BottomRepresentative.bottomTest
    laws.2.2.2.2 _ out input typ parameter hp hc hm
  rw [originalPreparedRepresentative]
  exact hb

/-- Full graph equivalence at arbitrary outputs, obtained internally from
Program totality and functionality, with no native-equality reflection. -/
theorem innerRepresentativeIff (rawData : Data) (window : Program 1)
    (laws : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalApplicationSidecar.originalData (preparedData rawData window) window).oldRepresentative
          out input parameter).iff
        (graph2 (canonical rawData window) out input parameter))) := by
  apply InternalAcceptanceSupportProof.programCases (canonical rawData window)
    (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hv
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact commonOutputIff _ _ value (out.relabel j) (input.relabel j) (parameter.relabel j)
    (guardsValue rawData window laws value (input.relabel j) (typ.relabel j) (parameter.relabel j) hp' hv) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGuardProof
