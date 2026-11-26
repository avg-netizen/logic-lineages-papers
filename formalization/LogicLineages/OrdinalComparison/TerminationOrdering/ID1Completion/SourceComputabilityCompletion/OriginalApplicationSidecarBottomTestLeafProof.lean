module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- S0 is literally the original nested selectedData. Its actual readyData
leaf preserves the exact whole-code bottom test at every symbolic value. -/
theorem leafBottomIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter))) :
    Nonempty (Derivation body Delta
      ((BottomRepresentative.bottomGraph value out).iff (BottomRepresentative.bottomGraph value input))) := by
  let nested := OriginalVariableRepresentative.baseData
    (OriginalConstructorShape.baseData (OriginalFunctionNeutrality.baseData data window) window) window
  have hdata : originalData data window = SpineApplicationTargets.selectedData nested window := rfl
  have hv' := hv
  rw [hdata] at hv'
  have active := SpineApplicationProof.activeValue nested window input parameter hw hv'
  have hl' := hl
  change Nonempty (Derivation body Delta
    (graph2 (InternalOriginalUniformDescentSelection.representative (originalData data window))
      out input parameter)) at hl'
  rw [hdata,SpineApplicationProof.selectedDataEq] at hl'
  exact BottomDescentProof.selectedIff (SpineApplicationTargets.parameters nested window)
    window out input parameter value active hl'

/-- Recover the actual closed C leaf, without inferring transition, fold or
child fixedness, then apply the original selected-leaf observer theorem. -/
theorem rejectedBottomIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (hz : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter))) :
    Nonempty (Derivation body Delta
      ((BottomRepresentative.bottomGraph value out).iff (BottomRepresentative.bottomGraph value input))) :=
  leafBottomIff data window out input parameter value hw hv
    (OriginalApplicationSidecarRootMarkLeafProof.closedLeafGraph data window out input parameter hc hz)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestLeafProof
