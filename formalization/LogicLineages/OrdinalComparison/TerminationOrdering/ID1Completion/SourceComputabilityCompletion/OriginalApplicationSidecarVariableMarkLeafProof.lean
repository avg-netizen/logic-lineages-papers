module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkLeafProof
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

/-- S0 is literally the original variable-selected Data at the existing
nested neutrality/shape baseData; its actual leaf retains whole-variable marks. -/
theorem leafMarkIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalVariableRepresentative.markGraph value out).iff (OriginalVariableRepresentative.markGraph value input))) := by
  obtain ⟨law⟩ := OriginalVariableRepresentativeSelectedProof.selectedMarkPreservation
    (OriginalConstructorShape.baseData (OriginalFunctionNeutrality.baseData data window) window)
    window body alpha Delta out input parameter value
  obtain ⟨premises⟩ := andIntro hw (andIntro hv hl)
  exact ⟨Derivation.implicationElimination law premises⟩

/-- Recover the actual closed C leaf, without inferring transition, fold or
child fixedness, then apply the original selected-leaf observer theorem. -/
theorem rejectedMarkIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (hz : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalVariableRepresentative.markGraph value out).iff (OriginalVariableRepresentative.markGraph value input))) :=
  leafMarkIff data window out input parameter value hw hv
    (OriginalApplicationSidecarRootMarkLeafProof.closedLeafGraph data window out input parameter hc hz)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkLeafProof
