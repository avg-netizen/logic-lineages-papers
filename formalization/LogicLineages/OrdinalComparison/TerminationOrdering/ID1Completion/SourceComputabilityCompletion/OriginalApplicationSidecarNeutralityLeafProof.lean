module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Reuse the actual S0 leaf and its original neutrality law on a closed C
root. Recovering this leaf graph does not assert any fixedness property. -/
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
      ((OriginalFunctionNeutrality.markGraph value out).iff (OriginalFunctionNeutrality.markGraph value input))) := by
  exact OriginalFunctionNeutralityFullFoldProof.leafMarkIff data window out input parameter value hw hv
    (OriginalApplicationSidecarRootMarkLeafProof.closedLeafGraph data window out input parameter hc hz)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityLeafProof
