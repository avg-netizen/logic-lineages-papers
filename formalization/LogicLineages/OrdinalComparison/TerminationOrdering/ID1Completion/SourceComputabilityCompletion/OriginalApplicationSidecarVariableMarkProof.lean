module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkProof
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

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)

/-- One direct split at the literal C root guard. All observer values and
original window/source/output graphs retain the frozen scope. -/
theorem actualOriginalApplicationSidecarVariableMark :
    OriginalApplicationSidecarVariableMarkTargets.ActualOriginalApplicationSidecarVariableMark := by
  intro body data window alpha Delta out input typ parameter value
  let A := OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) input typ parameter ⊓
      graph2 (fold data window) out input parameter)
  have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := andLeft hA
  have hv := andLeft (andLeft (andRight hA))
  have hc := andRight (andRight hA)
  have result : Nonempty (Derivation body (A :: Delta)
      ((OriginalVariableRepresentative.markGraph value out).iff (OriginalVariableRepresentative.markGraph value input))) := by
    let accepted := graph2 (InternalParameterizedApplicationResultStack.openGuardP
      (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) (suc z) input parameter
    apply formulaCases accepted
    · exact OriginalApplicationSidecarVariableMarkApplicationProof.openingMarkIff data window out input parameter value
        (withHyp hv accepted) (withHyp hc accepted) ⟨Derivation.hypothesis List.mem_cons_self⟩
    · have hz : Nonempty (Derivation body (accepted.not :: A :: Delta)
          (graph2 (InternalParameterizedApplicationResultStack.openGuardP
            (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter)) :=
        InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
          (Fin.cons input (Fin.cons parameter Fin.elim0))
          ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact OriginalApplicationSidecarVariableMarkLeafProof.rejectedMarkIff data window out input parameter value
        (withHyp hw accepted.not) (withHyp hv accepted.not) (withHyp hc accepted.not) hz
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkProof.actualOriginalApplicationSidecarVariableMark
