module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof
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


/-- Internally bind C's actual output, then use functionality in both directions. -/
theorem transitionIff (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((InternalParameterizedBoundedDescentNormalizer.transitionGraph
          (selectedData data window).oldRepresentative
          (InternalOriginalUniformDescentSelection.validity (selectedData data window))
          out input parameter).iff
        (graph2 (fold data window) out input parameter))) := by
  change Nonempty (Derivation body Delta
    ((graph2 (InternalParameterizedBoundedDescentNormalizer.transition
        (selectedData data window).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (selectedData data window)))
        out input parameter).iff (graph2 (fold data window) out input parameter)))
  apply programCases (fold data window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta candidate hj hc
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hc
  have hp' := renameInto hp j Theta hj
  rw [sourceHypRename] at hp'
  have ht := OriginalApplicationSidecarTransitionValueProof.transitionAtSidecarOutput data window
    candidate (input.relabel j) (typ.relabel j) (parameter.relabel j) hp' hc
  exact commonOutputIff _ _ candidate (out.relabel j) (input.relabel j) (parameter.relabel j) ht hc

theorem actualOriginalApplicationSidecarTransitionIdentification :
    OriginalApplicationSidecarTransitionTargets.ActualOriginalApplicationSidecarTransitionIdentification := by
  intro body data window alpha Delta out input typ parameter
  obtain ⟨h⟩ := transitionIff (body := body) (Delta := sourceHyp data window input typ parameter :: Delta)
    data window out input typ parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGuardProof.actualOriginalApplicationSidecarGuardRedundancy
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof.actualOriginalApplicationSidecarTransitionIdentification
