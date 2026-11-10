module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionActiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionInactiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGuardProof
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


/-- All actual witnesses remain bound inside the original graph calculus. -/
theorem activeIffAtType (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (selectedData data window).oldRepresentative out input parameter).iff
        (graph2 (representative data window) out input parameter))) := by
  apply programCases (fold data window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta candidate hj hc
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hc
  have hp' := renameInto hp j Theta hj
  rw [sourceHypRename] at hp'
  have ha := activeOfSource data window (input.relabel j) (typ.relabel j) (parameter.relabel j) hp'
  have hr := refinedValue data window candidate (input.relabel j) (parameter.relabel j) ha hc
  have hs := OriginalApplicationSidecarTransitionActiveProof.activeValue data window
    candidate (input.relabel j) (typ.relabel j) (parameter.relabel j) hp' hc
  exact commonOutputIff _ _ candidate (out.relabel j) (input.relabel j) (parameter.relabel j) hs hr

theorem activeIff (data : Data) (window : Program 1)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active data window) (suc z) input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (selectedData data window).oldRepresentative out input parameter).iff
        (graph2 (representative data window) out input parameter))) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro beta j Theta typ hj hl
  rw [binaryIffRename]
  simp only [consTermRename, emptyRename] at hl
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename, sucRelabel, zRelabel] at ha'
  exact activeIffAtType data window (out.relabel j) (input.relabel j) typ (parameter.relabel j)
    (sourceOfActive data window (input.relabel j) typ (parameter.relabel j) ha' hl)

/-- The inactive branch is preserved; the all-input RHS is R, not C. -/
theorem actualOriginalApplicationSidecarGuardRedundancy :
    OriginalApplicationSidecarTransitionTargets.ActualOriginalApplicationSidecarGuardRedundancy := by
  intro body data window alpha Delta out input parameter
  let accepted := graph2 (OriginalFunctionNeutrality.active data window) (suc z) input parameter
  apply formulaCases accepted
  · exact activeIff data window out input parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact OriginalApplicationSidecarTransitionInactiveProof.inactiveIff data window out input parameter
      (activeZero data window input parameter ⟨Derivation.hypothesis List.mem_cons_self⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGuardProof
