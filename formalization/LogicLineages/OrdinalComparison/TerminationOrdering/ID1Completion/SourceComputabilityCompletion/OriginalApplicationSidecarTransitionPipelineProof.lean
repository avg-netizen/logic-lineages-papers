module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
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
open OriginalApplicationSidecarTransitionPipelineDefinitions
/-- Only the retained representative projection is reduced. -/
theorem selectedOldRepresentative (data : Data) (window : Program 1) :
    (selectedData data window).oldRepresentative = bottom data window := rfl

theorem sourceHypRename {beta : Type} (data : Data) (window : Program 1)
    (input typ parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (sourceHyp data window input typ parameter).relabel j =
      sourceHyp data window (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  simp only [sourceHyp, InternalRecursionGraphStepSyntaxProof.conjunctionRename,
    OriginalFunctionNeutrality.windowGraph, OriginalVariableRepresentative.windowGraph,
    graph2Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename]

theorem activeOfSource (data : Data) (window : Program 1)
    (input typ parameter : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active data window) (suc z) input parameter)) := by
  rw [OriginalApplicationSidecarIdentityProgramsProof.activeOriginal]
  exact InternalAcceptanceConjunctionProof.conjunctionAccept _ _
    (Fin.cons input (Fin.cons parameter Fin.elim0)) (andLeft hp) (andLeft (andRight hp))

theorem sourceOfActive (data : Data) (window : Program 1)
    (input typ parameter : OrdinaryArithmetic.Term alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active data window) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
    Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)) := by
  rw [OriginalApplicationSidecarIdentityProgramsProof.activeOriginal] at ha
  have h := InternalAcceptanceConjunctionProof.conjunctionRecover _ _
    (Fin.cons input (Fin.cons parameter Fin.elim0)) ha
  exact andIntro (andLeft h) (andIntro (andRight h) hl)

theorem activeZero (data : Data) (window : Program 1)
    (input parameter : OrdinaryArithmetic.Term alpha)
    (hn : Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active data window) (suc z) input parameter).not)) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active data window) z input parameter)) := by
  rw [OriginalApplicationSidecarIdentityProgramsProof.activeOriginal] at hn ⊢
  exact InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hn

theorem refinedValue (data : Data) (window : Program 1)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalFunctionNeutrality.active data window) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (representative data window) out input parameter)) :=
  InternalAcceptanceBranchProof.successorBranchIntro _ _ _ out z
    (Fin.cons input (Fin.cons parameter Fin.elim0)) ha hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
