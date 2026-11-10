module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionActiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionValueProof
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


/-- The actual S1 transition has the supplied C output, with no new invariant premise. -/
theorem transitionAtSidecarOutput (data : Data) (window : Program 1)
    (candidate input typ parameter : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (sourceHyp data window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) candidate input parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph
        (selectedData data window).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (selectedData data window))
        candidate input parameter)) := by
  have hr := OriginalApplicationSidecarTransitionActiveProof.activeValue data window
    candidate input typ parameter hp hc
  have hInv := OriginalApplicationSidecarInvariantProof.invariantAtInput data window
    candidate input typ parameter (andIntro (andRight hp) hc)
  have hv := andLeft hInv
  have hlc := andLeft (andRight hInv)
  have hb := andRight (andRight hInv)
  have hli := andRight (andRight hp)
  have hv' : Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.validGraph
        (InternalOriginalUniformDescentSelection.validity (selectedData data window)) candidate parameter)) := by
    change Nonempty (Derivation body Delta (graph2
      (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) candidate parameter))
    rw [OriginalApplicationSidecarIdentityProgramsProof.sameValidity]
    exact hv
  have chosen := OriginalApplicationSidecarTransitionChoiceProof.chooseBounded
    (InternalOriginalUniformDescentSelection.validity (selectedData data window))
    candidate input typ parameter hv' hlc hli hb
  let xs : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply compositionValue
    (InternalParameterizedBoundedDescentNormalizer.choose
      (InternalOriginalUniformDescentSelection.validity (selectedData data window)))
    (Fin.cons (selectedData data window).oldRepresentative
      (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    candidate xs (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))) chosen
  intro i
  exact Fin.cases hr (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionValueProof
