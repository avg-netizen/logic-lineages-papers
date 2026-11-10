module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The checked final canonical consumer supplies only transition fixedness.
The actual transition iff C then yields sidecar fixedness of that output. -/
theorem canonicalFixed (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (selectedData data window) input typ parameter)))
    (hn : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (fold data window) out out parameter)) := by
  have hc := InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    (selectedData data window) out input typ parameter (andLeft hs) (andRight hs) hn
  have hi := andRight hc
  have hv := andLeft hi
  change Nonempty (Derivation body Delta
    (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) out parameter)) at hv
  rw [OriginalApplicationSidecarIdentityProgramsProof.sameValidity] at hv
  have hwout := OriginalApplicationSidecarWindowProof.windowTransfer window (suc z) input out parameter hw
  obtain ⟨hiff⟩ := OriginalApplicationSidecarTransitionProof.transitionIff data window out out typ parameter
    (andIntro hwout (andIntro hv (andLeft (andRight hi))))
  obtain ⟨hf⟩ := andRight (andRight hi)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hiff) hf⟩

theorem actualOriginalApplicationSidecarCanonicalOutputFixed :
    OriginalApplicationSidecarSameLeafTargets.ActualOriginalApplicationSidecarCanonicalOutputFixed := by
  intro body data window alpha Delta out input typ parameter
  let P := OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises (selectedData data window) input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out input parameter)
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := canonicalFixed data window out input typ parameter (andLeft hp)
    (andLeft (andRight hp)) (andRight (andRight hp))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafOutputProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafOutputProof.actualOriginalApplicationSidecarCanonicalOutputFixed
