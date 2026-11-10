module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafProof
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

/-- Literal identity graph of the SAME selected leaf at the rebuilt parent. -/
theorem leafIff (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut rebuilt out parameter : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Delta
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut arg parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 application rebuilt d e functionOut argumentOut))) :
    Nonempty (Derivation body Delta
      ((graph2 (InternalParameterizedCanonicalResultFold.leaf (selectedData data window)) out rebuilt parameter).iff
        (eqn out rebuilt))) :=
  OriginalApplicationSidecarSameLeafIterationProof.selfOutputIff
    (InternalParameterizedCanonicalResultFold.leaf (selectedData data window)) out rebuilt parameter
    (OriginalApplicationSidecarSameLeafApplicationProof.rebuiltLeafValue data window
      arrow d e fp ap fn arg parent functionOut argumentOut rebuilt parameter hw hc hv hf ha hr)

theorem actualOriginalApplicationSidecarSameFinalLeaf :
    OriginalApplicationSidecarSameLeafTargets.ActualOriginalApplicationSidecarSameFinalLeaf := by
  intro body data window alpha Delta arrow d e fp ap fn arg parent functionOut argumentOut rebuilt out parameter
  let P := OriginalFunctionNeutrality.windowGraph window parent parameter ⊓
    (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) parent parameter ⊓
        (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) functionOut fn parameter ⊓
          (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut arg parameter ⊓
            graph4 application rebuilt d e functionOut argumentOut))))
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := leafIff data window arrow d e fp ap fn arg parent functionOut argumentOut rebuilt out parameter
    (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
    (andLeft (andRight (andRight (andRight hp))))
    (andLeft (andRight (andRight (andRight (andRight hp)))))
    (andRight (andRight (andRight (andRight (andRight hp)))))
  rw [InternalControlGraphSupportProof.equalEqn]
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafProof.actualOriginalApplicationSidecarSameFinalLeaf
