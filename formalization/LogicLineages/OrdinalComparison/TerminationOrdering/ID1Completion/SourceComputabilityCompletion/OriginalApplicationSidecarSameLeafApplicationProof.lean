module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafRebuiltProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafApplicationProof
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

/-- Source inversion derives both child source/type premises, and actual N1
outputs supply their transition invariants. C-fixedness is then PROVED, not
assumed. The rebuilt application's valid T-fixed state selects the SAME L1. -/
theorem rebuiltLeafValue (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut rebuilt parameter : OrdinaryArithmetic.Term alpha)
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
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (selectedData data window)) rebuilt rebuilt parameter)) := by
  have children := OriginalApplicationInverseValidityProof.sourceRecover (selectedData data window)
    arrow d e fp ap fn arg parent parameter hc hv
  have hfl := pairLeft fn arrow fp (andLeft (andRight hc))
  have hal := pairLeft arg d ap (andLeft (andRight (andRight hc)))
  have hfv := andLeft (andRight children)
  have hav := andRight (andRight children)
  have hwf := OriginalApplicationSidecarWindowProof.windowTransfer window (suc z) parent fn parameter hw
  have hwa := OriginalApplicationSidecarWindowProof.windowTransfer window (suc z) parent arg parameter hw
  have hcf := OriginalApplicationSidecarSameLeafOutputProof.canonicalFixed data window
    functionOut fn arrow parameter hwf (andIntro hfv hfl) hf
  have hca := OriginalApplicationSidecarSameLeafOutputProof.canonicalFixed data window
    argumentOut arg d parameter hwa (andIntro hav hal) ha
  have hfi := andRight (InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    (selectedData data window) functionOut fn arrow parameter hfv hfl hf)
  have hai := andRight (InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    (selectedData data window) argumentOut arg d parameter hav hal ha)
  have hfol := andLeft (andRight hfi)
  have haol := andLeft (andRight hai)
  have hrv := InternalParameterizedCanonicalResultFoldOpeningProof.rawValidity (selectedData data window)
    arrow d e functionOut argumentOut rebuilt parameter (andLeft hc) hfol haol
    (andLeft children) (andLeft hfi) (andLeft hai) hr
  have hrv0 := hrv
  change Nonempty (Derivation body Delta (graph2
    (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) rebuilt parameter)) at hrv0
  rw [OriginalApplicationSidecarIdentityProgramsProof.sameValidity] at hrv0
  have hraw := OriginalApplicationSidecarSameLeafRebuiltProof.sidecarFixed data window
    arrow d e functionOut argumentOut rebuilt parameter (andLeft hc) hfol haol hr hrv0 hcf hca
  have hrl := InternalParameterizedCanonicalResultFoldOpeningProof.rawLeft d e functionOut argumentOut rebuilt hr
  have hwr := OriginalApplicationSidecarWindowProof.windowTransfer window (suc z) parent rebuilt parameter hw
  obtain ⟨hiff⟩ := OriginalApplicationSidecarTransitionProof.transitionIff data window rebuilt rebuilt e parameter
    (andIntro hwr (andIntro hrv0 hrl))
  obtain ⟨hraw⟩ := hraw
  have ht := Derivation.implicationElimination (Derivation.conjunctionRight hiff) hraw
  exact OriginalApplicationSidecarSameLeafIterationProof.selectedFixedValue
    (selectedData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (selectedData data window)) rebuilt parameter hrv ⟨ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafApplicationProof
