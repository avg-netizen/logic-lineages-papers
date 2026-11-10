module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z)
open OriginalApplicationSidecar OriginalNeutralApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original selected-typed function supplies T(f)=f. The established
T iff C identifies its sidecar value without introducing N(f)=f. -/
theorem typedSidecarFixed (data : Data) (window : Program 1)
    (function arrow parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window function parameter)))
    (hf : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.typedGraph
        (selectedData data window) function arrow parameter))) :
    Nonempty (Derivation body Gamma (graph2 (fold data window) function function parameter)) := by
  have htyped := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    (selectedData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (selectedData data window))
    (selectedData data window).member function arrow parameter hf
  have hi := andRight htyped
  have hv := andLeft hi
  change Nonempty (Derivation body Gamma
    (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window))
      (suc z) function parameter)) at hv
  rw [OriginalApplicationSidecarIdentityProgramsProof.sameValidity] at hv
  obtain ⟨hiff⟩ := OriginalApplicationSidecarTransitionProof.transitionIff
    data window function function arrow parameter (andIntro hw (andIntro hv (andLeft (andRight hi))))
  obtain ⟨ht⟩ := andRight (andRight hi)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hiff) ht⟩

/-- The actual argument fold gives C(argumentOut)=argumentOut, while the
requested function uses its original selected typing. The rebuilt application's
valid sidecar fixedness yields identity of the SAME selected final leaf. -/
theorem rawLeafValue (data : Data) (window : Program 1)
    (arrow d e function argument argumentOut rebuilt parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window)
        argumentOut argument parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rebuilt d e function argumentOut))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (selectedData data window))
        rebuilt rebuilt parameter)) := by
  have hw := andLeft hp
  have har := andLeft (andRight hp)
  have hm := andLeft (andRight (andRight hp))
  have hfunction := andLeft (andRight (andRight (andRight hp)))
  have hav := andLeft (andRight (andRight (andRight (andRight hp))))
  have hal := andRight (andRight (andRight (andRight (andRight hp))))
  have hfactors := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    (selectedData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (selectedData data window))
    (selectedData data window).member function arrow parameter hfunction
  have hfi := andRight hfactors
  have hfv := andLeft hfi
  have hfl := andLeft (andRight hfi)
  have hcf := typedSidecarFixed data window function arrow parameter hw hfunction
  have hwa := OriginalApplicationSidecarWindowProof.windowTransfer
    window (suc z) function argument parameter hw
  have hca := OriginalApplicationSidecarSameLeafOutputProof.canonicalFixed
    data window argumentOut argument d parameter hwa (andIntro hav hal) hn
  have hai := andRight (InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    (selectedData data window) argumentOut argument d parameter hav hal hn)
  have haov := andLeft hai
  have haol := andLeft (andRight hai)
  have hrv := InternalParameterizedCanonicalResultFoldOpeningProof.rawValidity
    (selectedData data window) arrow d e function argumentOut rebuilt parameter
    har hfl haol hm hfv haov hr
  have hrv0 := hrv
  change Nonempty (Derivation body Gamma
    (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window))
      (suc z) rebuilt parameter)) at hrv0
  rw [OriginalApplicationSidecarIdentityProgramsProof.sameValidity] at hrv0
  have hcraw := OriginalApplicationSidecarSameLeafRebuiltProof.sidecarFixed
    data window arrow d e function argumentOut rebuilt parameter har hfl haol hr hrv0 hcf hca
  have hrl := InternalParameterizedCanonicalResultFoldOpeningProof.rawLeft
    d e function argumentOut rebuilt hr
  have hwr := OriginalApplicationSidecarWindowProof.windowTransfer
    window (suc z) function rebuilt parameter hw
  obtain ⟨hiff⟩ := OriginalApplicationSidecarTransitionProof.transitionIff
    data window rebuilt rebuilt e parameter (andIntro hwr (andIntro hrv0 hrl))
  obtain ⟨hcraw⟩ := hcraw
  have ht := Derivation.implicationElimination (Derivation.conjunctionRight hiff) hcraw
  exact OriginalApplicationSidecarSameLeafIterationProof.selectedFixedValue
    (selectedData data window).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (selectedData data window))
    rebuilt parameter hrv ⟨ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationLeafProof
