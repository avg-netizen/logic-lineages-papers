module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarInvariant OriginalApplicationSidecarInvariantSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- Rebuilt children have their own actual output types, validities and bounds.
The existing rawValidity helper binds fresh output payloads internally. -/
theorem applicationAtOutputs (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out typ parameter : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (hs : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) parent typ parameter)))
    (hf : Nonempty (Derivation body Gamma (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (fold data window) argumentOut arg parameter)))
    (hp : Nonempty (Derivation body Gamma (graph2 (fold data window) out parent parameter)))
    (hfi : Nonempty (Derivation body Gamma (outputInvariant data window functionOut fn arrow parameter)))
    (hai : Nonempty (Derivation body Gamma (outputInvariant data window argumentOut arg d parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window out parent typ parameter)) := by
  have hr := OriginalApplicationSidecarEquationSupportProof.applicationBackward data window
    arrow d e fp ap fn arg parent functionOut argumentOut out parameter hc (InternalApplicationStepPeelSupportProof.andLeft hs) hf ha hp
  have children := OriginalApplicationInverseValidityProof.sourceRecover
    (originalData data window) arrow d e fp ap fn arg parent parameter hc (InternalApplicationStepPeelSupportProof.andLeft hs)
  have hv := InternalParameterizedCanonicalResultFoldOpeningProof.rawValidity
    (originalData data window) arrow d e functionOut argumentOut out parameter (InternalApplicationStepPeelSupportProof.andLeft hc)
    (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hfi)) (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hai)) (InternalApplicationStepPeelSupportProof.andLeft children)
    (InternalApplicationStepPeelSupportProof.andLeft hfi) (InternalApplicationStepPeelSupportProof.andLeft hai) hr
  have hleft := InternalParameterizedCanonicalResultFoldOpeningProof.rawLeft
    d e functionOut argumentOut out hr
  have oldLeft := InternalCanonicalResultFoldInvariantApplicationSupportProof.packedLeft
    d e fp ap parent (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hc)))
  have htype := valueUnique InternalUnpair.left e typ (Fin.cons parent Fin.elim0) oldLeft (InternalApplicationStepPeelSupportProof.andRight hs)
  have hleft' := outputTransport InternalUnpair.left e typ (Fin.cons out Fin.elim0) htype hleft
  have oldFunctionLeft := pairLeft fn arrow fp (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hc))
  have oldArgumentLeft := pairLeft arg d ap (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hc)))
  have originalRaw := InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    d e fn arg fp ap parent (pairRight fn arrow fp (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hc)))
    (pairRight arg d ap (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hc)))) (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hc)))
  have orderPremises := InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft hc)
    (InternalApplicationStepPeelSupportProof.andIntro oldFunctionLeft (InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hfi))
      (InternalApplicationStepPeelSupportProof.andIntro oldArgumentLeft (InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hai))
        (InternalApplicationStepPeelSupportProof.andIntro originalRaw (InternalApplicationStepPeelSupportProof.andIntro hr
          (InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hfi)) (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hai)))))))))
  obtain ⟨order⟩ := InternalOriginalApplicationOrderProof.actualOriginalApplicationCodeMonotonicity
    body α Gamma arrow d e fn arg functionOut argumentOut parent out
  obtain ⟨orderPremises⟩ := orderPremises
  exact InternalApplicationStepPeelSupportProof.andIntro hv (InternalApplicationStepPeelSupportProof.andIntro hleft' ⟨Derivation.implicationElimination order orderPremises⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantApplicationProof
