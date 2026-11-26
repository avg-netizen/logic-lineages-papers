module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure
open InternalOriginalUniformDescentSelection (Data)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderInternalAcceptanceBinaryProof (applicationIff)
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalTransparentLambdaFinalApplicationSelectorProof
open OriginalTransparentLambdaFinalApplicationNodeProof
open OriginalTransparentLambdaFinalApplicationAcceptanceProof
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original packed target has the SAME G factor at both children.
No context validity is added as a premise. -/
theorem packedApplication (H G : Program 1)
    (arrow d e fp ap fn arg packed parameter raw middle c gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg packed)))
    (hp : Nonempty (Derivation body Gamma (StepPair packed e raw)))
    (ht : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) middle)))
    (hb : Nonempty (Derivation body Gamma (StepBinaryPayload middle d fp ap)))
    (hparameter : Nonempty (Derivation body Gamma (StepPair parameter c gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter).iff
        (graph2 (OriginalTypedDecoder.target H G) (numeral 1) fn parameter ⊓
          graph2 (OriginalTypedDecoder.target H G) (numeral 1) arg parameter))) := by
  let P := graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter
  let Q := graph2 (OriginalTypedDecoder.target H G) (numeral 1) fn parameter ⊓
    graph2 (OriginalTypedDecoder.target H G) (numeral 1) arg parameter
  have hf : Nonempty (Derivation body (P :: Gamma) Q) := by
    have hfields := targetFieldsElim H G packed parameter e raw c gamma
      (addAssumption hp P) (addAssumption hparameter P)
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have he := applicationIff H raw middle d fp ap e arrow gamma
      (addAssumption ht P) (addAssumption hb P) (addAssumption (andLeft hc) P)
    have hchildren := iffForward he (andRight hfields)
    exact andIntro
      (targetFieldsIntro H G fn parameter arrow fp c gamma
        (addAssumption (andLeft (andRight hc)) P) (addAssumption hparameter P)
        (andLeft hfields) (andLeft hchildren))
      (targetFieldsIntro H G arg parameter d ap c gamma
        (addAssumption (andLeft (andRight (andRight hc))) P) (addAssumption hparameter P)
        (andLeft hfields) (andRight hchildren))
  have hr : Nonempty (Derivation body (Q :: Gamma) P) := by
    have hh : Nonempty (Derivation body (Q :: Gamma) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hfn := targetFieldsElim H G fn parameter arrow fp c gamma
      (addAssumption (andLeft (andRight hc)) Q) (addAssumption hparameter Q) (andLeft hh)
    have harg := targetFieldsElim H G arg parameter d ap c gamma
      (addAssumption (andLeft (andRight (andRight hc))) Q) (addAssumption hparameter Q) (andRight hh)
    have he := applicationIff H raw middle d fp ap e arrow gamma
      (addAssumption ht Q) (addAssumption hb Q) (addAssumption (andLeft hc) Q)
    exact targetFieldsIntro H G packed parameter e raw c gamma
      (addAssumption hp Q) (addAssumption hparameter Q) (andLeft hfn)
      (iffBackward he (andIntro (andRight hfn) (andRight harg)))
  obtain ⟨hf⟩ := hf
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hr)⟩

/-- HT application recurrence has no source-window callback. -/
theorem validatorApplication (data : Data)
    (arrow d e fp ap fn arg packed parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg packed))) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetValidator data) (numeral 1) packed parameter).iff
        (graph2 (targetValidator data) (numeral 1) fn parameter ⊓
          graph2 (targetValidator data) (numeral 1) arg parameter))) := by
  let N := normalizedData data
  let one := InternalLessThan.constantOne 2
  have hs := rawTypeAndTag arrow d e fp ap fn arg packed hc
  have hn := targetApplicationNode N packed parameter e (andLeft hs) (andRight hs)
  have hchildren := childrenEquation (targetRoot N) one one
    arrow d e fp ap fn arg packed parameter hc
  have he := acceptanceAtChildren (targetRoot N) one one one
    packed parameter e fn arg (andRight hs) hn hchildren
  let Q := graph2 (targetValidator data) (numeral 1) fn parameter ⊓
    graph2 (targetValidator data) (numeral 1) arg parameter
  have hunit : Nonempty (Derivation body Gamma
      ((graph2 one (numeral 1) e parameter ⊓ Q).iff Q)) := by
    obtain ⟨h1⟩ := InternalLessThanSupportProof.oneConstantValue
      (body := body) (Gamma := Q :: Gamma) ![e,parameter]
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction (Derivation.conjunctionRight
        (Derivation.hypothesis List.mem_cons_self)))
      (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction h1
        (Derivation.hypothesis List.mem_cons_self)))⟩
  exact iffCompose he hunit

/-- One induction application step at explicit original coordinates. -/
theorem targetApplicationStep (data : Data) (H G : Program 1)
    (arrow d e fp ap fn arg packed parameter raw middle c gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg packed)))
    (hp : Nonempty (Derivation body Gamma (StepPair packed e raw)))
    (ht : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) middle)))
    (hb : Nonempty (Derivation body Gamma (StepBinaryPayload middle d fp ap)))
    (hparameter : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hfn : Nonempty (Derivation body Gamma
      (Acceptance (targetValidator data) (OriginalTypedDecoder.target H G) fn parameter)))
    (harg : Nonempty (Derivation body Gamma
      (Acceptance (targetValidator data) (OriginalTypedDecoder.target H G) arg parameter))) :
    Nonempty (Derivation body Gamma
      (Acceptance (targetValidator data) (OriginalTypedDecoder.target H G) packed parameter)) :=
  iffCompose (validatorApplication data arrow d e fp ap fn arg packed parameter hc)
    (iffCompose (andIff hfn harg)
      (iffReverse (packedApplication H G arrow d e fp ap fn arg packed parameter raw middle c gamma
        hc hp ht hb hparameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetApplicationProof
