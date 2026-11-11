module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (Data)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderInternalAcceptanceUnaryProof (lambdaIff)
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalTransparentDecoderValidatorCollapseLambdaChildProof
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalTransparentLambdaValidityInternalLambdaSupportProof
open OriginalTransparentLambdaValidityInternalLambdaNodeProof
open OriginalTransparentLambdaFinalLogicProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Original target lambda acceptance, preserving G at the same outer context
and changing only the original encoded Gamma by one actual cons. -/
theorem packedLambda (H G : Program 1)
    (packed typ payload middle domain bodyPayload requestedDomain codomain
      parameter c gamma extended child childParam : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Gamma (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Gamma (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (hparam : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hext : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (hchild : Nonempty (Derivation body Gamma (StepPair child codomain bodyPayload)))
    (hchildParam : Nonempty (Derivation body Gamma (StepPair childParam c extended))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter).iff
        (((equal typ (numeral 0)).not ⊓ equal requestedDomain domain) ⊓
          graph2 (OriginalTypedDecoder.target H G) (numeral 1) child childParam))) := by
  let P := graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter
  let Q := ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain) ⊓
    graph2 (OriginalTypedDecoder.target H G) (numeral 1) child childParam
  have hforward : Nonempty (Derivation body (P :: Gamma) Q) := by
    have hfields := targetFieldsElim H G packed parameter typ payload c gamma
      (addAssumption hp P) (addAssumption hparam P)
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have he := lambdaIff H payload middle domain bodyPayload typ requestedDomain codomain gamma extended
      (addAssumption ht P) (addAssumption hm P) (addAssumption hf P) (addAssumption hext P)
    have hbody := iffForward he (andRight hfields)
    exact andIntro (andIntro (andLeft hbody) (andLeft (andRight hbody)))
      (targetFieldsIntro H G child childParam codomain bodyPayload c extended
        (addAssumption hchild P) (addAssumption hchildParam P) (andLeft hfields)
        (andRight (andRight hbody)))
  have hbackward : Nonempty (Derivation body (Q :: Gamma) P) := by
    have hq : Nonempty (Derivation body (Q :: Gamma) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hfields := targetFieldsElim H G child childParam codomain bodyPayload c extended
      (addAssumption hchild Q) (addAssumption hchildParam Q) (andRight hq)
    have he := lambdaIff H payload middle domain bodyPayload typ requestedDomain codomain gamma extended
      (addAssumption ht Q) (addAssumption hm Q) (addAssumption hf Q) (addAssumption hext Q)
    have hbody := iffBackward he (andIntro (andLeft (andLeft hq))
      (andIntro (andRight (andLeft hq)) (andRight hfields)))
    exact targetFieldsIntro H G packed parameter typ payload c gamma
      (addAssumption hp Q) (addAssumption hparam Q) (andLeft hfields) hbody
  obtain ⟨hforward⟩ := hforward
  obtain ⟨hbackward⟩ := hbackward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hforward)
    (Derivation.implicationIntroduction hbackward)⟩

/-- The actual lambda-child selector and original shape bridge discharge the
complete local target recurrence; no child acceptance is assumed here. -/
theorem validatorLambda (data : Data)
    (packed typ payload middle domain bodyPayload requestedDomain codomain
      parameter c gamma extended child childParam : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Gamma (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Gamma (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (hparam : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hext : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (hchild : Nonempty (Derivation body Gamma (StepPair child codomain bodyPayload)))
    (hchildParam : Nonempty (Derivation body Gamma (StepPair childParam c extended))) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetValidator data) (numeral 1) packed parameter).iff
        (((equal typ (numeral 0)).not ⊓ equal requestedDomain domain) ⊓
          graph2 (targetValidator data) (numeral 1) child childParam))) := by
  let N := normalizedData data
  let one := InternalLessThan.constantOne 2
  have htag := rawTagValue packed typ payload middle hp ht
  have hnode := targetNodeEquation N packed parameter htag
  have he := lambdaAcceptanceEquation (targetRoot N) one one packed parameter
    (OriginalTransparentLambdaValidityInternal.LambdaShape packed) htag hnode
  have hshape := lambdaShape_iff packed typ payload middle domain bodyPayload requestedDomain codomain hp ht hm hf
  have hbody := rootLambdaChild_iff (targetRoot N) one one
    packed typ payload middle domain bodyPayload requestedDomain codomain parameter c gamma extended child childParam
    hp ht hm hf hparam hext hchild hchildParam
  exact iffCompose he (andIff hshape hbody)

/-- The target induction hypothesis is used only at the actual body and its
own original extended parameter. -/
theorem targetLambdaStep (data : Data) (H G : Program 1)
    (packed typ payload middle domain bodyPayload requestedDomain codomain
      parameter c gamma extended child childParam : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Gamma (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Gamma (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (hparam : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hext : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (hchild : Nonempty (Derivation body Gamma (StepPair child codomain bodyPayload)))
    (hchildParam : Nonempty (Derivation body Gamma (StepPair childParam c extended)))
    (hbody : Nonempty (Derivation body Gamma
      (Acceptance (targetValidator data) (OriginalTypedDecoder.target H G) child childParam))) :
    Nonempty (Derivation body Gamma
      (Acceptance (targetValidator data) (OriginalTypedDecoder.target H G) packed parameter)) :=
  iffCompose (validatorLambda data packed typ payload middle domain bodyPayload requestedDomain codomain
    parameter c gamma extended child childParam hp ht hm hf hparam hext hchild hchildParam)
    (iffCompose (andIff (iffSelf _) hbody)
      (iffReverse (packedLambda H G packed typ payload middle domain bodyPayload requestedDomain codomain
        parameter c gamma extended child childParam hp ht hm hf hparam hext hchild hchildParam)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaProof
