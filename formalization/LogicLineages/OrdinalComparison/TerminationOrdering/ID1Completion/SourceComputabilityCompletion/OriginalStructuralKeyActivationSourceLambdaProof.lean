module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTransparentDecoderValidatorCollapse OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalTransparentDecoderValidatorCollapseLambdaChildProof
open OriginalTransparentDecoderValidatorCollapseLambdaSourceProof
open OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
open OriginalHereditaryValidity OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalLambdaNodeProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof
open OriginalTransparentLambdaFinalLogicProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

open OriginalStructuralKeyActivationSourceLambdaRecurrenceProof
/-- The source child induction hypothesis retains the mandatory original G.
No typedness or calibration premise is used to reflect source acceptance. -/
theorem sourceLambdaStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
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
      (Acceptance (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource child childParam))) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource packed parameter)) :=
  iffCompose (validatorSourceLambda p H G W packed typ payload middle domain bodyPayload requestedDomain codomain
    parameter c gamma extended child childParam hp ht hm hf hparam hext hchild hchildParam)
    (iffCompose (andIff (iffSelf _) hbody)
      (iffReverse (sourceLambdaCoordinatesIff H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W
        packed parameter typ payload middle domain bodyPayload requestedDomain codomain
        child c gamma extended childParam hp ht hm hf hchild hparam hext hchildParam)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaProof
