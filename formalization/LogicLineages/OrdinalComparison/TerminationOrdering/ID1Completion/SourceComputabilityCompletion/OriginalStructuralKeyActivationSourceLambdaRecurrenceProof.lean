module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaRecurrenceProof
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

/-- Extract the unrefined membership slice directly. This avoids unfolding
the large variable-refined Data just to compare its unchanged member field. -/
theorem unrefinedMemberAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (out typ parameter context gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (normalizedData (transparent p H G W).base).member out typ parameter).iff
        (graph2 (InternalOriginalUniformContextMembership.contextMember p.base.member)
          out typ context))) := by
  obtain ⟨hs⟩ := InternalOriginalUniformContextMembershipInternalProof.actualOriginalUniformMembershipSlice
    p.base.member body alpha Gamma out typ parameter context gamma
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination hs hp⟩

/-- The actual source recurrence, with memberships normalized at the SAME
outer context and the SAME original lambda child and extended Gamma. -/
theorem validatorSourceLambda (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
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
      ((graph2 (sourceValidator (transparent p H G W).base) (numeral 1) packed parameter).iff
        ((graph2 (InternalOriginalUniformContextMembership.contextMember p.base.member) (numeral 1) typ c ⊓
          (graph2 (InternalOriginalUniformContextMembership.contextMember p.base.member) (numeral 1) domain c ⊓
            ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))) ⊓
          graph2 (sourceValidator (transparent p H G W).base) (numeral 1) child childParam))) := by
  let N := normalizedData (transparent p H G W).base
  have htag := rawTagValue packed typ payload middle hp ht
  have hnode := sourceNodeEquation N packed parameter htag
  have hrec := lambdaAcceptanceEquation (sourceRoot N) (targetRoot N) N.member packed parameter
    (SourceLambdaRootFactors N packed parameter) htag hnode
  have hroot := sourceFactors_iff N packed parameter typ payload middle domain bodyPayload requestedDomain codomain hp ht hm hf
  have hmembers := andIff (unrefinedMemberAt p H G W (numeral 1) typ parameter c gamma hparam)
    (andIff (unrefinedMemberAt p H G W (numeral 1) domain parameter c gamma hparam)
      (iffSelf ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain)))
  have hbody := rootLambdaChild_iff (sourceRoot N) (targetRoot N) N.member
    packed typ payload middle domain bodyPayload requestedDomain codomain parameter c gamma extended child childParam
    hp ht hm hf hparam hext hchild hchildParam
  exact iffCompose hrec (andIff (iffCompose hroot hmembers) hbody)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceLambdaRecurrenceProof
