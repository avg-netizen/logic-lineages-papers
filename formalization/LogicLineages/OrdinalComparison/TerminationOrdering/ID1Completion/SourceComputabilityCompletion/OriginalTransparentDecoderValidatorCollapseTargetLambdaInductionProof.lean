module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetApplicationInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
open OriginalTransparentDecoderValidatorCollapseInductionBindingProof
open OriginalTransparentDecoderValidatorCollapseTargetLambdaProof
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
open OriginalTransparentLambdaValidity
open SourceComputabilityFormulaSupportProof (numeral)
open InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The actual lambda payload strictly decreases even if its outer type is
malformed. Rejection is therefore covered without a supplied shape premise. -/
theorem lambdaByInduction (data : Data) (H G : Program 1)
    (payload raw parameter : OTerm alpha)
    (hind : Nonempty (Derivation body Gamma
      (belowPayload (targetValidator data) (OriginalTypedDecoder.target H G) payload)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Gamma (OriginalTransparentLambdaValidityInternal.TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      (Acceptance (targetValidator data) (OriginalTypedDecoder.target H G) raw parameter)) := by
  apply lambdaCoordinatesCases raw parameter _ ht
  intro beta j Delta typ parentPayload middle domain bp requestedDomain codomain c gamma extended child childParam
    hj hpacked htag hmiddle harrow hparam hext hchild hchildParam
  rw [acceptanceRename]
  have hind' := renameInto hind j Delta hj
  rw [belowPayloadRename] at hind'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  obtain ⟨he⟩ := valueUnique InternalUnpair.right parentPayload (payload.relabel j)
    (Fin.cons (raw.relabel j) Fin.elim0) (pairRight _ _ _ hpacked) hp'
  obtain ⟨hlt⟩ := bodyPayloadStrict parentPayload middle domain bp htag hmiddle
  have hbody := belowPayloadApply (targetValidator data) (OriginalTypedDecoder.target H G)
    (payload.relabel j) bp child childParam hind' ⟨orderRight bp he hlt⟩
    (childPayloadValue child codomain bp hchild)
  exact targetLambdaStep data H G (raw.relabel j) typ parentPayload middle domain bp requestedDomain codomain
    (parameter.relabel j) c gamma extended child childParam
    hpacked htag hmiddle harrow hparam hext hchild hchildParam hbody

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaInductionProof
