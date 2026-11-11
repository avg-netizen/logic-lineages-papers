module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceApplicationInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalSquareRootArithmeticSupportProof
open InternalControlGraphChoiceProof (excludedMiddle)
open InternalBetaTotalityProof (disjunctionElimination)
open OriginalTransparentDecoderValidatorCollapse OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
open OriginalTransparentDecoderValidatorCollapseInductionBindingProof
open OriginalTransparentDecoderValidatorCollapseInductionProof
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
open OriginalTransparentDecoderValidatorCollapseSourceApplicationInductionProof
open OriginalTransparentDecoderValidatorCollapseSourceLambdaProof
open OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
open OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The lambda body is compared at its own strictly smaller original raw
payload, retaining the actual extended parameter and arbitrary outer type. -/
theorem lambdaByInduction (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (payload raw parameter : OTerm alpha)
    (hind : Nonempty (Derivation body Gamma
      (belowPayload (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource payload)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource raw parameter)) := by
  apply lambdaCoordinatesCases raw parameter _ ht
  intro beta j Delta typ actualPayload middle domain bodyPayload requestedDomain codomain c gamma extended child childParam
    hj hpacked htag hmiddle hfields hparameter hext hchild hchildParam
  rw [acceptanceRename]
  have hind' := renameInto hind j Delta hj
  rw [belowPayloadRename] at hind'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  obtain ⟨he⟩ := valueUnique InternalUnpair.right actualPayload (payload.relabel j)
    (Fin.cons (raw.relabel j) Fin.elim0) (pairRight (raw.relabel j) typ actualPayload hpacked) hp'
  obtain ⟨hlt⟩ := bodyPayloadStrict actualPayload middle domain bodyPayload htag hmiddle
  have hi := belowPayloadApply (sourceValidator (refined p H G W).base)
    (transparent p H G W).base.oldSource (payload.relabel j) bodyPayload child childParam
    hind' ⟨orderRight bodyPayload he hlt⟩ (childPayloadValue child codomain bodyPayload hchild)
  exact sourceLambdaStep p H G W (raw.relabel j) typ actualPayload middle domain bodyPayload
    requestedDomain codomain (parameter.relabel j) c gamma extended child childParam
    hpacked htag hmiddle hfields hparameter hext hchild hchildParam hi

/-- The three exhaustive raw cases are the existing application expansion,
lambda expansion, and opaque pop branch of the original framed machine. -/
theorem sourceStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (payload raw parameter : OTerm alpha)
    (hind : Nonempty (Derivation body Gamma
      (belowPayload (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource payload)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource raw parameter)) := by
  let A := TagIs 2 raw
  let B := TagIs 1 raw
  let C := Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource raw parameter
  have hy : Nonempty (Derivation body (A :: Gamma) C) :=
    applicationByInduction p H G W payload raw parameter (addAssumption hind A) (addAssumption hp A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hn : Nonempty (Derivation body (A.not :: Gamma) C) := by
    have hyes : Nonempty (Derivation body (B :: A.not :: Gamma) C) :=
      lambdaByInduction p H G W payload raw parameter
        (addAssumption (addAssumption hind A.not) B) (addAssumption (addAssumption hp A.not) B)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hno : Nonempty (Derivation body (B.not :: A.not :: Gamma) C) :=
      sourceLeafEquality p H G W raw parameter
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hyes⟩ := hyes
    obtain ⟨hno⟩ := hno
    exact ⟨disjunctionElimination (excludedMiddle B)
      (Derivation.implicationIntroduction hyes) (Derivation.implicationIntroduction hno)⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle A)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Independent all-raw HS acceptance collapse. The proof uses arithmetic
strong induction, not native calibration or semantic-to-internal reflection. -/
theorem sourceAcceptance (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource raw parameter)) :=
  acceptanceInduction (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource
    (fun _ _ payload raw parameter hind hp => sourceStep p H G W payload raw parameter hind hp)
    raw parameter
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceInductionProof
