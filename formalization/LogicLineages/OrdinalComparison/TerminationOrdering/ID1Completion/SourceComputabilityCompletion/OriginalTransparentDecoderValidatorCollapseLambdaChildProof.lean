module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight oneRename)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalListProof
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalExtensionProof
open OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The original initial state and the literal packed coordinates supply the
ACTUAL repacked body and the ACTUAL context-preserving child parameter. -/
theorem initialLambdaSelectors
    (packed typ payload middle domain bodyPayload requestedDomain codomain
      parameter c gamma extended child childParam state : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hparam : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
    (hext : Nonempty (Derivation body Delta (StepCons extended domain gamma)))
    (hchild : Nonempty (Derivation body Delta (StepPair child codomain bodyPayload)))
    (hchildParam : Nonempty (Derivation body Delta (StepPair childParam c extended)))
    (hi : Nonempty (Derivation body Delta (graph2 initial state packed parameter))) :
    Nonempty (Derivation body Delta
      (graph1 currentBody child state ⊓
        (graph1 childParameter childParam state ⊓ ExtendedParameter packed parameter childParam))) := by
  have hsel := initialSelectors state packed parameter hi
  have hr := andLeft hsel
  have hpar := andRight hsel
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hd := rawDomainValue packed typ payload middle domain bodyPayload hp ht hm
  have hb := rawBodyPayloadValue packed typ payload middle domain bodyPayload hp ht hm
  have htype := unaryValue InternalUnpair.left currentRaw typ packed xs
    (pairLeft packed typ payload hp) hr
  have hcod := unaryValue InternalListCodec.tailCode currentType codomain typ xs
    (listTail typ requestedDomain codomain hf) htype
  let bx : Fin 2 → OTerm alpha := Fin.cons codomain (Fin.cons packed Fin.elim0)
  have hbpay := unaryValue OriginalLambdaConstructor.bodyPayload (.projection 1)
    bodyPayload packed bx hb (projectionValue 1 bx)
  have hbodyCode : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaConstructor.bodyCode child codomain packed)) :=
    binaryValue InternalPairing.pairing (.projection 0)
      (.composition OriginalLambdaConstructor.bodyPayload (fun _ : Fin 1 => .projection 1))
      child codomain bodyPayload bx hchild (projectionValue 0 bx) hbpay
  have hbody : Nonempty (Derivation body Delta (graph1 currentBody child state)) :=
    binaryValue OriginalLambdaConstructor.bodyCode currentCodomain currentRaw
      child codomain packed xs hbodyCode hcod hr
  have hdomain := unaryValue OriginalLambdaConstructor.domain currentRaw domain packed xs hd hr
  have hcontext := pairLeftValue currentParameter parameter c gamma xs hpar hparam
  have hgamma := pairRightValue currentParameter parameter c gamma xs hpar hparam
  have hextended := binaryValue InternalListCodec.consCode currentDomain (rightOf currentParameter)
    extended domain gamma xs hext hdomain hgamma
  have hcp : Nonempty (Derivation body Delta (graph1 childParameter childParam state)) :=
    binaryValue InternalPairing.pairing (leftOf currentParameter)
      (consOf currentDomain (rightOf currentParameter)) childParam c extended xs
      hchildParam hcontext hextended
  have he := extendedParameterIntro packed parameter childParam domain c gamma extended
    (andIntro hd (andIntro hparam (andIntro hext hchildParam)))
  exact andIntro hbody (andIntro hcp he)

theorem rootLambdaSelected_iff (s t m : Program 2)
    (packed parameter state child childParam : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 initial state packed parameter)))
    (hb : Nonempty (Derivation body Delta (graph1 currentBody child state)))
    (hp : Nonempty (Derivation body Delta (graph1 childParameter childParam state)))
    (he : Nonempty (Derivation body Delta (ExtendedParameter packed parameter childParam))) :
    Nonempty (Derivation body Delta ((RootLambdaChild s t m packed parameter).iff
      (graph2 (validator s t m) (numeral 1) child childParam))) := by
  let P := RootLambdaChild s t m packed parameter
  let Q := graph2 (validator s t m) (numeral 1) child childParam
  obtain ⟨hi⟩ := hi
  obtain ⟨hb⟩ := hb
  obtain ⟨hp⟩ := hp
  obtain ⟨he⟩ := he
  obtain ⟨hforward⟩ := rootLambdaAt s t m packed parameter state child childParam
    ⟨InternalBetaTotalityProof.addHyp hi P⟩ ⟨InternalBetaTotalityProof.addHyp hb P⟩
    ⟨InternalBetaTotalityProof.addHyp hp P⟩
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hbackward⟩ := rootLambdaIntro s t m packed parameter state child childParam
    (andIntro (show Nonempty (Derivation body (Q :: Delta) (graph2 initial state packed parameter)) from
        ⟨InternalBetaTotalityProof.addHyp hi Q⟩)
      (andIntro (andIntro ⟨InternalBetaTotalityProof.addHyp hb Q⟩ ⟨InternalBetaTotalityProof.addHyp he Q⟩)
        (andIntro ⟨InternalBetaTotalityProof.addHyp hp Q⟩
          (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩))))
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hforward)
    (Derivation.implicationIntroduction hbackward)⟩

/-- All initial/selector/extension witnesses are internal; this iff has no
body-success premise and uses the identical arbitrary three callbacks. -/
theorem rootLambdaChild_iff (s t m : Program 2)
    (packed typ payload middle domain bodyPayload requestedDomain codomain
      parameter c gamma extended child childParam : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hparam : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
    (hext : Nonempty (Derivation body Delta (StepCons extended domain gamma)))
    (hchild : Nonempty (Derivation body Delta (StepPair child codomain bodyPayload)))
    (hchildParam : Nonempty (Derivation body Delta (StepPair childParam c extended))) :
    Nonempty (Derivation body Delta ((RootLambdaChild s t m packed parameter).iff
      (graph2 (validator s t m) (numeral 1) child childParam))) := by
  apply programCases initial (Fin.cons packed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta state hj hi
  change Nonempty (Derivation body Theta
    (((RootLambdaChild s t m packed parameter).relabel j).iff
      ((graph2 (validator s t m) (numeral 1) child childParam).relabel j)))
  simp only [rootLambdaRename,graph2Rename,oneRename]
  simp only [consTermRename,emptyRename] at hi
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  have hm' := renameInto hm j Theta hj
  have hf' := renameInto hf j Theta hj
  have hparam' := renameInto hparam j Theta hj
  have hext' := renameInto hext j Theta hj
  have hchild' := renameInto hchild j Theta hj
  have hchildParam' := renameInto hchildParam j Theta hj
  simp only [stepPairRename,stepConsRename,stepArrowFieldsRename,oneRename]
    at hp' ht' hm' hf' hparam' hext' hchild' hchildParam'
  have hsel := initialLambdaSelectors (packed.relabel j) (typ.relabel j) (payload.relabel j)
    (middle.relabel j) (domain.relabel j) (bodyPayload.relabel j) (requestedDomain.relabel j)
    (codomain.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
    (extended.relabel j) (child.relabel j) (childParam.relabel j) state
    hp' ht' hm' hf' hparam' hext' hchild' hchildParam' hi
  exact rootLambdaSelected_iff s t m (packed.relabel j) (parameter.relabel j) state
    (child.relabel j) (childParam.relabel j) hi (andLeft hsel)
    (andLeft (andRight hsel)) (andRight (andRight hsel))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaChildProof
