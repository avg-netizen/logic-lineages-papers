module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight oneRename)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalListProof
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalTransparentLambdaValidityInternal OriginalTransparentLambdaValidityInternalShapeSyntaxProof
open OriginalTransparentLambdaValidityInternalSourceSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The two source memberships refer to the same actual packed selectors;
shape is kept as its original internal formula, not assumed externally. -/
theorem sourceFactorsForward (data : Data) (packed parameter typ domain : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ packed)))
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.domain domain packed)))
    (hs : Nonempty (Derivation body Delta (SourceLambdaRootFactors data packed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 data.member (numeral 1) typ parameter ⊓
        (graph2 data.member (numeral 1) domain parameter ⊓ LambdaShape packed))) := by
  apply sourceCases data packed parameter _ hs
  intro beta j Theta actualType actualDomain actualCodomain hj hf
  simp only [conjunctionRename,graph2Rename,oneRename,shapeRename]
  have ht' := renameInto ht j Theta hj
  have hd' := renameInto hd j Theta hj
  rw [graph1Rename] at ht' hd'
  have et := valueUnique InternalUnpair.left actualType (typ.relabel j)
    (Fin.cons (packed.relabel j) Fin.elim0) (andLeft hf) ht'
  have ed := valueUnique OriginalLambdaConstructor.domain actualDomain (domain.relabel j)
    (Fin.cons (packed.relabel j) Fin.elim0) (andLeft (andRight hf)) hd'
  have hfactors := andRight (andRight (andRight hf))
  have hmt := headTransport data.member (numeral 1) actualType (typ.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0) et (andLeft (andRight hfactors))
  have hmd := headTransport data.member (numeral 1) actualDomain (domain.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0) ed (andRight (andRight hfactors))
  have hshape := shapeIntro (packed.relabel j) actualType actualDomain actualCodomain
    (andIntro (andLeft hf) (andIntro (andLeft (andRight hf))
      (andIntro (andLeft (andRight (andRight hf))) (andLeft hfactors))))
  exact andIntro hmt (andIntro hmd hshape)

theorem sourceFactorsBackward (data : Data) (packed parameter typ domain codomain : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ packed)))
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.domain domain packed)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode codomain typ)))
    (hs : Nonempty (Derivation body Delta
      (graph2 data.member (numeral 1) typ parameter ⊓
        (graph2 data.member (numeral 1) domain parameter ⊓ LambdaShape packed)))) :
    Nonempty (Derivation body Delta (SourceLambdaRootFactors data packed parameter)) := by
  have ha := shapeArrowRecover packed typ domain codomain ht hd hc (andRight (andRight hs))
  exact sourceIntro data packed parameter typ domain codomain
    (andIntro ht (andIntro hd (andIntro hc
      (andIntro ha (andIntro (andLeft hs) (andLeft (andRight hs)))))))

theorem sourceLambdaForward (data : Data)
    (packed parameter typ payload middle domain bodyPayload requestedDomain codomain : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hs : Nonempty (Derivation body Delta (SourceLambdaRootFactors data packed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 data.member (numeral 1) typ parameter ⊓
        (graph2 data.member (numeral 1) domain parameter ⊓
          ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain)))) := by
  have factors := sourceFactorsForward data packed parameter typ domain (pairLeft packed typ payload hp)
    (rawDomainValue packed typ payload middle domain bodyPayload hp ht hm) hs
  exact andIntro (andLeft factors) (andIntro (andLeft (andRight factors))
    (lambdaShapeForward packed typ payload middle domain bodyPayload requestedDomain codomain
      hp ht hm hf (andRight (andRight factors))))

theorem sourceLambdaBackward (data : Data)
    (packed parameter typ payload middle domain bodyPayload requestedDomain codomain : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hs : Nonempty (Derivation body Delta
      (graph2 data.member (numeral 1) typ parameter ⊓
        (graph2 data.member (numeral 1) domain parameter ⊓
          ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))))) :
    Nonempty (Derivation body Delta (SourceLambdaRootFactors data packed parameter)) := by
  have hshape := lambdaShapeBackward packed typ payload middle domain bodyPayload requestedDomain codomain
    hp ht hm hf (andRight (andRight hs))
  exact sourceFactorsBackward data packed parameter typ domain codomain (pairLeft packed typ payload hp)
    (rawDomainValue packed typ payload middle domain bodyPayload hp ht hm)
    (listTail typ requestedDomain codomain hf)
    (andIntro (andLeft hs) (andIntro (andLeft (andRight hs)) hshape))

theorem sourceFactors_iff (data : Data)
    (packed parameter typ payload middle domain bodyPayload requestedDomain codomain : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Delta (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Delta (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain))) :
    Nonempty (Derivation body Delta ((SourceLambdaRootFactors data packed parameter).iff
      (graph2 data.member (numeral 1) typ parameter ⊓
        (graph2 data.member (numeral 1) domain parameter ⊓
          ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))))) := by
  let P := SourceLambdaRootFactors data packed parameter
  let Q := graph2 data.member (numeral 1) typ parameter ⊓
    (graph2 data.member (numeral 1) domain parameter ⊓
      ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))
  obtain ⟨hp⟩ := hp
  obtain ⟨ht⟩ := ht
  obtain ⟨hm⟩ := hm
  obtain ⟨hf⟩ := hf
  obtain ⟨hforward⟩ := sourceLambdaForward data packed parameter typ payload middle domain bodyPayload requestedDomain codomain
    ⟨InternalBetaTotalityProof.addHyp hp P⟩ ⟨InternalBetaTotalityProof.addHyp ht P⟩
    ⟨InternalBetaTotalityProof.addHyp hm P⟩ ⟨InternalBetaTotalityProof.addHyp hf P⟩
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hbackward⟩ := sourceLambdaBackward data packed parameter typ payload middle domain bodyPayload requestedDomain codomain
    ⟨InternalBetaTotalityProof.addHyp hp Q⟩ ⟨InternalBetaTotalityProof.addHyp ht Q⟩
    ⟨InternalBetaTotalityProof.addHyp hm Q⟩ ⟨InternalBetaTotalityProof.addHyp hf Q⟩
    (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hforward)
    (Derivation.implicationIntroduction hbackward)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaSourceProof
