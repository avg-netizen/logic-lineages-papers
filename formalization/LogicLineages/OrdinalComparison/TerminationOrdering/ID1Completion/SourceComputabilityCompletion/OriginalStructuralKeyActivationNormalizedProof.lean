module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationNormalizedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepPairRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBottomShapeProof (bottomTag)
open OriginalTransparentLambdaValidityInternalNormalizationSupportProof
open OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
open OriginalTransparentDecoderValidatorCollapseNormalizedProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/- These are acceptance-level NORMALIZED CALLBACK suppliers, not full
validator equivalence or structural traversal preservation. In particular
no separate source equality between q and its variable refinement is used. -/

theorem normalizedSourceAtCoordinates (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hz : Nonempty (Derivation body Gamma (StepPair contextOnly c z))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (transparent p H G W).base).oldSource
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter))) := by
  let B := BottomRepresentative.bottomGraph (numeral 1) packed
  have hb : Nonempty (Derivation body (B :: Gamma) B) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hslice⟩ := sourceBottomAt H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
    packed parameter contextOnly typ raw c gamma z
    (addAssumption hp B) (addAssumption hc B) (addAssumption hz B) (bottomTag packed hb)
  exact normalizationAtCoordinates (transparent p H G W).base.oldSource
    (numeral 1) packed parameter c gamma contextOnly hc hz
    ⟨Derivation.implicationIntroduction hslice⟩

theorem normalizedSourceAt (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (transparent p H G W).base).oldSource
        (numeral 1) raw parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) raw parameter))) := by
  apply packedCases raw parameter _
  intro beta j Theta typ payload c gamma hj hp hc
  simp only [iffRename, graph2Rename, numeralRename]
  apply programCases InternalPairing.pairing (Fin.cons c (Fin.cons z Fin.elim0)) _
  intro beta' k Xi contextOnly hk hz
  have hp' := renameInto hp k Xi hk
  have hc' := renameInto hc k Xi hk
  simp only [stepPairRename] at hp' hc'
  simp only [consTermRename, emptyRename, zRelabel] at hz
  simp only [iffRename, graph2Rename, numeralRename]
  exact normalizedSourceAtCoordinates p H G W
    ((raw.relabel j).relabel k) ((parameter.relabel j).relabel k)
    (typ.relabel k) (payload.relabel k) (c.relabel k) (gamma.relabel k) contextOnly hp' hc' hz

theorem normalizedTargetAtCoordinates (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hz : Nonempty (Derivation body Gamma (StepPair contextOnly c z))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (transparent p H G W).base).oldTarget
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter))) := by
  let B := BottomRepresentative.bottomGraph (numeral 1) packed
  have hb : Nonempty (Derivation body (B :: Gamma) B) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hslice⟩ := targetBottomAt H G
    packed parameter contextOnly typ raw c gamma z
    (addAssumption hp B) (addAssumption hc B) (addAssumption hz B) (bottomTag packed hb)
  exact normalizationAtCoordinates (transparent p H G W).base.oldTarget
    (numeral 1) packed parameter c gamma contextOnly hc hz
    ⟨Derivation.implicationIntroduction hslice⟩

theorem normalizedTargetAt (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (transparent p H G W).base).oldTarget
        (numeral 1) raw parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) raw parameter))) := by
  apply packedCases raw parameter _
  intro beta j Theta typ payload c gamma hj hp hc
  simp only [iffRename, graph2Rename, numeralRename]
  apply programCases InternalPairing.pairing (Fin.cons c (Fin.cons z Fin.elim0)) _
  intro beta' k Xi contextOnly hk hz
  have hp' := renameInto hp k Xi hk
  have hc' := renameInto hc k Xi hk
  simp only [stepPairRename] at hp' hc'
  simp only [consTermRename, emptyRename, zRelabel] at hz
  simp only [iffRename, graph2Rename, numeralRename]
  exact normalizedTargetAtCoordinates p H G W
    ((raw.relabel j).relabel k) ((parameter.relabel j).relabel k)
    (typ.relabel k) (payload.relabel k) (c.relabel k) (gamma.relabel k) contextOnly hp' hc' hz

/-- The invariant preserved by variable refinement is the COUPLED callback.
Both sides refer to the same actual parameter. This is not source equality. -/
theorem normalizedCoupledRefinement (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (transparent p H G W).base).oldSource
          (numeral 1) raw parameter ⊓
        graph2 (OriginalHereditaryValidity.normalizedData (transparent p H G W).base).oldTarget
          (numeral 1) raw parameter).iff
       (graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
          (numeral 1) raw parameter ⊓
        graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
          (numeral 1) raw parameter))) :=
  iffCompose
    (iffCompose (andIff (normalizedSourceAt p H G W raw parameter)
      (normalizedTargetAt p H G W raw parameter))
      (sourceConjunctionAt p H G W raw parameter))
    (iffReverse (OriginalTransparentDecoderValidatorCollapseNormalizedProof.normalizedCoupledAt
      p H G W raw parameter))

/-- At OTHER tags, the entire actual source validator immediately exposes
that coupled callback, so no recursive-validator extensionality is needed. -/
theorem sourceValidatorOther (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma
      (OriginalTransparentLambdaValidityInternal.TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma
      (OriginalTransparentLambdaValidityInternal.TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalTransparentLambdaValidity.sourceValidator (transparent p H G W).base)
        (numeral 1) raw parameter).iff
       (graph2 (OriginalTransparentLambdaValidity.sourceValidator (refined p H G W).base)
        (numeral 1) raw parameter))) :=
  iffCompose (OriginalFinalOtherValidityLocalProof.sourceAcceptance
    (transparent p H G W).base raw parameter h2 h1)
    (iffCompose (normalizedCoupledRefinement p H G W raw parameter)
      (iffReverse (OriginalFinalOtherValidityLocalProof.sourceAcceptance
        (refined p H G W).base raw parameter h2 h1)))

/-- The unrefined transparent validator agrees with its original guarded
source leaf at every opaque tag. The G guard is retained on both sides. -/
theorem sourceLeafEquality (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma
      (OriginalTransparentLambdaValidityInternal.TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma
      (OriginalTransparentLambdaValidityInternal.TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalTransparentLambdaValidity.sourceValidator (transparent p H G W).base)
        (numeral 1) raw parameter).iff
       (graph2 (transparent p H G W).base.oldSource (numeral 1) raw parameter))) :=
  iffCompose (OriginalFinalOtherValidityLocalProof.sourceAcceptance
    (transparent p H G W).base raw parameter h2 h1)
    (iffCompose (andIff (normalizedSourceAt p H G W raw parameter)
      (normalizedTargetAt p H G W raw parameter))
      (sourceConjunctionAt p H G W raw parameter))

theorem targetLeafEquality (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma
      (OriginalTransparentLambdaValidityInternal.TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma
      (OriginalTransparentLambdaValidityInternal.TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalTransparentLambdaValidity.targetValidator (transparent p H G W).base)
        (numeral 1) raw parameter).iff
       (graph2 (transparent p H G W).base.oldTarget (numeral 1) raw parameter))) :=
  iffCompose (OriginalFinalOtherValidityLocalProof.targetAcceptance
    (transparent p H G W).base raw parameter h2 h1)
    (normalizedTargetAt p H G W raw parameter)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationNormalizedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationNormalizedProof
