module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedVariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open InternalTagArithmeticSyntaxProof (z)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepPairRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableConstructorValue)
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
open OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The target's guard is the missing source-variable factor. Both copies of
the SAME variable decoder are retained until this propositional contraction. -/
theorem coupledFactors (M V G : Formula alpha) :
    Nonempty (Derivation body Gamma (((M ⊓ V) ⊓ (G ⊓ V)).iff (G ⊓ (M ⊓ V)))) := by
  let A := (M ⊓ V) ⊓ (G ⊓ V)
  let B := G ⊓ (M ⊓ V)
  have ha : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body (B :: Gamma) B := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft (Derivation.conjunctionRight ha)) (Derivation.conjunctionLeft ha)))
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.conjunctionRight hb) (Derivation.conjunctionIntroduction
        (Derivation.conjunctionLeft hb) (Derivation.conjunctionRight (Derivation.conjunctionRight hb)))))⟩

theorem targetVariableFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma index : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hv : Nonempty (Derivation body Gamma (StepPair raw z index))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter))) := by
  have hn := booleanAcceptance
    (OriginalFinalVariableWeakeningLeafProof.targetLeafEquation G (transparent p H G W).base
      (numeral 1) packed raw typ index parameter c gamma (variableConstructorValue raw index hv) hp hc)
  have hq := iffCompose (targetEquation H G packed parameter typ raw c gamma hp hc)
    (andIff (iffSelf _) (OriginalTypedDecoderInternalAcceptanceLeafProof.variableIff H raw index typ gamma hv))
  exact iffCompose hn (iffReverse hq)

/-- Source alone cannot recover G. The coupled normalized source/target leaf
recovers precisely the original transparent guarded source at unchanged c. -/
theorem coupledVariableFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma index : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hv : Nonempty (Derivation body Gamma (StepPair raw z index))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
          (numeral 1) packed parameter ⊓
        graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
          (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter))) := by
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  have hctor := variableConstructorValue raw index hv
  have hs := booleanAcceptance
    (OriginalFinalVariableWeakeningLeafProof.sourceLeafEquation G (transparent p H G W).base
      (numeral 1) packed raw typ index parameter c gamma hctor hp hc)
  have ht := booleanAcceptance
    (OriginalFinalVariableWeakeningLeafProof.targetLeafEquation G (transparent p H G W).base
      (numeral 1) packed raw typ index parameter c gamma hctor hp hc)
  have hq := iffCompose (sourceEquation H G M W packed parameter typ raw c gamma hp hc)
    (andIff (iffSelf _) (OriginalUniverseDecoderInternalAcceptanceLeafProof.variableIff
      H M W raw index typ gamma c hv))
  exact iffCompose (andIff hs ht)
    (iffCompose (coupledFactors (graph2 M (numeral 1) typ c)
      (OriginalVariableDecoder.graph (numeral 1) typ index gamma) (graph1 G (numeral 1) c))
      (iffReverse hq))

theorem targetVariableAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (ht : Nonempty (Derivation body Gamma (TagIs 0 packed))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter))) := by
  apply tagPayloadCases 0 packed typ raw _ hp ht
  intro beta j Theta index hj hv
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  simp only [stepPairRename] at hp' hc'
  simp only [iffRename,conjunctionRename,graph2Rename,numeralRename]
  exact targetVariableFields p H G W (packed.relabel j) (parameter.relabel j)
    (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) index hp' hc' hv

theorem coupledVariableAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (ht : Nonempty (Derivation body Gamma (TagIs 0 packed))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
          (numeral 1) packed parameter ⊓
        graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
          (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter))) := by
  apply tagPayloadCases 0 packed typ raw _ hp ht
  intro beta j Theta index hj hv
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  simp only [stepPairRename] at hp' hc'
  simp only [iffRename,conjunctionRename,graph2Rename,numeralRename]
  exact coupledVariableFields p H G W (packed.relabel j) (parameter.relabel j)
    (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) index hp' hc' hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedVariableProof
