module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepPairRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBottomShapeProof (bottomTag tagNotAtThree)
open OriginalTransparentLambdaValidityInternalNormalizationSupportProof
open OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- A known original tag and the actual inner right selector reconstruct the
original untyped term pair; no decoder or syntactic well-formedness is used. -/
theorem rawTagPair (packed typ raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag packed)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Gamma (StepPair raw tag payload)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons packed Fin.elim0
  have hraw := unaryValue InternalUnpair.right (.projection 0) raw packed xs
    (pairRight packed typ raw hp) (projectionValue 0 xs)
  exact reconstructPair raw tag payload
    (unaryRecover InternalUnpair.left (rightOf (.projection 0)) tag raw xs ht hraw) hr

/-- Totality supplies the original payload, preserving every ambient assumption. -/
theorem tagPayloadCases (k : Nat) (packed typ raw : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (ht : Nonempty (Derivation body Gamma (TagIs k packed)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (payload : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepPair (raw.relabel j) (numeral k) payload)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
  intro beta j Theta payload hj hr
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [stepPairRename] at hp'
  simp only [TagIs,graph1Rename,numeralRename] at ht'
  simp only [consTermRename,emptyRename] at hr
  exact step beta j Theta payload hj
    (rawTagPair (packed.relabel j) (typ.relabel j) (raw.relabel j) (numeral k) payload hp' ht' hr)

/-- The original bottom recurrence has no Gamma dependence, even when its
inner type fails to match. G remains at the SAME original outer context. -/
theorem targetBottomAt (H G : Program 1)
    (packed parameter other typ raw c gamma otherGamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (ho : Nonempty (Derivation body Gamma (StepPair other c otherGamma)))
    (ht : Nonempty (Derivation body Gamma (TagIs 3 packed))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter).iff
        (graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed other))) := by
  apply tagPayloadCases 3 packed typ raw _ hp ht
  intro beta j Theta payload hj hr
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [stepPairRename] at hp' hc' ho'
  simp only [iffRename,conjunctionRename,graph2Rename,numeralRename]
  exact iffCompose
    (iffCompose (targetEquation H G (packed.relabel j) (parameter.relabel j)
      (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) hp' hc')
      (andIff (iffSelf _) (OriginalTypedDecoderInternalAcceptanceLeafProof.bottomIff
        H (raw.relabel j) payload (typ.relabel j) (gamma.relabel j) hr)))
    (iffReverse (iffCompose (targetEquation H G (packed.relabel j) (other.relabel j)
      (typ.relabel j) (raw.relabel j) (c.relabel j) (otherGamma.relabel j) hp' ho')
      (andIff (iffSelf _) (OriginalTypedDecoderInternalAcceptanceLeafProof.bottomIff
        H (raw.relabel j) payload (typ.relabel j) (otherGamma.relabel j) hr))))

/-- Source bottom retains both SAME-context G and M; only its Gamma varies. -/
theorem sourceBottomAt (H G : Program 1) (M W : Program 2)
    (packed parameter other typ raw c gamma otherGamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (ho : Nonempty (Derivation body Gamma (StepPair other c otherGamma)))
    (ht : Nonempty (Derivation body Gamma (TagIs 3 packed))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter).iff
        (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed other))) := by
  apply tagPayloadCases 3 packed typ raw _ hp ht
  intro beta j Theta payload hj hr
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [stepPairRename] at hp' hc' ho'
  simp only [iffRename,conjunctionRename,graph2Rename,numeralRename]
  exact iffCompose
    (iffCompose (sourceEquation H G M W (packed.relabel j) (parameter.relabel j)
      (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) hp' hc')
      (andIff (iffSelf _) (OriginalUniverseDecoderInternalAcceptanceLeafProof.bottomIff
        H M W (raw.relabel j) payload (typ.relabel j) (gamma.relabel j) (c.relabel j) hr)))
    (iffReverse (iffCompose (sourceEquation H G M W (packed.relabel j) (other.relabel j)
      (typ.relabel j) (raw.relabel j) (c.relabel j) (otherGamma.relabel j) hp' ho')
      (andIff (iffSelf _) (OriginalUniverseDecoderInternalAcceptanceLeafProof.bottomIff
        H M W (raw.relabel j) payload (typ.relabel j) (otherGamma.relabel j) (c.relabel j) hr))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
