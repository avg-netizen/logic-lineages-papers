module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open OriginalLambdaConstructor OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalTypedDecoderInternalListProof (consArrowFields)
open OriginalTypedDecoderTransportLogicalProof (iffForward)

theorem fieldsIff (H G : Program 1) (M W : Program 2)
    (out parameter b d e arrowCode c gamma extended childParam : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (Fields out d e b arrowCode)))
    (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam c extended))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) out parameter).iff
       ((graph2 M (numeral 1) arrowCode c ⊓
         (graph2 M (numeral 1) d c ⊓ ((equal arrowCode (numeral 0)).not ⊓ equal d d))) ⊓
        graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) b childParam))) := by
  apply OriginalPackedSourceLambdaChildProof.rawCoordinates out b d e arrowCode _ hf
  intro beta j Theta node inner payload hj ho hn hi hb
  simp only [OriginalTransparentLambdaStepInternalProof.iffRename,conjunctionRename,graph2Rename,oneRename,
   OriginalTypedDecoderInternalAcceptanceUnaryProof.notRename,OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename]
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  have hparam' := renameInto hparam j Theta hj
  have hext' := renameInto hext j Theta hj
  have hcp' := renameInto hcp j Theta hj
  simp only [graph2Rename,oneRename] at hparam' hext' hcp'
  have harrow := consArrowFields (arrowCode.relabel j) (d.relabel j) (e.relabel j)
    (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf')))
  have law := OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof.sourceLambdaCoordinatesIff
    H G M W (out.relabel j) (parameter.relabel j) (arrowCode.relabel j) node inner
    (d.relabel j) payload (d.relabel j) (e.relabel j) (b.relabel j)
    (c.relabel j) (gamma.relabel j) (extended.relabel j) (childParam.relabel j)
    ho hn hi harrow hb hparam' hext' hcp'
  exact law

theorem rebuild (H G : Program 1) (M W : Program 2)
 (s t parameter oldChild newChild d e arrow c gamma extended childParam : OTerm alpha)
 (hfs : Nonempty (Derivation body Delta (Fields s d e oldChild arrow)))
 (hft : Nonempty (Derivation body Delta (Fields t d e newChild arrow)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) newChild childParam)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam c extended))) :
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)) := by
 have a := iffForward (fieldsIff H G M W s parameter oldChild d e arrow c gamma extended childParam hfs hp he hcp) hs
 have b := fieldsIff H G M W t parameter newChild d e arrow c gamma extended childParam hft hp he hcp
 obtain ⟨hb⟩ := InternalApplicationStepPeelSupportProof.andRight b
 obtain ⟨ha⟩ := InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft a) ht
 exact ⟨Derivation.implicationElimination hb ha⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaSourceProof
