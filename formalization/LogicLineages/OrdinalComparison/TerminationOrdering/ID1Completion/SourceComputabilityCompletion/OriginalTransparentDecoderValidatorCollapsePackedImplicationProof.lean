module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderValidatorCollapseInclusionProof (termSourceToTarget)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Independent internal inclusion of the original packed leaves at the SAME
original context and Gamma. It drops only source checks, without calibration. -/
theorem sourceToTarget (H G : Program 1) (M W : Program 2)
    (packed parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter)) := by
  apply packedCases packed parameter _
  intro beta j Theta typ raw c gamma hj hp hc
  simp only [graph2Rename,numeralRename]
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  have hf := sourceFieldsElim H G M W (packed.relabel j) (parameter.relabel j)
    typ raw c gamma hp hc ha'
  exact targetFieldsIntro H G (packed.relabel j) (parameter.relabel j)
    typ raw c gamma hp hc (andLeft hf)
    (termSourceToTarget H M W typ raw gamma c (andRight hf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
