module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportContextProof
open OriginalTypedDecoderTransportBinaryProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationTag (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw _ ht
  intro beta j Theta domain fn arg hj hc
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact applicationBranch H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) domain fn arg hind' hc hi' ho' ha'

theorem numberedTag (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw _ ht
  intro beta j Theta label head recorded base types extras hj hc
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact numberedBranch H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) label head recorded base types extras hind' hc hi' ho' ha'

theorem consTag (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H true typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H true typ out (targetContext erasing gamma extended))) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ ht
  intro beta j Theta domain head tail hj hc
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact consBranch H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) domain head tail hind' hc hi' ho' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryTagsProof
