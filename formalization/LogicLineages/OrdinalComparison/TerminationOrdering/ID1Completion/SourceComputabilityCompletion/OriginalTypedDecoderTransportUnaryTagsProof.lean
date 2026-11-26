module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportContextProof
open OriginalTypedDecoderTransportUnaryProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaTag (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases raw _ ht
  intro beta j Theta domain child hj hc
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact lambdaBranch H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) domain child hind' hc hi' ho' ha'

theorem ordinaryTag (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases raw _ ht
  intro beta j Theta head base hj hc
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact ordinaryBranch H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) head base hind' hc hi' ho' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryTagsProof
