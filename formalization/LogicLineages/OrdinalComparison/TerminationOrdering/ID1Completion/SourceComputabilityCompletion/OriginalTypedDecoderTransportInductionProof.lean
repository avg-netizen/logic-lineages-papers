module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportKnownProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportIntroductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportContextProof OriginalTypedDecoderTransportKnownProof
open OriginalTypedDecoderTransportTagSupportProof
open OriginalTypedDecoderTransportBindingProof OriginalTypedDecoderTransportIntroductionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The exhaustive raw constructor step uses only the already proved original
checker recurrences. Every accepting child is recovered from the parent,
then paid by the smaller-original-raw induction hypothesis. -/
theorem transportStep (H : Program 1) (erasing arguments : Bool)
    (raw out d cutoff gamma extended typ : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H arguments typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H arguments typ out (targetContext erasing gamma extended))) := by
  apply rawTagCases raw
  · intro beta j Theta i payload hj ht hp
    simp only [acceptedRename,targetContextRename]
    have hind' := renameInto hind j Theta hj
    have hi' := renameInto hi j Theta hj
    have ho' := renameInto ho j Theta hj
    have ha' := renameInto ha j Theta hj
    rw [belowRawRename] at hind'
    rw [insertRename] at hi'
    rw [graph3Rename] at ho'
    simp only [acceptedRename,sourceContextRename] at ha'
    cases arguments
    · exact termKnown H erasing i (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
        (gamma.relabel j) (extended.relabel j) (typ.relabel j) payload hind' hi' ho' ha' ht hp
    · exact argumentsKnown H erasing i (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
        (gamma.relabel j) (extended.relabel j) (typ.relabel j) payload hind' hi' ho' ha' ht hp
  · intro beta j Theta tag payload hj hp hu
    simp only [acceptedRename,targetContextRename]
    have ha' := renameInto ha j Theta hj
    simp only [acceptedRename,sourceContextRename] at ha'
    exact OriginalTypedDecoderTransportRejectedProof.unknown H arguments (raw.relabel j) tag payload
      (typ.relabel j) (sourceContext erasing (gamma.relabel j) (extended.relabel j)) _ hp hu ha'

/-- Complete independent INTERNAL induction over every arithmetic raw code,
for both original term/argument modes and arbitrary local H. No transformed
raw bound, native calibration, type window or successful child is assumed. -/
theorem allRawTransport (H : Program 1) (erasing : Bool) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H erasing raw)) := by
  apply rawInduction H erasing raw
  intro beta Theta r hind
  apply atRawIntroFrom H erasing r
  intro gamma j Xi arguments d cutoff context extended typ transformed hj hi ho ha
  have hind' := renameInto hind j Xi hj
  rw [belowRawRename] at hind'
  exact transportStep H erasing arguments (r.relabel j) transformed d cutoff context extended typ hind' hi ho ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInductionProof
