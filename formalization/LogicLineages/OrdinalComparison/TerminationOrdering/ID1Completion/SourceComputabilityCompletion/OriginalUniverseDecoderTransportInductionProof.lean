module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportIntroductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalRawSyntaxTransport
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalTypedDecoderTransportContextProof OriginalUniverseDecoderTransportKnownProof
open OriginalTypedDecoderTransportTagSupportProof
open OriginalUniverseDecoderTransportBindingProof OriginalUniverseDecoderTransportIntroductionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The exhaustive raw constructor step uses only the already proved original
checker recurrences. Every accepting child is recovered from the parent,
then paid by the smaller-original-raw induction hypothesis. -/
theorem transportStep (H : Program 1) (M W : Program 2) (erasing arguments : Bool)
    (raw out d cutoff gamma extended typ c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W arguments typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta (Accepted H M W arguments typ out (targetContext erasing gamma extended) c)) := by
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
    · exact termKnown H M W erasing i (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
        (gamma.relabel j) (extended.relabel j) (typ.relabel j) payload (c.relabel j) hind' hi' ho' ha' ht hp
    · exact argumentsKnown H M W erasing i (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
        (gamma.relabel j) (extended.relabel j) (typ.relabel j) payload (c.relabel j) hind' hi' ho' ha' ht hp
  · intro beta j Theta tag payload hj hp hu
    simp only [acceptedRename,targetContextRename]
    have ha' := renameInto ha j Theta hj
    simp only [acceptedRename,sourceContextRename] at ha'
    exact OriginalUniverseDecoderTransportRejectedProof.unknown H M W arguments (raw.relabel j) tag payload
      (typ.relabel j) (sourceContext erasing (gamma.relabel j) (extended.relabel j)) (c.relabel j) _ hp hu ha'

/-- Complete independent INTERNAL induction over every arithmetic raw code,
for both original term/argument modes and arbitrary local H M W. No transformed
raw bound, native calibration, type window or successful child is assumed. -/
theorem allRawTransport (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H M W erasing raw)) := by
  apply rawInduction H M W erasing raw
  intro beta Theta r hind
  apply atRawIntroFrom H M W erasing r
  intro gamma j Xi arguments d cutoff context extended typ transformed c hj hi ho ha
  have hind' := renameInto hind j Xi hj
  rw [belowRawRename] at hind'
  exact transportStep H M W erasing arguments (r.relabel j) transformed d cutoff context extended typ c hind' hi ho ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInductionProof
