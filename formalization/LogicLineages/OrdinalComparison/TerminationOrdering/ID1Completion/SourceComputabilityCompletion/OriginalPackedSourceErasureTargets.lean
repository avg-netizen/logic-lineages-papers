module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Erasure of the ORIGINAL packed source at arbitrary literal insertion.
Both parameter graphs retain the SAME outer context; no source validity is
inferred from a certificate, and no type, membership or window oracle is added.
The internal payload/type/erased-payload witnesses are not caller premises. -/
def ActualOriginalPackedSourceErasure : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (H G : Program 1) (M W : Program 2)
   (packed out d cutoff gamma extended c oldParam newParam : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw out d cutoff packed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam c extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed oldParam)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) out newParam))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
