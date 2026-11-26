module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Forward acceptance under the actual packed shift, at an arbitrary valid
insertion cutoff. Both parameters are literal original pairs with the SAME
outer context c. No transformed bound, membership or canonicality is assumed. -/
def PackedWeakening (validator : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d cutoff gamma extended c parameter extendedParameter packed shifted : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Insert d cutoff gamma extended ⊓
      (graph2 InternalPairing.pairing parameter c gamma ⊓
        (graph2 InternalPairing.pairing extendedParameter c extended ⊓
          (graph2 shiftPackedRaw shifted cutoff packed ⊓
            graph2 validator (numeral 1) packed parameter)))).imp
      (graph2 validator (numeral 1) shifted extendedParameter)))

/-- Guarded forward erasure at the SAME valid insertion. Original acceptance
is in the extended context; the result uses the original context. Neither
an erased-type window nor an independent transformed-code bound is required. -/
def PackedErasure (validator : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d cutoff gamma extended c parameter extendedParameter packed erased : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Insert d cutoff gamma extended ⊓
      (graph2 InternalPairing.pairing parameter c gamma ⊓
        (graph2 InternalPairing.pairing extendedParameter c extended ⊓
          (graph3 erasePackedRaw erased d cutoff packed ⊓
            graph2 validator (numeral 1) packed extendedParameter)))).imp
      (graph2 validator (numeral 1) erased parameter)))

/- These are actual final validity graph laws, not selectedTyped transport,
canonical fixedness, rank, I or C. Rejection equivalence is not asserted. The
final data are selected exactly once and remain unchanged at both endpoints. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransport
