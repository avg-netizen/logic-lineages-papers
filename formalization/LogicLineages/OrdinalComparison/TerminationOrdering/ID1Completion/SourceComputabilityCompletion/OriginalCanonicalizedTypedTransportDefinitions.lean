module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data selectedTyped)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalContextInsertion OriginalRawSyntaxTransport
open SourceComputabilityFormulaSupportProof (numeral)

/-- Canonicalized weakening at one unchanged Data tuple. The premise supplies
only the original typed input, actual packed shift and actual fold output.
Validity, membership and transition fixedness of that output are conclusions. -/
def PackedWeakening (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d cutoff gamma extended c parameter extendedParameter input shifted out typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Insert d cutoff gamma extended ⊓
      (graph2 InternalPairing.pairing parameter c gamma ⊓
        (graph2 InternalPairing.pairing extendedParameter c extended ⊓
          (graph2 shiftPackedRaw shifted cutoff input ⊓
            (graph3 (selectedTyped data) (numeral 1) input typ parameter ⊓
              foldGraph data out shifted extendedParameter))))).imp
      (graph3 (selectedTyped data) (numeral 1) out typ extendedParameter)))

/-- Canonicalized erasure uses the same insertion and unchanged Data tuple.
The original typed input is in the extended context. No erased-type window,
transformed-code bound, transformed fixedness or canonicality is assumed. -/
def PackedErasure (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d cutoff gamma extended c parameter extendedParameter input erased out typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Insert d cutoff gamma extended ⊓
      (graph2 InternalPairing.pairing parameter c gamma ⊓
        (graph2 InternalPairing.pairing extendedParameter c extended ⊓
          (graph3 erasePackedRaw erased d cutoff input ⊓
            (graph3 (selectedTyped data) (numeral 1) input typ extendedParameter ⊓
              foldGraph data out erased parameter))))).imp
      (graph3 (selectedTyped data) (numeral 1) out typ parameter)))

/- These contracts do not claim that the raw transformed input itself is
selectedTyped. They require only the unchanged canonical-fold graph and do
not assume a final canonical law, rank, coherence, I or C. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransport
