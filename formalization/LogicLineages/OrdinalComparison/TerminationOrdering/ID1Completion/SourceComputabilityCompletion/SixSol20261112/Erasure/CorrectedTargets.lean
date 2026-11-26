module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.CorrectedTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Internal soundness at the ORIGINAL root of the actual mixed recognizer.
Neither source acceptance nor leaf acceptance is an extra premise. The same
four runtime inputs are retained, for arbitrary original Programs. -/
def RecognizerRootSoundness : Prop :=
 ∀ (source : Program 2) (leaf : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph4
  (OriginalMixedDirectBottomTrace.recognizes source leaf) (numeral 1) s t cert parameter)) →
 Nonempty (Derivation body Delta
  (graph2 source (numeral 1) s parameter ⊓
   graph4 leaf (numeral 1) s t cert parameter))

/-- Accepted recognition by the unchanged explicit closed checker supplies
the original root source/edge internally, then transports erasure. The actual
insertion, SAME outer parameter and exact raw erasures remain explicit.
This still describes recognized mixed-prefix/direct-bottom edges, not every
source rule or an identification with any selected final tuple. -/
def ClosedRecognizedErasure : Prop :=
 ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph4 (OriginalMixedDirectBottomTrace.recognizes
    (OriginalTransparentMixedDirectBottom.source H G M W)
    (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window))
    (numeral 1) s t cert oldParam ⊓
   (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
   (graph2 InternalPairing.pairing oldParam c extended ⊓
   (graph2 InternalPairing.pairing newParam c gamma ⊓
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
    graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))).imp
   (graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) erasedS newParam ⊓
    OriginalExistentialRankResultDefinitions.Result
     (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
     erasedS erasedT newParam s t)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.CorrectedTargets
