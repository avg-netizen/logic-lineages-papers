module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)
def ActualBothErasedSource : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (source H G M W) (numeral 1) s oldParam)) →
 Nonempty (Derivation body Delta (graph4 (OriginalMixedDirectBottomTrace.recognizes (source H G M W) (leaf H G M W oldStep))
  (numeral 1) s t cert oldParam)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam c extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)) →
 Nonempty (Derivation body Delta
  (graph2 (source H G M W) (numeral 1) erasedS newParam ⊓ graph2 (source H G M W) (numeral 1) erasedT newParam))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityTargets
