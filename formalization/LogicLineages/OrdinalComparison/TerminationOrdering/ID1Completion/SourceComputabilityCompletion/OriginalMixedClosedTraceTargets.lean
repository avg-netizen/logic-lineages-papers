module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)
/-- Restricted mixed prefix/direct-bottom transport at a NEW standalone leaf. Same original H/G/M/W and outer c, arbitrary actual insertion. Rank witnesses concern ORIGINAL endpoints. No final-global tuple, arbitrary source-edge closure, external ChildIH, or native reflection. -/
def ActualClosedRestrictedTransport : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (source H G M W) (numeral 1) s oldParam ⊓
   (graph4 (leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓
   (graph4 (OriginalMixedDirectBottomTrace.recognizes (source H G M W) (leaf H G M W oldStep)) (numeral 1) s t cert oldParam ⊓
   (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
   (graph2 InternalPairing.pairing oldParam c extended ⊓
   (graph2 InternalPairing.pairing newParam c gamma ⊓
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
    graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))))).imp
   (graph2 (source H G M W) (numeral 1) erasedS newParam ⊓
    OriginalExistentialRankResultDefinitions.Result (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) erasedS erasedT newParam s t)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTargets
