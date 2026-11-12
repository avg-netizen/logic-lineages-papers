module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- NEW standalone leaf and exact direct-bottom branch only; no old final tuple identity. -/
def ActualErasure : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))).imp
   (graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) erasedS newParam ⊓
    OriginalTransparentDirectBottomDichotomy.Result
     (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) erasedS erasedT newParam)))

def ActualRankedCollapse : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))).imp
   ((equal erasedS erasedT).imp
     (OriginalLambdaOriginalRankDefinitions.PackedRankDrop s t (numeral 1) (numeral 0)))))

def ActualRankedErasure : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))).imp
   (graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) erasedS newParam ⊓
    OriginalExistentialRankResultDefinitions.Result
     (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) erasedS erasedT newParam s t)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureTargets
