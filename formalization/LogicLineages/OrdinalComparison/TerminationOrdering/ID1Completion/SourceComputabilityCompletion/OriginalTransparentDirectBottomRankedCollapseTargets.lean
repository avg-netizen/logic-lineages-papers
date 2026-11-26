module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDichotomyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Only the equality branch of the actual original direct-bottom certificate.
Erasure collapse forces original variable rank one against bottom rank zero.
Ranks concern ORIGINAL packed endpoints. No general source-edge closure. -/
def ActualRankedCollapse : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1)
 (W : Program 2) (P : Program 3) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))).imp
   ((equal erasedS erasedT).imp
     (OriginalLambdaOriginalRankDefinitions.PackedRankDrop s t (numeral 1) (numeral 0)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
