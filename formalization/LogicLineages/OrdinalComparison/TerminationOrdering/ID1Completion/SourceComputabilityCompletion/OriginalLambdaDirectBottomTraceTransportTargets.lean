module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDichotomyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Restricted original lambda-prefix/direct-bottom certificates only. The
separate recognizer records old-edge provenance, not the desired conclusion.
Equality decreases ORIGINAL occurrence rank from one to zero; otherwise an
actual transformed certificate is accepted by the SAME unchanged final leaf.
No other root-rule/certificate branch or general source-edge closure. -/
def ActualRestrictedTransport : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1)
 (W : Program 2) (P : Program 3) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (numeral 1) s t cert oldParam ⊓ (graph4 (OriginalLambdaDirectBottomTrace.recognizes (OriginalTransparentDirectBottomGlobal.source p H G W) (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep) (numeral 1) s t cert oldParam ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))).imp
   (graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) erasedS newParam ⊓
    OriginalLambdaOriginalRankDefinitions.Result
     (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep erasedS erasedT newParam s t (numeral 1) (numeral 0))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportTargets
