module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDichotomyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual original direct-bottom certificate edge only, at the SAME selected
leaf and concrete original source. Fresh-zero erasure gives equality OR an
exact newly constructed direct-bottom certificate accepted by that SAME leaf.
Outer type and erased-source validity are derived. No observer-equality,
strict-rank, other-certificate branch or canonical-fold conclusion. -/
def ActualFreshZero : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1)
 (W : Program 2) (P : Program 3) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (graph2 InternalListCodec.consCode extended d gamma ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d (numeral 0) s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d (numeral 0) t)))))))).imp
   (graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) erasedS newParam ⊓
    OriginalTransparentDirectBottomDichotomy.Result
     (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep erasedS erasedT newParam)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroTargets
