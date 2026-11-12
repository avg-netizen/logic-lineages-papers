module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalNumericListSortExchange

/-- Extend a literal zero-front accepted certificate by an arbitrary actual numeric prefix. -/
def ActualZeroPrefix : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (source target certificate payloadCode newFront newCertificate newSource newTarget : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate z payloadCode)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newCertificate newFront payloadCode)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append newSource newFront source)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append newTarget newFront target))),
 Nonempty (Derivation body Delta (graph3 edge (suc z) newSource newTarget newCertificate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixTargets
