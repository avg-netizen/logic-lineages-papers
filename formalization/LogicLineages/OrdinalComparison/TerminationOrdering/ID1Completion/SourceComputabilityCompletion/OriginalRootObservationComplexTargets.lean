module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRootObservation
/-- Literal original ordinary/numbered wiring: actual head-class, converter,
and numeric-sort graph computations only, never their native calibration. -/
def OrdinaryLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input parameter typ raw payload head base headValue baseValues sortedBase headAndBase data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload head base)) →
 Nonempty (Derivation body Delta (graph1 OriginalHeadClassNumber.classNumber headValue head)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) baseValues base parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sortedBase baseValues)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headAndBase headValue sortedBase)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data typ headAndBase)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 4) data)) →
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter))

def NumberedLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields base afterBase extraTypes extras headValue baseValues sortedBase extraValues baseAndExtras headAndArgs typedData data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload label afterLabel)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterLabel head afterHead)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterHead encodedType numberedFields)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numberedFields base afterBase)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterBase extraTypes extras)) →
 Nonempty (Derivation body Delta (graph1 OriginalHeadClassNumber.classNumber headValue head)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) baseValues base parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sortedBase baseValues)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) extraValues extras parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing baseAndExtras sortedBase extraValues)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headAndArgs headValue baseAndExtras)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ headAndArgs)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data label typedData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 5) data)) →
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexTargets
