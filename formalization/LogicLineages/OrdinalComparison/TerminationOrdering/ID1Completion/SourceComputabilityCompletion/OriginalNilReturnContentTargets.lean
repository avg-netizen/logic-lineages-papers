module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNilReturnContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal deletion values are consumed and discarded at a nil-list return.
The actual output head/work/suffix are recovered, not supplied as correct. -/
def NilContent : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload count row reversed old stack out outRest outOld value : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.raw raw input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.childCount z input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionCount count input)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed old)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out outRest stack)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value outOld)) →
 Nonempty (Derivation body Delta (eqn value z ⊓ (eqn outRest rest ⊓ eqn outOld old)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNilReturnContentTargets
