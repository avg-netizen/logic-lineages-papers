module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Deletion values are consumed, not incorporated into the list result. -/
def Nil : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload count row reversed old stack out : OTerm alpha),
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
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack z old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
/-- Deletion values are consumed, not incorporated into the list result. -/
def Cons : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload count row reversed old stack out suffix childTail first second value : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.raw raw input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.childCount (suc (suc z)) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionCount count input)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix second childTail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childTail first old)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons value raw first second)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnTargets
