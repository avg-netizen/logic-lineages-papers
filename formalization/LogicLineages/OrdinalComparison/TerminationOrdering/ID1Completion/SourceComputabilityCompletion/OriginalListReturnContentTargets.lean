module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Invert an ACTUAL list-cons return using a literal completed child/deletion
stack partition. The output value is not assumed to be a return result, and
neither the restored work nor restored old result suffix is assumed equal.
This is a local content boundary law, not a global evaluator semantic invariant. -/
def ConsContent : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload count row reversed old stack out outRest outOld suffix childTail first second value : OTerm alpha),
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
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out outRest stack)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value outOld)) →
 Nonempty (Derivation body Delta
  (graph3 OriginalHereditaryReturn.returnArgumentsCons value raw first second ⊓
   (eqn outRest rest ⊓ eqn outOld old)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentTargets
