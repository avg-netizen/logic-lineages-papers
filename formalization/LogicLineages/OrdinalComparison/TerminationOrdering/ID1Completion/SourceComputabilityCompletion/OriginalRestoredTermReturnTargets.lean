module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Children0 : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter count row reversed old root returned tail value stack out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role z input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.childCount z input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionCount count input)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed old)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed z z)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
def Children1 : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix first : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role z input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.childCount (suc z) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionCount count input)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix first old)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed first z)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
def Children2 : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix childTail first second : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role z input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.childCount (suc (suc z)) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionCount count input)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix second childTail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childTail first old)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed first second)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnTargets
