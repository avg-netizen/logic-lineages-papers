module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def TermChildren0 : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter count row reversed old root returned tail value stack out parent counts typed rawJob typ raw : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent z typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts z count)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
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
def TermChildren1 : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix first parent counts typed rawJob typ raw : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent z typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts (suc z) count)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
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
def TermChildren2 : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix childTail first second parent counts typed rawJob typ raw : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent z typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts (suc (suc z)) count)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
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
def ListNil : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload count row reversed old stack out parent counts typed rawJob typ packed parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent (numeral 1) typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts z count)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed old)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack z old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
def ListCons : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload count row reversed old stack out suffix childTail first second value parent counts typed rawJob typ packed parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent (numeral 1) typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts (suc (suc z)) count)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results reversed suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix second childTail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childTail first old)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons value raw first second)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnTargets
